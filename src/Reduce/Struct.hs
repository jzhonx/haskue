{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Struct where

import Control.Monad (foldM, unless)
import Cursor
import Data.Aeson (toJSON)
import qualified Data.ByteString.Char8 as BC
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import qualified Data.Text as T
import DepGraph (delDGEdgesByUseMatch, queryUsesByDepMatch)
import Feature
import {-# SOURCE #-} Reduce.Core (reduce, reduceVN, signalReduced)
import Reduce.Monad (
  RM,
  getRMDepGraph,
  mapDepGraph,
  modifyRMContext,
 )
import Reduce.Reference ()
import Reduce.Store (copyVTermNode, storeVal)
import Reduce.TraceSpan (
  debugInstStr,
  emptySpanValue,
  traceSpanAdaptTM,
  traceSpanArgsTM,
  traceSpanTM,
  traceSpanTermsRepTM,
 )
import Reduce.Unification (patMatchLabel)
import StringIndex (
  ShowWTIndexer (..),
  TextIndex,
  TextIndexerMonad,
  ToJSONWTIndexer (..),
  textIndexToBS,
  textToTextIndex,
 )
import Text.Printf (printf)
import Util.Format (msprintfS, packFmtA)
import Value
import Value.Export.Debug (
  cnstrsToFullTermsRep,
  termsRepToFullJSON,
  vnToStringTermsRep,
 )
import Value.Instances (posttravsVT)

reduceStruct :: Struct -> ValAddr -> RM Val
reduceStruct initStruct addr = traceSpanTM "reduceStruct" addr emptySpanValue $ do
  r <-
    do
      whenStruct
        ( \s -> do
            let nf = appendSeg addr
            stcBindings' <- Map.traverseWithKey (\k v -> reduce (nf $ mkLetFeature k) v) (stcBindings s)
            stcDynFields' <-
              mapM
                ( \df -> do
                    dsfLabel' <- reduce (nf (mkDynFieldFeature (dsfID df) 0)) (dsfLabel df)
                    return df{dsfLabel = dsfLabel'}
                )
                (stcDynFields s)
            stcCnstrs' <-
              mapM
                ( \cnstr -> do
                    do
                      scsPattern' <- reduce (nf (mkPatternFeature (scsID cnstr) 0)) (scsPattern cnstr)
                      return cnstr{scsPattern = scsPattern'}
                )
                (stcCnstrs s)
            stcFields' <-
              Map.traverseWithKey
                (\k v -> vtmapM (applyAddrFOnVN reduce) (nf $ mkStringFeature k) v)
                (stcFields s)
            stcEmbedVal' <- case stcEmbedVal s of
              Nothing -> return Nothing
              Just ev -> do
                Just <$> reduceVN (nf mkEmbedValueFeature) ev
            return
              ( VStruct $
                  s
                    { stcBindings = stcBindings'
                    , stcDynFields = stcDynFields'
                    , stcCnstrs = stcCnstrs'
                    , stcFields = stcFields'
                    , stcEmbedVal = stcEmbedVal'
                    }
              )
        )
        (VStruct initStruct)
      >>= whenStruct
        ( \s ->
            foldM
              (\acc i -> handleSObjChange (appendSeg addr (mkDynFieldFeature i 0)) acc)
              (VStruct s)
              (IntMap.keys $ stcDynFields s)
        )
      >>= whenStruct
        ( \s ->
            foldM
              (\acc i -> handleSObjChange (appendSeg addr (mkPatternFeature i 0)) acc)
              (VStruct s)
              (IntMap.keys $ stcCnstrs s)
        )
  whenStruct
    ( \s -> do
        validateStructPerm addr s
    )
    r

whenStruct :: (Struct -> RM Val) -> Val -> RM Val
whenStruct f v = do
  case v of
    VStruct struct -> f struct
    -- The struct might have been turned to another type due to embedding or reducing fields.
    _ -> return v

validateStructPerm :: ValAddr -> Struct -> RM Val
validateStructPerm addr struct = traceSpanTermsRepTM "validateStructPerm" addr (VStruct struct) $
  do
    r <-
      foldM
        ( \acc perm -> case acc of
            Just _ -> return acc
            Nothing -> validatePermItem struct perm addr
        )
        Nothing
        (stcPerms struct)
    case r of
      Just err -> do
        debugInstStr
          "validateStructPerm"
          addr
          ( do
              rep <- vnToStringTermsRep (VBottom err)
              msprintfS "permission error: %s" [packFmtA rep]
          )
        return (VStruct $ struct{stcPermErr = Just err})
      Nothing -> return (VStruct $ struct{stcPermErr = Nothing})

{- | Validate the permission item.

A struct must be provided so that dynamic fields and constraints can be found.

It constructs the allowing labels and constraints and checks if the joining labels are allowed.
-}
validatePermItem :: Struct -> PermItem -> ValAddr -> RM (Maybe Bottom)
validatePermItem struct pitem addr =
  -- traceSpanRMTC "validatePermItem" vc $
  do
    labelMs <- mapM convertLabel $ Set.toList $ piLabels pitem
    opLabelMs <- mapM convertLabel $ Set.toList $ piOpLabels pitem
    let
      cnstrs = IntMap.fromList $ map (\i -> (i, stcCnstrs struct IntMap.! i)) (Set.toList $ piCnstrs pitem)
    case (sequence labelMs, sequence opLabelMs) of
      (Just labels, Just opLabels) -> do
        foldM
          ( \acc opLabel -> case acc of
              Just _ -> return acc
              Nothing -> do
                allowed <- checkLabelAllowed (Set.fromList labels) cnstrs opLabel addr
                if allowed
                  then return acc
                  else do
                    s <- tshow opLabel
                    -- show s so that we have quotes around the label.
                    return $ Just (Bottom $ printf "%s is not allowed" (show s))
          )
          Nothing
          (Set.fromList opLabels)
      -- If not all dynamic fields can be resolved to string labels, we can not check the permission.
      -- This is what CUE does.
      _ -> return Nothing
 where
  convertLabel :: (TextIndexerMonad s m) => StructFieldLabel -> m (Maybe TextIndex)
  convertLabel (StructStaticFieldLabel f) = return $ Just f
  convertLabel (StructDynFieldOID i) = do
    let strM = do
          df <- IntMap.lookup i (stcDynFields struct)
          rtrString (value $ dsfLabel df)
    case strM of
      Just s -> Just <$> textToTextIndex s
      Nothing -> return Nothing

checkLabelAllowed ::
  Set.Set TextIndex ->
  IntMap.IntMap StructCnstr ->
  TextIndex ->
  ValAddr ->
  RM Bool
checkLabelAllowed baseLabels baseAllCnstrs newLabel addr =
  traceSpanArgsTM
    "checkLabelAllowed"
    addr
    emptySpanValue
    ( do
        newLabelT <- tshow newLabel
        return $
          printf
            "newLabel: %s, baseLabels: %s, baseAllCnstrs: %s"
            newLabelT
            (show $ Set.toList baseLabels)
            (show $ IntMap.toList baseAllCnstrs)
    )
    check
 where
  check
    | newLabel `Set.member` baseLabels = return True
    | otherwise =
        -- A "new" field is allowed if there is at least one pattern that matches the field.
        foldM
          ( \acc cnstr ->
              if acc
                then return acc
                else do
                  let pat = scsPattern cnstr
                  patMatchLabel pat newLabel addr
          )
          -- By default, "new" label is not allowed.
          False
          (IntMap.elems baseAllCnstrs)

handleSObjChange :: ValAddr -> Val -> RM Val
handleSObjChange subValAddr parentV@(VStruct struct) = case lastSeg subValAddr of
  Just seg@(FeatureType DynFieldLabelType) -> go seg
  Just seg@(FeatureType PatternLabelType) -> go seg
  _ -> return parentV
 where
  go seg = do
    let structAddr = fromJust $ initValAddr subValAddr
    traceSpanTermsRepTM (printf "handleSObjChange, seg: %s" (show seg)) structAddr parentV $ do
      (parentV', affectedPairs) <- handleSObjChangeInner seg struct structAddr parentV
      foldM
        ( \acc (afAddr, afv) -> do
            sub <- reduce afAddr afv
            let label = fromJust $ lastSeg afAddr
                newAcc = fromJust $ setSubVN label sub (mkValVN acc)
            return $ value newAcc
        )
        parentV'
        affectedPairs
handleSObjChange _ v = return v

{- | Handle the post process of the mutable object change in the struct.

Returns the affected labels and removed labels.
-}
handleSObjChangeInner :: Feature -> Struct -> ValAddr -> Val -> RM (Val, [(ValAddr, VNode)])
handleSObjChangeInner seg struct structAddr structV = case seg of
  -- If the sub value is an error, propagate the error to the struct.
  FeatureType DynFieldLabelType -> do
    let (i, _) = getDynFieldIndexesFromFeature seg
    (removed, removedAffected, removedLabels) <- removeAppliedObject i struct structAddr
    removeChangedSubFields (genAddrs structAddr (map fst removedAffected ++ removedLabels)) structAddr

    let dsf = stcDynFields struct IntMap.! i
        allCnstrs = IntMap.elems $ stcCnstrs removed
    rE <- dynFieldToStatic (stcFields removed) dsf structAddr
    debugInstStr
      "handleSObjChange"
      structAddr
      (msprintfS "rE: %s" [packFmtA $ show rE])
    case rE of
      Left err -> return (value err, [])
      Right Nothing -> return (VStruct removed, [])
      Right (Just (name, field)) -> do
        -- Constrain the dynamic field with all existing constraints.
        (addAffFields, addAffLabels) <- do
          (newField, matchedAny) <- constrainFieldWithCnstrs name field allCnstrs structAddr
          return
            ( [(name, newField)]
            , [name | matchedAny]
            )

        let
          newS = updateStructWithFields addAffFields removed
          newVals = map (\(x, y) -> (x, ssfValue y)) addAffFields
        debugInstStr
          "handleSObjChange"
          structAddr
          (msprintfS "-: %s, +: %s" [packFmtA (map fst removedAffected), packFmtA addAffLabels])

        return (VStruct newS, genAddrVals structAddr (removedAffected ++ newVals))
  FeatureType PatternLabelType -> do
    -- Constrain all fields with the new constraint if it exists.
    let
      (i, _) = getPatternIndexesFromFeature seg
      cnstr = stcCnstrs struct IntMap.! i
    -- New constraint might have the following effects:
    -- A. It matches fewer fields than the previous constraint with narrower constraints.
    -- -----
    -- abcde
    --   +++
    -- In the above example, we need to do
    -- 1. Remove the constraint for a,b
    -- 2. Do nothing for c,d,e
    --
    -- B. It could also match more fields when the constraint just got reduced to a concrete pattern.

    (removed, removedAffected, removedLabels) <- removeAppliedObject i struct structAddr
    removeChangedSubFields (genAddrs structAddr (map fst removedAffected ++ removedLabels)) structAddr

    (newStruct, addAffPairs) <- applyCnstrToFields cnstr removed structAddr
    let affectedPairs = removedAffected ++ addAffPairs

    unless (null affectedPairs) $
      debugInstStr
        "handleSObjChange"
        structAddr
        ( msprintfS
            "-: %s, +: %s, new struct: %s"
            [packFmtA removedLabels, packFmtA (map fst addAffPairs), packFmtA $ mkStructVN newStruct]
        )
    return (VStruct newStruct, genAddrVals structAddr affectedPairs)
  _ -> return (structV, [])
 where
  genAddrs baseAddr = map (\name -> appendSeg baseAddr (mkStringFeature name))
  genAddrVals baseAddr = map (\(name, v) -> (appendSeg baseAddr (mkStringFeature name), v))

{- | Make all sub fields of changed fields NoVal.

The "changed" means a field is removed or its value is changed. No need to do this for added fields as they have been
NoVal by default.

Suppose we have an old value {a: {b: 1, c: 2}} and the new value is {a: {b: 1}}. All references that reference the a.c
field should be updated to NoVal since the field is removed.
-}
removeChangedSubFields :: [ValAddr] -> ValAddr -> RM ()
removeChangedSubFields affected structAddr =
  mapM_
    ( \afFieldAddr -> do
        -- First we delete all edges that are from the affected field or its sub fields.
        modifyRMContext $ mapDepGraph $ delDGEdgesByUseMatch (isPrefix afFieldAddr)
        storeVal afFieldAddr (mkValVN VNoVal)
        g <- getRMDepGraph
        let pairs = queryUsesByDepMatch (isPrefix afFieldAddr) g

        debugInstStr
          "removeChangedSubFields"
          structAddr
          ( do
              watchersT <- mapM tshow pairs
              msprintfS
                "removed affected addr: %s, watchers: %s, graph: %s"
                [packFmtA afFieldAddr, packFmtA watchersT, packFmtA g]
          )
        -- Next we delete all values that are sub fields of the affected field and are referenced, and signal reduced
        -- for them.
        -- TODO: maybe change the dep of the uses to the affected field.
        mapM_
          ( \(afSubDep, use) ->
              -- If the use is a sub field of the removed field, then we do nothing since the afSubDep will also be
              -- removed. Otherwise, need to set it to NoVal and signal reduced.
              if isPrefix afFieldAddr use
                then return ()
                else do
                  debugInstStr
                    "removeChangedSubFields"
                    structAddr
                    (msprintfS "set sub affected addr to NoVal: %s" [packFmtA afSubDep])
                  storeVal afSubDep (mkValVN VNoVal)
                  signalReduced afSubDep
          )
          pairs
    )
    affected

{- | Convert a dynamic field to a static field.

It returns a pair which contains reduced string and the newly created/updated field.
-}
dynFieldToStatic ::
  Map.Map TextIndex Field -> DynamicField -> ValAddr -> RM (Either VNode (Maybe (TextIndex, Field)))
dynFieldToStatic fields df addr
  | Just name <- rtrString (value label) = do
      nidx <- textToTextIndex name
      let
        res = Map.lookup nidx fields
        newSF = dynToField df res

      debugInstStr
        "dynFieldToStatic"
        addr
        ( msprintfS
            "converted dynamic field to static field, name: %s, old field: %s, new field: %s"
            [packFmtA (BC.unpack name), packFmtA (show res), packFmtA (show newSF)]
        )
      return $ Right (Just (nidx, newSF))
  | Just _ <- rtrBottom (value label) = return $ Left label
  -- Incomplete field label, no change is made. If the mutable was a reference with string value, then it would
  -- have been reduced to a string.
  | Nothing <- rtrNonUnion (value label) = return $ Right Nothing
  | otherwise = return $ Left (mkBottomVal "label can only be a string")
 where
  label = dsfLabel df

dynToField :: DynamicField -> Maybe Field -> Field
dynToField df sfM = case sfM of
  -- Only when the field of the identifier exists, we merge the dynamic field with the existing field.
  -- If the identifier is a let binding, then no need to merge. The limit that there should only be one identifier
  -- in a scope can be ignored.
  Just sf ->
    sf
      { ssfValue = mapConstraints (insertDynCnstr (dsfID df) (dsfValue df)) (ssfValue sf)
      , ssfAttr = mergeAttrs (ssfAttr sf) (dsfAttr df)
      }
  -- No existing field, so we just turn the dynamic field into a field.
  _ ->
    Field
      { ssfValue = emptyVNode{constraints = emptyConstraintsSet{dynamic = IntMap.singleton (dsfID df) (dsfValue df)}}
      , ssfAttr = dsfAttr df
      }

{- | Apply pattern constraints ([pattern]: constraint) to the static field.

Returns the new field. If the field is not matched with the pattern, it returns the original field.
-}
constrainFieldWithCnstrs :: TextIndex -> Field -> [StructCnstr] -> ValAddr -> RM (Field, Bool)
constrainFieldWithCnstrs name field cnstrs structAddr =
  foldM
    ( \(accField, accMatched) cnstr -> do
        (newField, matched) <- bindFieldWithCnstr name accField cnstr structAddr
        return (newField, accMatched || matched)
    )
    (field, False)
    cnstrs

{- | Bind the pattern constraint ([pattern]: constraint) to the static field if the field name matches the pattern.

If the field name matches the pattern, it returns the new unify function node, which is constraint & field.
Otherwise, return the original field.

The field should not have been applied with the constraint before.

It can run in any kind of node.
-}
bindFieldWithCnstr :: TextIndex -> Field -> StructCnstr -> ValAddr -> RM (Field, Bool)
bindFieldWithCnstr name field cnstr structAddr = do
  let selPattern = scsPattern cnstr

  matched <- patMatchLabel selPattern name structAddr
  if not matched
    then return (field, False)
    else do
      cnstrVal <- forkCnstrVal name cnstr structAddr
      debugInstStr
        "bindFieldWithCnstr"
        structAddr
        (show <$> cnstrsToFullTermsRep cnstrVal)
      let
        fval = ssfValue field
        op = fval{constraints = insertDynCnstr (scsID cnstr) cnstrVal (constraints fval)}
        newField = field{ssfValue = op}
      return (newField, True)

forkCnstrVal :: TextIndex -> StructCnstr -> ValAddr -> RM ConstraintSeq
forkCnstrVal fieldName cnstr structAddr = do
  let
    cnstrValAddr = appendSeg structAddr (mkPatternFeature (scsID cnstr) 1)
    fieldAddr = appendSeg structAddr (mkStringFeature fieldName)
  traceSpanAdaptTM
    "forkCnstrVal"
    structAddr
    (toJSON <$> cnstrsToFullTermsRep (scsValue cnstr))
    termsRepToFullJSON
    $ case scsPatAlias cnstr of
      Nothing -> return $ vtmapT (\_ vt -> copyVTermNode cnstrValAddr fieldAddr vt) cnstrValAddr (scsValue cnstr)
      Just aliasIdx -> do
        fieldNameT <- textIndexToBS fieldName
        let realNameV = VAtom $ String fieldNameT
            aliasAddr = appendSeg cnstrValAddr (mkLetFeature aliasIdx)
        debugInstStr
          "forkCnstrVal"
          structAddr
          ( msprintfS
              "aliasSeg: %s, aliasAddr: %s, realNameV: %s"
              [ packFmtA (mkLetFeature aliasIdx)
              , packFmtA aliasAddr
              , packFmtA (mkValVN realNameV)
              ]
          )
        replaced <- replaceAlias aliasAddr fieldNameT cnstrValAddr (scsValue cnstr)
        return $ vtmapT (\_ vt -> copyVTermNode cnstrValAddr fieldAddr vt) cnstrValAddr replaced

replaceAlias :: ValAddr -> BC.ByteString -> ValAddr -> ConstraintSeq -> RM ConstraintSeq
replaceAlias aliasAddr fieldNameT topAddr sq =
  do
    let
      alias = VAtom $ String fieldNameT
      replace =
        posttravsVT
          ( \_ x ->
              case x of
                IsRef _ ref
                  | let resIdentAddr = ref.resolvedIdentAddr
                  , resIdentAddr == aliasAddr ->
                      if null ref.selectors
                        then VTVal alias
                        else
                          let newIndx =
                                ValueSelect
                                  { bvID = 0 -- It should not be referenced.
                                  , iSelectors = ref.selectors
                                  , base = mkValVN alias
                                  }
                           in VTOp (VSelect newIndx)
                _ -> x
          )
          topAddr
    let sq' = vtmapT (\_ vt -> replace vt) topAddr sq
    return sq'

{- | Update the struct with the constrained result.

If the constrained result introduce new fields that are not in the struct, then they are ignored.
-}
updateStructWithCnstredRes ::
  -- | The constrained result is a list of tuples that contains the name of the field, the field.
  [(TextIndex, Field)] ->
  Struct ->
  Struct
updateStructWithCnstredRes res struct =
  foldr
    ( \(name, newField) acc ->
        maybe
          acc
          (\_ -> updateStructField name newField acc)
          (lookupStructField name struct)
    )
    struct
    res

-- | Filter the names that are matched with the constraint's pattern.
filterMatchedNames :: StructCnstr -> [TextIndex] -> ValAddr -> RM [TextIndex]
filterMatchedNames cnstr labels addr =
  foldM
    ( \acc name -> do
        matched <- patMatchLabel (scsPattern cnstr) name addr
        return $ if matched then name : acc else acc
    )
    []
    labels

{- | Remove the applied object from the fields.

Returns the updated struct, affected labels that represent values that are changed, and removed labels.

This is done by re-applying existing objects except the one that is removed because unification is a lossy operation.

For removed fields, they are not removed from the struct but marked as NoVal.
-}
removeAppliedObject :: Int -> Struct -> ValAddr -> RM (Struct, [(TextIndex, VNode)], [TextIndex])
removeAppliedObject objID struct addr =
  traceSpanAdaptTM
    "removeAppliedObject"
    addr
    emptySpanValue
    ( \(s, fds, rmLabels) -> do
        sT <- T.pack <$> vnToStringTermsRep (VStruct s)
        fdsT <-
          mapM
            ( \(name, v) -> do
                nameT <- tshow name
                vT <- tshow v
                return (nameT, vT)
            )
            fds
        rmLabelsT <- mapM tshow rmLabels
        ttoJSON (sT, (fdsT, rmLabelsT))
    )
    $ do
      (updatedFields, removedLabels) <-
        foldM
          ( \(accUpdated, accRemoved) (name, field) -> do
              if memberDynCnstr objID (constraints $ ssfValue field)
                then do
                  let constraints' = removeDynCnstr objID (constraints $ ssfValue field)
                  if hasEmptyCnstrs constraints'
                    then return (accUpdated, name : accRemoved)
                    else do
                      let newField = field{ssfValue = field.ssfValue{constraints = constraints'}}
                      return ((name, newField) : accUpdated, accRemoved)
                else return (accUpdated, accRemoved)
          )
          ([], [])
          (Map.toList $ stcFields struct)
      let res =
            removeStructFieldsByNames removedLabels $
              updateStructWithFields updatedFields struct
      return (res, map (\(x, y) -> (x, ssfValue y)) updatedFields, removedLabels)

-- | Apply the additional constraint to the fields.
applyCnstrToFields :: StructCnstr -> Struct -> ValAddr -> RM (Struct, [(TextIndex, VNode)])
applyCnstrToFields cnstr struct addr = traceSpanAdaptTM
  "applyCnstrToFields"
  addr
  emptySpanValue
  ( \(s, fds) -> do
      sT <- tshow (mkStructVN s)
      fdsT <- mapM (mapM tshow) fds
      ttoJSON (sT, fdsT)
  )
  $ do
    (addAffFields, _) <-
      foldM
        ( \(accFields, accLabels) (name, field) -> do
            (nf, isMatched) <- bindFieldWithCnstr name field cnstr addr
            if isMatched
              then return ((name, nf) : accFields, name : accLabels)
              else return (accFields, accLabels)
        )
        ([], [])
        (Map.toList $ stcFields struct)
    let newStruct = updateStructWithFields addAffFields struct
    return (newStruct, map (\(x, y) -> (x, ssfValue y)) addAffFields)
