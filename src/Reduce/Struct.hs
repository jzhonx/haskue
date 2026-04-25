{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Struct where

import Control.Monad (foldM, unless)
import Cursor
import qualified Data.ByteString.Char8 as BC
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import DepGraph (delDGEdgesByUseMatch, queryUsesByDepMatch)
import Feature
import {-# SOURCE #-} Reduce.Core (reduce, signalReduced)
import Reduce.Monad (
  RM,
  getRMDepGraph,
  mapDepGraph,
  modifyRMContext,
 )
import Reduce.Reference ()
import Reduce.Store (copyVal, storeVal)
import Reduce.TraceSpan (
  debugInstStr,
  debugInstText,
  emptySpanValue,
  traceSpanAdaptTM,
  traceSpanArgsTM,
  traceSpanValTM,
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
import Util.Format (msprintf, packFmtA)
import Value
import Value.Export.Debug (valToFullRepString, valToRepString)
import Value.Instances (posttravsVal)

reduceStruct :: ValAddr -> Val -> RM Val
reduceStruct addr initVal =
  traceSpanValTM "reduceStruct" addr initVal $ do
    r <-
      do
        -- First assign the base fields to the fields.
        whenStruct
          ( \s structV -> do
              let nf = appendSeg addr
                  newS = s{stcFields = stcStaticFieldBases s}
              -- Store the stub fields first.
              mapM_ (\(k, v) -> storeVal (nf $ mkStringFeature k) (ssfValue v)) (Map.toList $ stcFields newS)
              return $ setVN (VNStruct newS) structV
          )
          initVal
        >>= whenStruct
          ( \s structV -> do
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
              stcFields' <- Map.traverseWithKey (\k v -> vtmapM reduce (nf $ mkStringFeature k) v) (stcFields s)
              stcEmbedVal' <- case stcEmbedVal s of
                Nothing -> return Nothing
                Just ev -> Just <$> reduce (nf mkEmbedValueFeature) ev
              return $
                setVN
                  ( VNStruct $
                      s
                        { stcBindings = stcBindings'
                        , stcDynFields = stcDynFields'
                        , stcCnstrs = stcCnstrs'
                        , stcFields = stcFields'
                        , stcEmbedVal = stcEmbedVal'
                        }
                  )
                  structV
          )
        >>= whenStruct
          ( \s v ->
              foldM
                (\acc i -> handleSObjChange (appendSeg addr (mkDynFieldFeature i 0)) acc)
                v
                (IntMap.keys $ stcDynFields s)
          )
        >>= whenStruct
          ( \s v ->
              foldM
                (\acc i -> handleSObjChange (appendSeg addr (mkPatternFeature i 0)) acc)
                v
                (IntMap.keys $ stcCnstrs s)
          )
    validateStructPerm addr r

whenStruct :: (Struct -> Val -> RM Val) -> Val -> RM Val
whenStruct f v = do
  case v of
    IsStruct struct -> f struct v
    -- The struct might have been turned to another type due to embedding or reducing fields.
    _ -> return v

validateStructPerm :: ValAddr -> Val -> RM Val
validateStructPerm addr structV =
  traceSpanValTM "validateStructPerm" addr structV $
    whenStruct
      ( \s v -> do
          r <-
            foldM
              ( \acc perm -> case acc of
                  Just _ -> return acc
                  Nothing -> validatePermItem s perm addr
              )
              Nothing
              (stcPerms s)
          case r of
            Just err -> do
              rep <- valToRepString err
              debugInstText "validateStructPerm" addr (msprintf "permission error: %s" [packFmtA rep])
              return $ setVN (VNStruct $ s{stcPermErr = Just err}) v
            Nothing -> return $ setVN (VNStruct $ s{stcPermErr = Nothing}) v
      )
      structV

{- | Validate the permission item.

A struct must be provided so that dynamic fields and constraints can be found.

It constructs the allowing labels and constraints and checks if the joining labels are allowed.
-}
validatePermItem :: Struct -> PermItem -> ValAddr -> RM (Maybe Val)
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
                    return $ Just (mkBottomVal $ printf "%s is not allowed" (show s))
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
          rtrString (dsfLabel df)
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
    ( const $ do
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
handleSObjChange subValAddr parentV@(IsStruct struct) = case lastSeg subValAddr of
  Just seg@(FeatureType DynFieldLabelType) -> go seg
  Just seg@(FeatureType PatternLabelType) -> go seg
  _ -> return parentV
 where
  go seg = do
    let structAddr = fromJust $ initValAddr subValAddr
    traceSpanValTM (printf "handleSObjChange, seg: %s" (show seg)) structAddr parentV $ do
      (parentV', affectedPairs) <- handleSObjChangeInner seg struct structAddr parentV
      res <-
        foldM
          ( \acc (afAddr, afv) -> do
              sub <- reduce afAddr afv
              let label = fromJust $ lastSeg afAddr
                  newAcc = fromJust $ setSubVal label sub acc
              return newAcc
          )
          parentV'
          affectedPairs
      storeVal structAddr res
      return res
handleSObjChange _ v = return v

{- | Handle the post process of the mutable object change in the struct.

Returns the affected labels and removed labels.
-}
handleSObjChangeInner :: Feature -> Struct -> ValAddr -> Val -> RM (Val, [(ValAddr, Val)])
handleSObjChangeInner seg struct structAddr structV = case seg of
  -- If the sub value is an error, propagate the error to the struct.
  FeatureType DynFieldLabelType -> do
    let (i, _) = getDynFieldIndexesFromFeature seg
    (removed, removedAffected, removedLabels) <- removeAppliedObject i struct structAddr
    removeChangedSubFields (genAddrs structAddr (map fst removedAffected ++ removedLabels)) structAddr

    let dsf = stcDynFields struct IntMap.! i
        allCnstrs = IntMap.elems $ stcCnstrs removed
    rE <- dynFieldToStatic (stcFields removed) dsf structAddr
    debugInstText
      "handleSObjChange"
      structAddr
      (msprintf "rE: %s" [packFmtA $ show rE])
    case rE of
      Left err -> return (setVN (valNode err) structV, [])
      Right Nothing -> return (setVN (VNStruct removed) structV, [])
      Right (Just (name, field)) -> do
        -- Constrain the dynamic field with all existing constraints.
        (addAffFields, addAffLabels) <- do
          newField <- constrainFieldWithCnstrs name field allCnstrs structAddr
          return
            ( [(name, newField)]
            , if not (null $ ssfObjects newField) then [name] else []
            )

        let
          newS = updateStructWithFields addAffFields removed
          newVals = map (\(x, y) -> (x, ssfValue y)) addAffFields
        debugInstText
          "handleSObjChange"
          structAddr
          (msprintf "-: %s, +: %s" [packFmtA (map fst removedAffected), packFmtA addAffLabels])

        return (setVN (VNStruct newS) structV, genAddrVals structAddr (removedAffected ++ newVals))
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
      debugInstText
        "handleSObjChange"
        structAddr
        ( msprintf
            "-: %s, +: %s, new struct: %s"
            [packFmtA removedLabels, packFmtA (map fst addAffPairs), packFmtA $ mkStructVal newStruct]
        )
    return (setVN (VNStruct newStruct) structV, genAddrVals structAddr affectedPairs)
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
        modifyRMContext $ mapDepGraph $ delDGEdgesByUseMatch (isPrefix afFieldAddr)
        storeVal afFieldAddr (mkNewVal VNNoVal)
        g <- getRMDepGraph
        let pairs = queryUsesByDepMatch (isPrefix afFieldAddr) g

        debugInstText
          "removeChangedSubFields"
          structAddr
          ( do
              watchersT <- mapM tshow pairs
              msprintf
                "removed affected addr: %s, watchers: %s, graph: %s"
                [packFmtA afFieldAddr, packFmtA watchersT, packFmtA g]
          )

        mapM_
          ( \(afSubDep, use) ->
              -- If the use is a sub field of the removed field, then can do nothing since the afSubDep will also be
              -- removed. Otherwise, need to set it to NoVal and signal reduced.
              if isPrefix afFieldAddr use
                then return ()
                else do
                  debugInstText
                    "removeChangedSubFields"
                    structAddr
                    ( msprintf
                        "set sub affected addr to NoVal: %s"
                        [packFmtA afSubDep]
                    )
                  storeVal afSubDep (mkNewVal VNNoVal)
                  signalReduced afSubDep
          )
          pairs
    )
    affected

{- | Convert a dynamic field to a static field.

It returns a pair which contains reduced string and the newly created/updated field.
-}
dynFieldToStatic ::
  Map.Map TextIndex Field -> DynamicField -> ValAddr -> RM (Either Val (Maybe (TextIndex, Field)))
dynFieldToStatic fields df addr
  | Just name <- rtrString label = do
      nidx <- textToTextIndex name
      let
        unifier l r = mkMutableVal $ mkUnifyOp [l, r]
        res = Map.lookup nidx fields
        newSF = dynToField df res unifier

      debugInstText
        "dynFieldToStatic"
        addr
        ( msprintf
            "converted dynamic field to static field, name: %s, old field: %s, new field: %s"
            [packFmtA (BC.unpack name), packFmtA (show res), packFmtA (show newSF)]
        )
      return $ Right (Just (nidx, newSF))
  | Just _ <- rtrBottom label = return $ Left label
  -- Incomplete field label, no change is made. If the mutable was a reference with string value, then it would
  -- have been reduced to a string.
  | Nothing <- rtrNonUnion label = return $ Right Nothing
  | otherwise = return $ Left (mkBottomVal "label can only be a string")
 where
  label = dsfLabel df

{- | Apply pattern constraints ([pattern]: constraint) to the static field.

Returns the new field. If the field is not matched with the pattern, it returns the original field.
-}
constrainFieldWithCnstrs :: TextIndex -> Field -> [StructCnstr] -> ValAddr -> RM Field
constrainFieldWithCnstrs name field cnstrs structAddr =
  foldM
    ( \accField cnstr -> do
        (newField, _) <- bindFieldWithCnstr name accField cnstr structAddr
        return newField
    )
    field
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
        (const $ valToFullRepString cnstrVal)
      let
        fval = ssfValue field
        op = mkMutableVal $ mkUnifyOp [fval, cnstrVal]
        newField = field{ssfValue = op, ssfObjects = Set.insert (scsID cnstr) (ssfObjects field)}
      return (newField, True)

forkCnstrVal :: TextIndex -> StructCnstr -> ValAddr -> RM Val
forkCnstrVal fieldName cnstr structAddr = do
  let
    cnstrValAddr = appendSeg structAddr (mkPatternFeature (scsID cnstr) 1)
    fieldAddr = appendSeg structAddr (mkStringFeature fieldName)

  case scsPatAlias cnstr of
    Nothing -> copyVal cnstrValAddr fieldAddr (scsValue cnstr)
    Just aliasIdx -> do
      fielaNameT <- textIndexToBS fieldName
      let realNameV = mkAtomVal $ String fielaNameT
          aliasAddr = appendSeg cnstrValAddr (mkLetFeature aliasIdx)
      debugInstText
        "forkCnstrVal"
        structAddr
        ( msprintf
            "aliasSeg: %s, aliasAddr: %s, realNameV: %s, cnstrVal: %s"
            [packFmtA (mkLetFeature aliasIdx), packFmtA aliasAddr, packFmtA realNameV, packFmtA (scsValue cnstr)]
        )
      replaced <- replaceAlias aliasAddr realNameV cnstrValAddr (scsValue cnstr)
      copyVal cnstrValAddr fieldAddr replaced

replaceAlias :: ValAddr -> Val -> ValAddr -> Val -> RM Val
replaceAlias aliasAddr alias topAddr topV =
  do
    let v' =
          posttravsVal
            ( \_ x ->
                case x of
                  IsRef sop ref
                    | let resIdentAddr = ref.resolvedIdentAddr
                    , resIdentAddr == aliasAddr ->
                        if null ref.selectors
                          then alias
                          else
                            let newIndx = ValueSelect{iSelectors = ref.selectors, base = alias}
                             in setTOp (setOpInSOp (VSelect newIndx) sop) x
                  _ -> x
            )
            topAddr
            topV
    return v'

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
removeAppliedObject :: Int -> Struct -> ValAddr -> RM (Struct, [(TextIndex, Val)], [TextIndex])
removeAppliedObject objID struct addr =
  traceSpanAdaptTM
    "removeAppliedObject"
    addr
    emptySpanValue
    ( \(s, fds, rmLabels) -> do
        sT <- tshow (mkStructVal s)
        fdsT <- mapM tshow fds
        rmLabelsT <- mapM tshow rmLabels
        ttoJSON (sT, (fdsT, rmLabelsT))
    )
    $ do
      (updatedFields, removedLabels) <-
        foldM
          ( \(accUpdated, accRemoved) (name, field) -> do
              let
                updatedObjectIDs = Set.delete objID (ssfObjects field)
                updatedCnstrs = IntMap.filterWithKey (\k _ -> k `Set.member` updatedObjectIDs) allCnstrs
                updatedDyns = IntMap.filterWithKey (\k _ -> k `Set.member` updatedObjectIDs) allDyns
                baseRawM = ssfValue <$> Map.lookup name (stcStaticFieldBases struct)
              debugInstStr
                "removeAppliedObject"
                addr
                ( const $ do
                    baseRawMT <- mapM tshow baseRawM
                    return $
                      printf
                        "field: %s, objID: %s, updatedObjectIDs: %s, raw: %s"
                        (show name)
                        (show objID)
                        (show $ Set.toList updatedObjectIDs)
                        (show baseRawMT)
                )

              case baseRawM of
                Just raw -> do
                  let
                    rawField = field{ssfValue = raw, ssfObjects = Set.empty}
                    fieldWithDyns =
                      foldr
                        (\dyn acc -> dynToField dyn (Just acc) unifier)
                        rawField
                        (IntMap.elems updatedDyns)
                  newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems updatedCnstrs) addr
                  return ((name, newField) : accUpdated, accRemoved)
                -- The field is created by a dynamic field, so it does not have a base raw.
                _ ->
                  if null updatedDyns
                    -- If there are no dynamic fields left, then the field should be removed.
                    then return (accUpdated, name : accRemoved)
                    else do
                      let
                        dyns = IntMap.elems updatedDyns
                        startField =
                          field
                            { ssfValue = dsfValue $ head dyns
                            , ssfObjects = Set.singleton (dsfID $ head dyns)
                            }
                        fieldWithDyns =
                          foldr
                            (\dyn acc -> dynToField dyn (Just acc) unifier)
                            startField
                            (tail dyns)
                      newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems updatedCnstrs) addr
                      return ((name, newField) : accUpdated, accRemoved)
          )
          ([], [])
          (fieldsUnifiedWithObject objID $ Map.toList $ stcFields struct)
      let res =
            removeStructFieldsByNames removedLabels $
              updateStructWithFields updatedFields struct
      return (res, map (\(x, y) -> (x, ssfValue y)) updatedFields, removedLabels)
 where
  allCnstrs = stcCnstrs struct
  allDyns = stcDynFields struct
  unifier l r = mkMutableVal $ mkUnifyOp [l, r]

  -- Find the fields that are unified with the object
  fieldsUnifiedWithObject :: Int -> [(TextIndex, Field)] -> [(TextIndex, Field)]
  fieldsUnifiedWithObject j =
    foldr (\(k, field) acc -> if j `elem` ssfObjects field then (k, field) : acc else acc) []

-- | Apply the additional constraint to the fields.
applyCnstrToFields :: StructCnstr -> Struct -> ValAddr -> RM (Struct, [(TextIndex, Val)])
applyCnstrToFields cnstr struct addr = traceSpanAdaptTM
  "applyCnstrToFields"
  addr
  emptySpanValue
  ( \(s, fds) -> do
      sT <- tshow (mkStructVal s)
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
