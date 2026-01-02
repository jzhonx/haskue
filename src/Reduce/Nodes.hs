{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Nodes where

import Control.Monad (foldM, forM_, unless, when)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (modify')
import Cursor
import Data.Aeson (KeyValue (..), ToJSON (..), object)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Vector as V
import Feature
import Reduce.RMonad (
  RM,
  addRMDanglingLet,
  allocRMObjID,
  createCnstr,
  debugInstantOpRM,
  debugInstantRM,
  debugInstantTM,
  delTMDepPrefix,
  descendTMSegMust,
  emptySpanValue,
  getRMDanglingLets,
  getTMAbsAddr,
  getTMCursor,
  getTMVal,
  inRemoteTM,
  inSubTM,
  inTempTM,
  liftEitherRM,
  mapCtx,
  modifyTMVN,
  modifyTMVal,
  noRecalc,
  params,
  propUpTM,
  putTMCursor,
  supersedeTMVN,
  throwFatal,
  traceSpanAdaptRM,
  traceSpanArgsAdaptRM,
  traceSpanArgsRMTC,
  traceSpanRMTC,
  traceSpanTM,
  unwrapTMVN,
 )
import Reduce.RefSys (IdentType (..), searchTCIdent)
import {-# SOURCE #-} Reduce.Root (reduce, reducePureVN, reduceToNonMut)
import Reduce.UnifyOp (mergeTCs, patMatchLabel, prepConj, unifyTCs)
import StringIndex (ShowWTIndexer (..), TextIndex, TextIndexerMonad, ToJSONWTIndexer (..), textToTextIndex)
import Text.Printf (printf)
import Value
import Value.Util.ValRep (treeToRepString)

reduceStruct :: RM ()
reduceStruct = traceSpanTM "reduceStruct" $ do
  -- First assign the base fields to the fields.
  whenStruct
    (\s -> modifyTMVN (VNStruct $ s{stcFields = stcStaticFieldBases s}))

  whenStruct
    ( \s ->
        mapM_
          (\i -> inSubTM (mkDynFieldFeature i 0) reduce)
          (IntMap.keys $ stcDynFields s)
    )
  whenStruct
    ( \s ->
        mapM_
          (\i -> inSubTM (mkPatternFeature i 0) reduce)
          (IntMap.keys $ stcCnstrs s)
    )
  -- Reduce lets.
  whenStruct
    ( \s -> do
        vc <- getTMCursor
        mapM_
          ( \k -> whenStruct $ \_ -> do
              f <- mkLetFeature k Nothing
              errM <- checkRedecl True k vc
              case errM of
                Just err -> modifyTMVN (valNode err)
                Nothing -> inSubTM f $ do
                  reduce
                  addr <- getTMAbsAddr
                  let isIterVar = (s.stcBindings Map.! k).isIterVar
                  unless isIterVar $ addRMDanglingLet addr
          )
          (Map.keys s.stcBindings)
    )
  -- Reduce all fields.
  whenStruct (\s -> mapM_ reduceStructField (Map.keys . stcFields $ s))

  -- Validate if all let bindings are referred.
  -- Return the last error if multiple unreferenced let bindings exist.
  whenStruct $ \s -> do
    baseAddr <- getTMAbsAddr
    mapM_
      ( \k -> do
          lf <- mkLetFeature k Nothing
          let addr = appendSeg baseAddr lf
          danglings <- getRMDanglingLets
          when (addr `elem` danglings) $ do
            -- Print the pure identifier.
            kStr <- tshow k
            modifyTMVN $ VNBottom $ Bottom $ printf "unreferenced let clause let %s" (show kStr)
      )
      (Map.keys $ stcBindings s)

  -- Set the struct as concrete if all fields are concrete.
  whenStruct
    ( \s -> do
        -- According to the spec,
        -- A value is concrete if it is either an atom, or a struct whose field values are all concrete, recursively.
        let isStructConcrete =
              foldl
                (\acc field -> acc && isJust (rtrConcrete $ ssfValue field))
                True
                (Map.elems . stcFields $ s)
            newStruct = s{stcIsConcrete = isStructConcrete}
        modifyTMVN (VNStruct newStruct)
    )

  validateStructPerm

whenStruct :: (Struct -> RM ()) -> RM ()
whenStruct f = do
  t <- getTMVal
  case t of
    IsStruct struct -> f struct
    -- The struct might have been turned to another type due to embedding or reducing fields.
    _ -> return ()

validateStructPerm :: RM ()
validateStructPerm = traceSpanTM "validateStructPerm" $ whenStruct $ \s -> do
  vc <- getTMCursor
  r <-
    foldM
      ( \acc perm -> case acc of
          Just _ -> return acc
          Nothing -> validatePermItem s perm vc
      )
      Nothing
      (stcPerms s)
  case r of
    Just err -> do
      rep <- treeToRepString err
      debugInstantTM "validateStructPerm" (printf "permission error: %s" rep)
      modifyTMVN (VNStruct $ s{stcPermErr = Just err})
    Nothing -> modifyTMVN (VNStruct $ s{stcPermErr = Nothing})

{- | Validate the permission item.

A struct must be provided so that dynamic fields and constraints can be found.

It constructs the allowing labels and constraints and checks if the joining labels are allowed.
-}
validatePermItem :: Struct -> PermItem -> VCur -> RM (Maybe Val)
validatePermItem struct p vc = traceSpanRMTC "validatePermItem" vc $ do
  labelMs <- mapM convertLabel $ Set.toList $ piLabels p
  opLabelMs <- mapM convertLabel $ Set.toList $ piOpLabels p
  let
    cnstrs = IntMap.fromList $ map (\i -> (i, stcCnstrs struct IntMap.! i)) (Set.toList $ piCnstrs p)
  case (sequence labelMs, sequence opLabelMs) of
    (Just labels, Just opLabels) -> do
      foldM
        ( \acc opLabel -> case acc of
            Just _ -> return acc
            Nothing -> do
              allowed <- checkLabelAllowed (Set.fromList labels) cnstrs opLabel vc
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
  VCur ->
  RM Bool
checkLabelAllowed baseLabels baseAllCnstrs newLabel vc =
  traceSpanArgsRMTC
    "checkLabelAllowed"
    ( printf
        "newLabel: %s, baseLabels: %s, baseAllCnstrs: %s"
        (show newLabel)
        (show $ Set.toList baseLabels)
        (show $ IntMap.toList baseAllCnstrs)
    )
    vc
    $ _checkLabelAllowed baseLabels baseAllCnstrs newLabel vc

_checkLabelAllowed ::
  Set.Set TextIndex ->
  IntMap.IntMap StructCnstr ->
  TextIndex ->
  VCur ->
  RM Bool
_checkLabelAllowed baseLabels baseAllCnstrs newLabel vc
  | newLabel `Set.member` baseLabels = return True
  | otherwise =
      -- A "new" field is allowed if there is at least one pattern that matches the field.
      foldM
        ( \acc cnstr ->
            if acc
              then return acc
              else do
                let pat = scsPattern cnstr
                patMatchLabel pat newLabel vc
        )
        -- By default, "new" label is not allowed.
        False
        (IntMap.elems baseAllCnstrs)

checkRedecl :: Bool -> TextIndex -> VCur -> RM (Maybe Val)
checkRedecl nameIsLetVar ident vc = do
  -- Fields and let bindings are made exclusive in the same block in the evalExpr step, so we only need to make sure
  -- in the parent block that there is no field with the same name.
  parResM <-
    if isVCRoot vc
      then return Nothing
      else do
        ptc <- liftEitherRM (propUpVC vc)
        m <- searchTCIdent True ident ptc
        return $ maybe Nothing (\(x, y) -> Just (vcAddr x, y)) m
  case parResM of
    -- If the let binding with the same name is found in the scope. No matter what the name in the current block is a
    -- field or a let binding, it is a redeclaration error.
    Just (_, ITLetBinding)
      | nameIsLetVar -> Just <$> lbRedeclErr ident
      | otherwise -> Just <$> aliasErr ident
    -- If the field with the same name is found in the scope, and the name in the current block is a let, it is a
    -- redeclaration error.
    Just (_, ITField)
      | nameIsLetVar -> Just <$> aliasErr ident
    _ -> return Nothing

aliasErr :: TextIndex -> RM Val
aliasErr name = do
  nameStr <- tshow name
  return $ mkBottomVal $ printf "can not have both alias and field with name %s in the same scope" (show nameStr)

lbRedeclErr :: TextIndex -> RM Val
lbRedeclErr name = do
  nameStr <- tshow name
  return $ mkBottomVal $ printf "%s redeclared in same scope" (show nameStr)

{- | Reduce the struct field with the given name.

If the field is reduced to bottom, the whole struct becomes bottom.
-}
reduceStructField :: TextIndex -> RM ()
reduceStructField i = whenStruct $ \_ -> do
  vc <- getTMCursor
  errM <- checkRedecl False i vc
  case errM of
    Just err -> modifyTMVN (valNode err)
    Nothing -> do
      addr <- getTMAbsAddr
      r <- inSubTM (mkStringFeature i) (reduce >> getTMVal)
      case r of
        IsBottom _ | IsValImmutable <- r -> do
          modifyTMVN (valNode r)
          delTMDepPrefix addr
        _
          | isSCyclic r -> do
              modifyTMVN (valNode $ mkBottomVal "structural cycle")
              delTMDepPrefix addr
          | otherwise -> return ()

-- | Handle the post process of the mutable object change in the struct.
handleSObjChange :: RM [ValAddr]
handleSObjChange = do
  vc <- getTMCursor
  seg <- liftEitherRM $ vcFocusSegMust vc
  stc <- liftEitherRM $ propUpVC vc
  let r = focus vc
  case focus stc of
    -- If the sub value is an error, propagate the error to the struct.
    IsStruct struct
      | FeatureType StringLabelType <- seg -> traceSpanTM (printf "handleSObjChange, seg: %s" (show seg)) do
          let errM = case r of
                IsBottom _ | IsValImmutable <- r -> Just r
                _
                  | isSCyclic r -> Just $ mkBottomVal "structural cycle"
                  | otherwise -> Nothing
          case errM of
            Just err -> do
              modifyTMVN (valNode err)
              delTMDepPrefix $ vcAddr stc
            Nothing -> return ()
          return []
      | FeatureType DynFieldLabelType <- seg -> traceSpanTM (printf "handleSObjChange, seg: %s" (show seg)) do
          let (i, _) = getDynFieldIndexesFromFeature seg
          (oldLRmd, remAffLabels) <- removeAppliedObject i struct stc
          let dsf = stcDynFields struct IntMap.! i
              allCnstrs = IntMap.elems $ stcCnstrs oldLRmd
          rE <- dynFieldToStatic (stcFields oldLRmd) dsf
          debugInstantTM "handleSObjChange" (printf "dsf: %s, rE: %s, dsf: %s" (show dsf) (show rE) (show dsf))
          case rE of
            Left err -> modifyTMVN (valNode err) >> return []
            -- If the dynamic field label is incomplete, no change is made. But we still need to return the removed
            -- affected labels.
            Right Nothing -> return $ genAddrs (vcAddr stc) remAffLabels
            Right (Just (name, field)) -> do
              -- Constrain the dynamic field with all existing constraints.
              (addAffFields, addAffLabels) <- do
                newField <- constrainFieldWithCnstrs name field allCnstrs stc
                return
                  ( [(name, newField)]
                  , if not (null $ ssfObjects newField) then [name] else []
                  )

              let
                affectedLabels =
                  remAffLabels
                    ++ foldr (\n acc -> if n `elem` remAffLabels then acc else n : acc) [] addAffLabels
                newS = updateStructWithFields addAffFields oldLRmd
              debugInstantTM
                "handleSObjChange"
                (printf "-: %s, +: %s, all: %s" (show remAffLabels) (show addAffLabels) (show affectedLabels))

              propUpTM >> modifyTMVN (VNStruct newS) >> descendTMSegMust seg
              return $ genAddrs (vcAddr stc) affectedLabels
      | FeatureType PatternLabelType <- seg -> traceSpanTM (printf "handleSObjChange, seg: %s" (show seg)) do
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

          (oldPVRmd, remAffLabels) <- removeAppliedObject i struct stc
          (newStruct, addAffLabels) <- applyCnstrToFields cnstr oldPVRmd stc
          let affectedLabels = remAffLabels ++ addAffLabels

          propUpTM >> modifyTMVN (VNStruct newStruct) >> descendTMSegMust seg
          unless (null affectedLabels) $
            debugInstantTM
              "handleSObjChange"
              ( printf
                  "-: %s, +: %s, new struct: %s"
                  (show remAffLabels)
                  (show addAffLabels)
                  (show $ mkStructVal newStruct)
              )
          return $ genAddrs (vcAddr stc) affectedLabels
    _ -> return []
 where
  genAddrs baseAddr = map (\name -> appendSeg baseAddr (mkStringFeature name))

{- | Convert a dynamic field to a static field.

It returns a pair which contains reduced string and the newly created/updated field.
-}
dynFieldToStatic ::
  Map.Map TextIndex Field -> DynamicField -> RM (Either Val (Maybe (TextIndex, Field)))
dynFieldToStatic fields df
  | Just name <- rtrString label = do
      nidx <- textToTextIndex name
      let
        unifier l r = mkMutableVal $ mkUnifyOp [l, r]
        res = Map.lookup nidx fields
        newSF = dynToField df res unifier

      debugInstantTM
        "dynFieldToStatic"
        ( printf
            "converted dynamic field to static field, name: %s, old field: %s, new field: %s"
            name
            (show res)
            (show newSF)
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
constrainFieldWithCnstrs :: TextIndex -> Field -> [StructCnstr] -> VCur -> RM Field
constrainFieldWithCnstrs name field cnstrs vc =
  foldM
    ( \accField cnstr -> do
        (newField, _) <- bindFieldWithCnstr name accField cnstr vc
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
bindFieldWithCnstr :: TextIndex -> Field -> StructCnstr -> VCur -> RM (Field, Bool)
bindFieldWithCnstr name field cnstr vc = do
  let selPattern = scsPattern cnstr

  matched <- patMatchLabel selPattern name vc

  let
    fval = ssfValue field
    op = mkMutableVal $ mkUnifyOp [fval, scsValue cnstr]
    newField =
      if matched
        then field{ssfValue = op, ssfObjects = Set.insert (scsID cnstr) (ssfObjects field)}
        else field

  return (newField, matched)

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
filterMatchedNames :: StructCnstr -> [TextIndex] -> VCur -> RM [TextIndex]
filterMatchedNames cnstr labels vc =
  foldM
    ( \acc name -> do
        matched <- patMatchLabel (scsPattern cnstr) name vc
        return $ if matched then name : acc else acc
    )
    []
    labels

{- | Remove the applied object from the fields.

Returns the updated struct and the list of labels whose fields are affected.

This is done by re-applying existing objects except the one that is removed because unification is a lossy operation.
-}
removeAppliedObject :: Int -> Struct -> VCur -> RM (Struct, [TextIndex])
removeAppliedObject objID struct vc =
  traceSpanAdaptRM "removeAppliedObject" emptySpanValue vc $ do
    (remAffFields, removedLabels) <-
      foldM
        ( \(accUpdated, accRemoved) (name, field) -> do
            let
              newObjectIDs = Set.delete objID (ssfObjects field)
              newCnstrs = IntMap.filterWithKey (\k _ -> k `Set.member` newObjectIDs) allCnstrs
              newDyns = IntMap.filterWithKey (\k _ -> k `Set.member` newObjectIDs) allDyns
              baseRawM = ssfValue <$> Map.lookup name (stcStaticFieldBases struct)
            debugInstantRM
              "removeAppliedObject"
              ( printf
                  "field: %s, objID: %s, newObjectIDs: %s, raw: %s"
                  (show name)
                  (show objID)
                  (show $ Set.toList newObjectIDs)
                  (show baseRawM)
              )
              vc

            case baseRawM of
              Just raw -> do
                let
                  rawField = field{ssfValue = raw, ssfObjects = Set.empty}
                  fieldWithDyns =
                    foldr
                      (\dyn acc -> dynToField dyn (Just acc) unifier)
                      rawField
                      (IntMap.elems newDyns)
                newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems newCnstrs) vc
                return ((name, newField) : accUpdated, accRemoved)
              -- The field is created by a dynamic field, so it does not have a base raw.
              _ ->
                if null newDyns
                  -- If there are no dynamic fields left, then the field should be removed.
                  then return (accUpdated, name : accRemoved)
                  else do
                    let
                      dyns = IntMap.elems newDyns
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
                    newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems newCnstrs) vc
                    return ((name, newField) : accUpdated, accRemoved)
        )
        ([], [])
        (fieldsUnifiedWithObject objID $ Map.toList $ stcFields struct)
    let res = removeStructFieldsByNames removedLabels $ updateStructWithFields remAffFields struct
    return (res, map fst remAffFields)
 where
  allCnstrs = stcCnstrs struct
  allDyns = stcDynFields struct
  unifier l r = mkMutableVal $ mkUnifyOp [l, r]

  -- Find the fields that are unified with the object
  fieldsUnifiedWithObject :: Int -> [(TextIndex, Field)] -> [(TextIndex, Field)]
  fieldsUnifiedWithObject j =
    foldr (\(k, field) acc -> if j `elem` ssfObjects field then (k, field) : acc else acc) []

-- | Apply the additional constraint to the fields.
applyCnstrToFields :: StructCnstr -> Struct -> VCur -> RM (Struct, [TextIndex])
applyCnstrToFields cnstr struct vc = traceSpanAdaptRM "applyCnstrToFields" (\x -> ttoJSON $ snd x) vc $ do
  (addAffFields, addAffLabels) <-
    foldM
      ( \(accFields, accLabels) (name, field) -> do
          (nf, isMatched) <- bindFieldWithCnstr name field cnstr vc
          if isMatched
            then return ((name, nf) : accFields, name : accLabels)
            else return (accFields, accLabels)
      )
      ([], [])
      (Map.toList $ stcFields struct)
  let newStruct = updateStructWithFields addAffFields struct
  return (newStruct, addAffLabels)

reduceDisj :: Disj -> RM ()
reduceDisj d = do
  -- We have to reduce all disjuncts because they might be generated by merging one disjunction with another value.
  mapM_
    (\(i, _) -> inSubTM (mkDisjFeature i) reduce)
    (zip [0 ..] (dsjDisjuncts d))

  vc <- getTMCursor
  case valNode (focus vc) of
    VNDisj nd -> do
      newDisjT <- normalizeDisj (isJust . rtrBottom) nd vc
      modifyTMVN (valNode newDisjT)
    _ -> return ()

reduceList :: List -> RM ()
reduceList l = do
  r <-
    foldM
      ( \acc (i, origElem) -> do
          r <- inSubTM (mkListStoreIdxFeature i) (reduce >> getTMVal)
          case origElem of
            -- If the element is a comprehension and the result of the comprehension is a list, per the spec, we insert
            -- the elements of the list into the list at the current index.
            IsValMutable (Op (Compreh cph))
              | cph.isListCompreh
              , Just rList <- rtrList r ->
                  return $ acc ++ toList rList.final
            _ -> return $ acc ++ [r]
      )
      []
      (zip [0 ..] (toList l.store))
  t <- getTMVal
  case t of
    IsList lst -> do
      let newList = lst{final = V.fromList r}
      modifyTMVN (VNList newList)
    _ -> return ()

-- | Closes a struct when the tree has struct.
resolveCloseFunc :: [Val] -> VCur -> RM (Maybe Val)
resolveCloseFunc args _
  | length args /= 1 = throwFatal $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      let arg = head args
      return $ Just $ closeTree arg

-- | Close a struct when the tree has struct.
closeTree :: Val -> Val
closeTree a =
  case valNode a of
    VNStruct s -> setVN (VNStruct $ s{stcClosed = True}) a
    VNDisj dj ->
      let
        ds = map closeTree (dsjDisjuncts dj)
       in
        setVN (VNDisj (dj{dsjDisjuncts = ds})) a
    -- TODO: SOp should be closed.
    -- TNMutable _ -> throwFatal "TODO"
    _ -> mkBottomVal $ printf "cannot use %s as struct in argument 1 to close" (show a)

{- | Discover conjuncts from a **unreduced** tree node that contains conjuncts as its children.

It reduces every conjunct node it finds.

It should not be directly called.
-}
partialReduceUnifyOp :: RM ResolvedPConjuncts
partialReduceUnifyOp = traceSpanTM "partialReduceUnifyOp" $ do
  t <- getTMVal
  case t of
    IsStrictUnifyOp sop -> go sop False
    IsEmbedUnifyOp sop -> go sop True
    _ -> throwFatal "partialReduceUnifyOp: focus is not a unify operation"
 where
  go sop hasEmbeds = do
    xs <-
      foldM
        ( \acc (f, _) -> do
            subs <- inSubTM f discoverConjs
            return (acc ++ subs)
        )
        []
        (toList $ getSOpArgs sop)
    -- In the beginning, set the accumulating tree node to no value.
    -- TODO: remove deps
    modifyTMVN VNNoVal
    -- Get the original constraint node.
    cnstr <- getTMVal

    -- Preprocess conjuncts to validate if identifiers can be resolved.
    -- This prevents later preprocessing from incorrectly seeing resolved identifiers in other conjuncts.
    mapM_
      ( \(i, addr) -> inRemoteTM addr $ do
          vc <- getTMCursor
          case focus vc of
            -- No need to reduce comprehensions conjuncts.
            IsCompreh _ _ -> return ()
            _ -> do
              -- If the conjunct is a struct, it might have conflicting let bindings which need to be rewritten.
              -- The let bindings in the first encapsulating struct should not be rewritten.
              let toRewriteLets = not hasEmbeds || i > 0
              getTMCursor >>= prepConj toRewriteLets >>= putTMCursor
      )
      (zip [(0 :: Int) ..] xs)

    (aconjM, foundNoVal) <-
      foldM
        ( \(aconjM, foundNoVal) (i, addr) -> do
            rM <- inRemoteTM addr $ do
              vc <- getTMCursor
              case focus vc of
                -- No need to reduce comprehensions conjuncts.
                IsCompreh _ _ -> return $ Just vc
                _ -> do
                  reduceToNonMut
                  -- If the conjunct is reduced to a struct, it might have conflicting let bindings which need to be
                  -- rewritten.
                  -- The let bindings in the first encapsulating struct should not be rewritten.
                  let toRewriteLets = not hasEmbeds || i > 0
                  cur <- getTMCursor
                  -- Modify the current tree to be immutable so that prepConj will not invalidate ref's values.
                  res <- prepConj toRewriteLets (modifyVCFocus setValImmutable cur)
                  let conjT = focus res
                  -- Update the argument tree.
                  modifyTMVN (valNode conjT)
                  case rtrVal conjT of
                    Nothing -> return Nothing
                    Just v -> return $ Just (v `setVCFocus` vc)
            case rM of
              Nothing -> return (aconjM, True)
              Just r -> do
                let aM = case focus r of
                      IsAtom a -> Just a
                      _ -> Nothing
                acc <- getTMCursor
                case focus acc of
                  -- The accumulating tree is NoVal, so we just set the tree node to the reduced conjunct.
                  IsNoVal -> do
                    debugInstantRM
                      "partialReduceUnifyOp"
                      ( printf
                          "setting accumulating conjunct to reduced conjunct %s"
                          (show $ valNode $ focus r)
                      )
                      acc
                    modifyTMVN (valNode $ focus r)
                  -- The accumulating tree is not NoVal, so we need to unify it with the reduced conjunct.
                  _ -> do
                    res <- unifyTCs [acc, r] acc
                    modifyTMVN (valNode res)
                return (aM, foundNoVal)
        )
        (Nothing, False)
        (zip [(0 :: Int) ..] xs)

    createCnstr <- asks (createCnstr . params)
    case (aconjM, foundNoVal) of
      -- If there is at least one atom conjunct and there are incomplete conjuncts, we create an atom constraint
      -- conjunction.
      (Just a, True) | createCnstr -> return $ AtomCnstrConj $ AtomCnstr a cnstr
      (_, True) -> do
        modifyTMVN VNNoVal
        return IncompleteConjuncts
      _ -> CompletelyResolved <$> getTMVal

  -- Discover conjuncts and preprocess them.
  discoverConjs = do
    conjTC <- getTMCursor
    case focus conjTC of
      IsStrictUnifyOp sop ->
        -- A conjunct can be incomplete. For example, 1 & (x + 1) resulting an atom constraint.
        foldM
          ( \acc (f, _) -> do
              subs <- inSubTM f discoverConjs
              return (acc ++ subs)
          )
          []
          (toList $ getSOpArgs sop)
      -- We do not discover conjuncts that are part of an embed unify op because they should be treated as a whole.
      _ -> do
        addr <- getTMAbsAddr
        return [addr]

data ResolvedPConjuncts
  = -- | AtomCnstrConj is created if one of the pending conjuncts is an atom and the runtime parameter
    -- 'createCnstr' is True.
    AtomCnstrConj AtomCnstr
  | CompletelyResolved Val
  | IncompleteConjuncts
  deriving (Show)

instance ToJSON ResolvedPConjuncts where
  toJSON (AtomCnstrConj _) = toJSON ("AtomCnstrConj" :: String)
  toJSON (CompletelyResolved _) = toJSON ("CompletelyResolved" :: String)
  toJSON IncompleteConjuncts = toJSON ("IncompleteConjuncts" :: String)

instance ToJSONWTIndexer ResolvedPConjuncts where
  ttoJSON = return . toJSON

resolveDisjOp :: VCur -> RM (Maybe Val)
resolveDisjOp disjOpTC@(VCFocus (IsValMutable (Op (DisjOp disjOp)))) = traceSpanRMTC "resolveDisjOp" disjOpTC $ do
  let terms = toList $ djoTerms disjOp
  when (length terms < 2) $
    throwFatal $
      printf "disjunction operation requires at least 2 terms, got %d" (length terms)

  debugInstantRM "resolveDisjOp" (printf "terms: %s" (show terms)) disjOpTC
  disjuncts <- procMarkedTerms terms

  debugInstantRM "resolveDisjOp" (printf "disjuncts: %s" (show disjuncts)) disjOpTC
  if null disjuncts
    -- If none of the disjuncts are ready, return Nothing.
    then return Nothing
    else do
      let d = emptyDisj{dsjDisjuncts = disjuncts}
      r <- normalizeDisj (isJust . rtrBottom) d disjOpTC
      return $ Just r
resolveDisjOp _ = throwFatal "resolveDisjOp: focus is not a disjunction operation"

{- | Normalize a disjunction which is generated by reducing a disjunction operation.

1. Flatten the disjunction.
2. Deduplicate the disjuncts.
3. Remove the bottom disjuncts.
4. If the disjunct is left with only one element, return the value.
5. If the disjunct is left with no elements, return the first bottom it found.
-}
normalizeDisj :: (Val -> Bool) -> Disj -> VCur -> RM Val
normalizeDisj discardDisjunct d vc = do
  dStr <- tshow (mkDisjVal d)
  traceSpanArgsRMTC "normalizeDisj" (show dStr) vc $ do
    flattened <- flattenDisjunction discardDisjunct d
    final <- modifyDisjuncts discardDisjunct flattened vc
    debugInstantRM
      "normalizeDisj"
      ( printf
          "flattened: %s, flattened disjuncts: %s, final: %s"
          (show $ mkDisjVal flattened)
          (show $ dsjDisjuncts flattened)
          (show final.dsjDisjuncts)
      )
      vc
    if
      | null final.dsjDisjuncts ->
          let
            noVals = filter (\case IsNoVal -> True; _ -> False) flattened.dsjDisjuncts
            bottoms = filter (isJust . rtrBottom) flattened.dsjDisjuncts
           in
            if
              | length noVals == length flattened.dsjDisjuncts -> return $ mkNewVal VNNoVal
              | not (null bottoms) -> return $ head bottoms
              | otherwise ->
                  throwFatal $ printf "normalizeDisj: no disjuncts left in %s" (show flattened.dsjDisjuncts)
      -- When there is only one disjunct and the disjunct is not default, the disjunction is converted to the disjunct.
      | length final.dsjDisjuncts == 1 && null (dsjDefIndexes final) -> return $ head final.dsjDisjuncts
      | otherwise -> return $ mkDisjVal final

{- | Flatten the disjunction.

Because disjunction operation is associative, we can flatten the disjuncts. The nested disjunctions were like
parenthesized disjunctions. For example, (a | *b) | c | (d | e) = a | *b | c | d | e.

Notice before this step, there is no marked terms in the disjunction. For example, *(a | *b) has been reduced to (a |
*b).

This handles the case where a marked term is a reference. For example the f of the *f | v1 would be <f, f> if we use the
value-default pair. When the value of the f changes to a disjunction like *1 | 2, the flattened disjuncts would be 1 and
2 with the default index of di, where di is the index of the disjunct f. When the value of f changes to 1 | 2, the
flattened disjuncts would be 1 and 2 with the default indexes of di and di + 1.

It also follows the rules of disjunction operation:
D0: ⟨v1⟩ | ⟨v2⟩         => ⟨v1|v2⟩
D1: ⟨v1, d1⟩ | ⟨v2⟩     => ⟨v1|v2, d1⟩
D2: ⟨v1, d1⟩ | ⟨v2, d2⟩ => ⟨v1|v2, d1|d2⟩

TODO: more efficiency
-}
flattenDisjunction :: (Val -> Bool) -> Disj -> RM Disj
flattenDisjunction discardDisjunct (Disj{dsjDefIndexes = idxes, dsjDisjuncts = disjuncts}) = do
  reps <- mapM treeToRepString disjuncts
  debugInstantOpRM
    "flattenDisjunction"
    (printf "before disjuncts: %s, defIdxes: %s" (show reps) (show idxes))
    emptyValAddr

  -- Use foldl because the new default indexes are based on the length of the accumulated disjuncts.
  (newIndexes, newDisjs) <- foldM flatten ([], []) (zip [0 ..] disjuncts)
  return $ emptyDisj{dsjDefIndexes = newIndexes, dsjDisjuncts = newDisjs}
 where
  origDefIdxesSet = Set.fromList idxes
  -- Suppose we are processing the ith disjunct, and we have accumulated the disjuncts xs.
  -- If the ith disjunct is not a disjunction, then we can just add it to the disjuncts. We also need to add the index
  -- to the default indexes if it belongs to the default disjunction.
  flatten (accIs, accDs) (origIdx, t) = do
    debugInstantOpRM
      "flattenDisjunction"
      (printf "At %s, val: %s" (show origIdx) (show t))
      emptyValAddr
    case rtrDisj t of
      Just sub -> do
        Disj{dsjDefIndexes = subDefIndexes, dsjDisjuncts = subDisjs} <- flattenDisjunction discardDisjunct sub
        let
          -- Add offset to the indexes of the new disjuncts. The offset is the length of the accumulated disjuncts.
          newDefIndexes =
            -- If no sub defaults found for the disjunct but the disjunct is a default disjunct, that means the
            -- disjunct has been flattened to multiple disjuncts.
            if null subDefIndexes && origIdx `Set.member` origDefIdxesSet
              then map (+ length accDs) [0 .. length subDisjs - 1]
              else map (+ length accDs) subDefIndexes
        return (accIs ++ newDefIndexes, accDs ++ subDisjs)
      _ ->
        return
          ( if origIdx `Set.member` origDefIdxesSet
              -- The index of the new disjunct is the length of the accumulated disjuncts.
              then accIs ++ [length accDs]
              else accIs
          , accDs ++ [t]
          )

{- | Remove unwanted or rewrite the disjuncts.

All the disjuncts have been reduced before this step.

Unwanted disjuncts include:

* duplicate default disjuncts
* duplicate disjuncts
* bottom disjuncts

Rewrite includes:

* IsRefCycle
* Struct with embedded value

TODO: consider make t an instance of Ord and use Set to remove duplicates.
-}
modifyDisjuncts :: (Val -> Bool) -> Disj -> VCur -> RM Disj
modifyDisjuncts discardDisjunct idisj@(Disj{dsjDefIndexes = dfIdxes, dsjDisjuncts = disjuncts}) vc = do
  disjStr <- tshow (mkDisjVal idisj)
  traceSpanArgsAdaptRM
    "modifyDisjuncts"
    (show disjStr)
    emptySpanValue
    vc
    $ do
      (newIndexes, newDisjs) <- foldM go ([], []) (zip [0 ..] disjuncts)
      return $ emptyDisj{dsjDefIndexes = newIndexes, dsjDisjuncts = newDisjs}
 where
  defValues = map (disjuncts !!) dfIdxes
  origDefIdxesSet = Set.fromList dfIdxes

  go (accIs, accDisjs) (idx, v) = do
    let partialCancelled conjs = do
          rfbAddr <- rfbAddrToAddr <$> addrIsRfbAddr (vcAddr vc)
          return $
            filter
              ( \x -> case x of
                  FixSelect rcAddr -> rcAddr /= rfbAddr
                  _ -> True
              )
              conjs
    case v of
      -- Try if the RCs are cancellable.
      IsFix f
        | Just conjs <- partialCancelled f.conjs
        , -- If all conjuncts are cancelled, then we just use the inner value.
          null conjs ->
            -- If the inner value is NoVal, we just discard it.
            if f.val == VNNoVal
              then return (accIs, accDisjs)
              else return $ updateDisjuncts (accIs, accDisjs) (idx, mkNewVal f.val)
      IsEmbedVal ev -> return $ updateDisjuncts (accIs, accDisjs) (idx, ev)
      _ -> return $ updateDisjuncts (accIs, accDisjs) (idx, v)

  updateDisjuncts (accIs, accXs) (idx, x) =
    let
      notAddedDisj = not (x `elem` accXs)
      -- If the disjunct is equal to the default value. Note that it does not mean the disjunct is the original default
      -- value.
      isValEqDef = x `elem` defValues
      -- The disjunct is kept if all of the following conditions are met:
      -- 1. it is not a bottom disjunct.
      -- 2. it is not added before
      -- 3. it is not a default value OR it is one of the default disjuncts and its index is in the original default
      -- indexes.
      -- The second condition makes sure the relative order of the default disjuncts is kept.
      -- For example, *b | c | a | b | *a should be reduced to <b | c | a, 0|2>.
      keepDisjunct =
        not (discardDisjunct x)
          && notAddedDisj
          && (not isValEqDef || idx `Set.member` origDefIdxesSet)
      -- The disjunct is default if it is one of the default disjuncts and it is not seen before.
      isDefIndex = keepDisjunct && isValEqDef
     in
      -- Add the current disjunct index to the default indexes if condition is met.
      ( if isDefIndex then accIs ++ [length accXs] else accIs
      , if keepDisjunct then accXs ++ [x] else accXs
      )

{- | Construct a list of disjuncts from the disjunction terms.

Some existing rules for marked disjunctions:
M0:  ⟨v⟩    => ⟨v⟩        don't introduce defaults for unmarked term
M1: *⟨v⟩    => ⟨v, v⟩     introduce identical default for marked term
M2: *⟨v, d⟩ => ⟨v, d⟩     keep existing defaults for marked term
M3:  ⟨v, d⟩ => ⟨v⟩        strip existing defaults from unmarked term
-}
procMarkedTerms :: [DisjTerm] -> RM [Val]
procMarkedTerms terms = do
  -- disjoin operation allows incompleteness.
  let hasMarked = any dstMarked terms
  return $
    foldr
      ( \term accDisjuncts ->
          let val = dstValue term
           in if
                -- Apply Rule M1 and M2
                | hasMarked && dstMarked term ->
                    setVN
                      ( VNDisj $
                          maybe
                            -- Rule M1
                            (emptyDisj{dsjDefIndexes = [0], dsjDisjuncts = [val]})
                            ( \d ->
                                if null (dsjDefIndexes d)
                                  -- Rule M1
                                  then d{dsjDefIndexes = [0 .. length (dsjDisjuncts d)]}
                                  -- Rule M2
                                  else d
                            )
                            (rtrDisj val)
                      )
                      val
                      : accDisjuncts
                -- Apply Rule M0 and M3
                | hasMarked ->
                    maybe
                      val
                      (\d -> setVN (VNDisj $ d{dsjDefIndexes = []}) val)
                      (rtrDisj val)
                      : accDisjuncts
                | otherwise -> val : accDisjuncts
      )
      []
      terms

reduceCompreh :: Comprehension -> RM ()
reduceCompreh cph = traceSpanTM "reduceCompreh" $ do
  r <- comprehend 0 cph.args (IterCtx 0 Map.empty (Right []))
  res <- case r.res of
    Left t -> return t
    Right vs ->
      if cph.isListCompreh
        then return $ mkListVal vs vs
        else case vs of
          [] -> return $ mkStructVal emptyStruct
          [x] -> return x
          _ -> do
            let mutT = mkMutableVal $ mkUnifyOp vs
            inTempTM "reduceCompreh" mutT $ reduce >> getTMVal

  debugInstantTM "reduceCompreh" (printf "comprehension result: %s" (show res))
  -- The result could be a struct, list or noval. But we should get rid of the mutable if there is any.
  modifyTMVN (valNode res)
  reducePureVN

data IterCtx = IterCtx
  { iterCnt :: Int
  -- ^ The count of the iterations.
  , bindings :: Map.Map TextIndex Val
  , res :: Either Val [Val]
  -- ^ It contains a list of resulted structs that are generated by each iteration.
  }
  deriving (Show)

instance ToJSON IterCtx where
  toJSON IterCtx{iterCnt} =
    object
      [ "iterCnt" .= iterCnt
      -- , "bindings" .= Map.map oneLinerStringOfVal bindings
      -- , "res" .= case res of
      --     Left t -> object ["error" .= oneLinerStringOfVal t]
      --     Right ts -> object ["values" .= map oneLinerStringOfVal ts]
      ]

instance ToJSONWTIndexer IterCtx where
  ttoJSON i = do
    bds <- ttoJSON i.bindings
    r <- case i.res of
      Left t -> do
        tRep <- oneLinerStringOfVal t
        return $ toJSON tRep
      Right ts -> do
        tReps <- mapM oneLinerStringOfVal ts
        return $ toJSON tReps
    return $
      object
        [ "iterCnt" .= i.iterCnt
        , "bindings" .= bds
        , "res" .= r
        ]

tshowBindings :: Map.Map TextIndex Binding -> RM T.Text
tshowBindings binds = do
  pairs <-
    mapM
      ( \(nameIdx, b) -> do
          name <- tshow nameIdx
          trep <- oneLinerStringOfVal b.value
          return $ printf "%s: %s" (T.unpack name) (T.unpack trep)
      )
      (Map.toList binds)
  return $ T.pack $ "{" ++ intercalate ", " pairs ++ "}"

{- | Iterate through the comprehension clauses.

The iteration is done in a depth-first manner. If all clauses are processed, it creates a new struct with the
bindings and adds the struct to the result list.
-}
comprehend :: Int -> Seq.Seq ComprehArg -> IterCtx -> RM IterCtx
comprehend i args iterCtx
  -- The case for the template struct.
  | i >= length args - 1 = traceSpanTM
      (printf "comprehend_last_iter_cl itercnt:%s, arg: %d" (show iterCtx.iterCnt) i)
      $ case iterCtx.res of
        Left err -> do
          rep <- treeToRepString err
          throwFatal $ printf "should not reach the leaf node if the result is already an error: %s" rep
        Right vs -> do
          -- Fork the template struct so that references in the struct can be resolved.
          r <-
            inSubTM
              (mkMutArgFeature i False)
              ( do
                  attachBindings iterCtx.bindings
                  forkStruct
              )
          -- Make the forked struct of this iteration immutable because it would simplify later unification of
          -- iteration results, mostly because of removal of the embedded value.
          r2 <- inTempTM "iter_struct" r $ reduceToNonMut >> setValImmutable <$> getTMVal
          return $ iterCtx{res = Right (vs ++ [r2]), iterCnt = iterCtx.iterCnt + 1}
  | otherwise = reduceClause i args iterCtx

-- | Fork the struct template for the comprehension iteration.
forkStruct :: RM Val
forkStruct = do
  t <- getTMVal
  case t of
    IsStruct struct
      | IsValImmutable <- t -> do
          -- The original let bindings in the struct should take the precedence over the iteration bindings.
          newStruct <- mkUnique struct
          return $ setVN (VNStruct newStruct) t
    -- The template struct can have embedded values.
    _
      | IsValMutable mut <- t
      , let args = getSOpArgs mut
      , (_, a) Seq.:<| _ <- args
      , IsStruct tmplStruct <- a -> do
          newStruct <- mkUnique tmplStruct
          inSubTM (mkMutArgFeature 0 True) $ modifyTMVN $ VNStruct newStruct
          forM_ [1 .. length args - 1] $ \i ->
            inSubTM (mkMutArgFeature i True) $ modifyTMVal $ \x -> x{embType = ETEmbedded newStruct.stcID}
          getTMVal
    _ -> throwFatal "attachBindings can only be used with a struct template"
 where
  mkUnique struct = do
    sid <- allocRMObjID
    newDynPairs <-
      mapM
        ( \df -> do
            oid <- allocRMObjID
            return (oid, df{dsfID = oid}, df.dsfID)
        )
        (IntMap.elems struct.stcDynFields)
    let
      dynIDMap = IntMap.fromList $ map (\(newID, _, oldID) -> (oldID, newID)) newDynPairs
      newDyns = IntMap.fromList $ map (\(newID, df, _) -> (newID, df)) newDynPairs
    newCnstrPairs <-
      mapM
        ( \cnstr -> do
            cid <- allocRMObjID
            return (cid, cnstr{scsID = cid})
        )
        (IntMap.elems struct.stcCnstrs)
    let newCnstrs = IntMap.fromList newCnstrPairs
        newOrdLabels =
          map
            ( \case
                StructStaticFieldLabel name -> StructStaticFieldLabel name
                StructDynFieldOID oldID -> StructDynFieldOID (fromJust $ IntMap.lookup oldID dynIDMap)
            )
            struct.stcOrdLabels
    return
      struct
        { stcID = sid
        , stcDynFields = newDyns
        , stcCnstrs = newCnstrs
        , stcOrdLabels = newOrdLabels
        }

-- | Reduce the ith clause of the comprehension in the depth-first manner.
reduceClause :: Int -> Seq.Seq ComprehArg -> IterCtx -> RM IterCtx
reduceClause _ _ iterCtx@IterCtx{res = Left _} = return iterCtx
reduceClause i args iterCtx = case args `Seq.index` i of
  ComprehArgStructTmpl _ -> throwFatal "ComprehArgStructTmpl should not appear in comprehension clauses"
  ComprehArgLet letName _ -> do
    t <- reduceClauseWithBindings i iterCtx.bindings
    case t of
      IsNoVal -> return iterCtx
      IsBottom _ -> return $ iterCtx{res = Left t}
      _ -> comprehend (i + 1) args (iterCtx{bindings = Map.insert letName t iterCtx.bindings})
  ComprehArgIf _ -> do
    t <- reduceClauseWithBindings i iterCtx.bindings
    case t of
      IsNoVal -> return iterCtx
      IsBottom _ -> return $ iterCtx{res = Left t}
      _ -> case rtrAtom t of
        Just (Bool True) -> comprehend (i + 1) args iterCtx
        -- Do not go to next clause if the condition is false.
        Just (Bool False) -> return iterCtx
        _ -> return $ iterCtx{res = Left $ mkBottomVal $ printf "%s is not a boolean" (showValSymbol t)}
  ComprehArgFor k vM _ -> do
    t <- reduceClauseWithBindings i iterCtx.bindings
    if
      | IsNoVal <- t -> return iterCtx
      | IsBottom _ <- t -> return $ iterCtx{res = Left t}
      -- TODO: only iterate optional fields
      | IsStruct struct <- t ->
          foldM
            ( \acc (labelIdx, field) -> do
                label <- tshow labelIdx
                comprehend
                  (i + 1)
                  args
                  ( acc
                      { bindings =
                          Map.union
                            ( Map.fromList $
                                maybe
                                  [(k, ssfValue field)]
                                  (\v -> [(k, mkAtomVal (String label)), (v, ssfValue field)])
                                  vM
                            )
                            acc.bindings
                      }
                  )
            )
            iterCtx
            (Map.toList $ stcFields struct)
      | Just (List{store}) <- rtrList t ->
          foldM
            ( \acc (idx, element) ->
                comprehend
                  (i + 1)
                  args
                  ( acc
                      { bindings =
                          Map.union
                            ( Map.fromList $
                                maybe
                                  [(k, element)]
                                  (\v -> [(k, mkAtomVal (Int idx)), (v, element)])
                                  vM
                            )
                            acc.bindings
                      }
                  )
            )
            iterCtx
            (zip [0 ..] (toList store))
      | otherwise ->
          return $
            iterCtx
              { res = Left $ mkBottomVal $ printf "%s is not iterable" (showValSymbol t)
              }

-- | Embed a value to a new block and return a new tree cursor that points to the embedded value.
reduceClauseWithBindings :: Int -> Map.Map TextIndex Val -> RM Val
reduceClauseWithBindings i bindings = do
  vc <- getTMCursor
  case vc of
    VCFocus (IsValMutable mut@(Op (Compreh cph))) -> do
      let newTC = modifyVCFocus (\t -> t{op = Just $ setOpInSOp (Compreh cph{iterBindings = bindings}) mut}) vc
      putTMCursor newTC
      inSubTM (mkMutArgFeature i False) (reduce >> getTMVal)
    _ -> throwFatal "reduceClauseWithBindings can only be used with a mutable comprehension"

-- | Make bindings immutable and insert into the template struct.
attachBindings :: Map.Map TextIndex Val -> RM ()
attachBindings rawBindings = do
  let bindings = Map.map setValImmutable rawBindings
  t <- getTMVal
  case t of
    IsStruct struct
      | IsValImmutable <- t -> do
          -- The original let bindings in the struct should take the precedence over the iteration bindings.
          let
            cleanBindings = Map.filter (not . isIterVar) struct.stcBindings
            newBindings =
              Map.union
                cleanBindings
                (Map.map (\x -> Binding x True) bindings)
          bStr <- tshowBindings newBindings
          debugInstantTM "attachBindings" (printf "imm struct's new bindings: %s" bStr)
          modifyTMVN $ VNStruct $ struct{stcBindings = newBindings}
    -- The template struct can have embedded values.
    _
      | IsValMutable mut <- t
      , let args = getSOpArgs mut
      , (f, a) Seq.:<| _ <- args
      , IsStruct tmplStruct <- a -> do
          -- The original let bindings in the struct should take the precedence over the iteration bindings.
          let
            cleanBindings = Map.filter (not . isIterVar) tmplStruct.stcBindings
            newBindings =
              Map.union
                cleanBindings
                (Map.map (\x -> Binding x True) bindings)
          bStr <- tshowBindings newBindings
          debugInstantTM "attachBindings" (printf "new bindings: %s" bStr)
          inSubTM f $ modifyTMVN $ VNStruct $ tmplStruct{stcBindings = newBindings}
    _ -> throwFatal "attachBindings can only be used with a struct template"

resolveInterpolation :: Interpolation -> [Val] -> RM (Maybe Val)
resolveInterpolation l args = do
  r <-
    foldM
      ( \accRes seg -> case seg of
          IplSegExpr j -> do
            let r = args !! j
            if
              | Just s <- rtrString r -> return $ (`T.append` s) <$> accRes
              | Just i <- rtrInt r -> return $ (`T.append` (T.pack $ show i)) <$> accRes
              | Just b <- rtrBool r -> return $ (`T.append` (T.pack $ show b)) <$> accRes
              | Just f <- rtrFloat r -> return $ (`T.append` (T.pack $ show f)) <$> accRes
              | Just _ <- rtrStruct r ->
                  return $
                    Left $
                      mkBottomVal $
                        printf "can not use struct in interpolation: %s" (showValSymbol r)
              | Just _ <- rtrList r ->
                  return $
                    Left $
                      mkBottomVal $
                        printf "can not use list in interpolation: %s" (showValSymbol r)
              | otherwise -> throwFatal $ printf "unsupported interpolation expression: %s" (showValSymbol r)
          IplSegStr s -> return $ (`T.append` s) <$> accRes
      )
      (Right T.empty)
      (itpSegs l)
  case r of
    Left err -> return $ Just err
    Right res -> return $ Just $ mkAtomVal (String res)

reduceFix :: Fix -> RM ()
reduceFix f = traceSpanTM "reduceFix" $ do
  -- First we need to make the current tree immutable so that later reduce will not re-run functions.
  origTreeOp <- op <$> getTMVal
  modifyTMVal setValImmutable
  -- Because withRCs only has one inner structure, which will have the dependency addresses as its wrapper, we
  -- can just put the inner structure first.
  supersedeTMVN f.val

  -- Calculate a temporary result first.
  reducePureVN
  -- In the intermediate steps of resolving RCs, we do not want to trigger recalculation of functions.
  modify' $ mapCtx (\c -> c{noRecalc = True})
  unknownExists <- runFix 0 f.conjs
  modify' $ mapCtx (\c -> c{noRecalc = False})

  -- Restore the original valGenEnv.
  modifyTMVal $ \t -> t{op = origTreeOp}

  if not unknownExists
    -- reduce the sub fields again so that dependents of the sub fields of the inner value can be notified.
    -- The value of the top of the tree will not be used to notify dependents here. Because this function should be called
    -- inside a reduce. At the end of the outer reduce, the dependents of the top of the tree will be notified.
    -- TODO: optimize this step to avoid redundant reduce by recursively notifying the dependents of the fields.
    -- If there is no RCs left, no need to keep the wrapper. Make the inner value the top of the tree.
    then reducePureVN
    else unwrapTMVN (\x -> VNFix (Fix (valNode x) f.conjs unknownExists))

{- | Find the fixed point of unifying normal conjuncts and reference cycles.

During the function call, the top of the tree will be updated to the temporary result of unifying normal
conjuncts. After the function call, the tree will be updated to the reduced result.

Unify operators are normal conjuncts, reference cycles and references to sub-fields in reference cycles.
The algorithm is as follows:
1. Calculate a temporary result for normal_conjs, which is r
2. Loop to resolve the RC_subs
   - Fetch the sub value from the result
   - If the sub value is new, meaning it is not an instance of the result, unify it with the result. r' = r & r.f.
   - Terminate when no new sub values can be fetched.

Proof of why fetching sub-fields from r is correct:

let fval = r.f,

1. If r.f is a struct with {f: dsub}, the fetched sub can modify the field f in the final result by having fval' =
fval & dsub. Then we do fetch again and get fval & dsub. The value will be unified with f field again, but it is
(fval & dsub) & (fval & dsub), which is the same as fval & dsub.
2. If sub is a struct but without sub field f, then r.f is unknown.
3. If sub is not a struct, then r.f is unknown.
-}
runFix :: Int -> [FixConj] -> RM Bool
runFix count conjs = do
  (more, unknownExists) <- traceSpanTM (printf "runFix %d" count) $ do
    prevT <- getTMVal
    unifyTC <- getTMCursor
    -- find known RCs from the v
    let unifyAddr = vcAddr unifyTC
    (newConjTCs, unknownExists) <-
      foldM
        ( \(accNewConjs, accUE) conj -> case conj of
            FixSelect rcAddr ->
              if rcAddr == unifyAddr
                -- If the address is the same as the unifyTC, which means the RC refers to itself, we can skip it.
                then return (accNewConjs, accUE)
                else
                  let rest = trimPrefixAddr unifyAddr rcAddr
                      subTCM = goDownVCAddr rest unifyTC
                   in case subTCM of
                        Just subTC -> return (subTC : accNewConjs, accUE)
                        -- The sub value is not found, we treat it as unknown.
                        Nothing -> return (accNewConjs, True)
            FixCompreh ct -> inTempTM "runFix_reduce_compreh_conj" ct $ do
              vc <- getTMCursor >>= prepConj True
              putTMCursor vc
              reduce
              rtc <- getTMCursor
              case focus rtc of
                IsNoVal -> return (accNewConjs, True)
                _ -> return (rtc : accNewConjs, accUE)
        )
        ([], False)
        conjs

    tStr <- tshow prevT
    newConjsStr <- mapM tshow newConjTCs
    debugInstantRM
      "runFix"
      ( printf
          "resolving Fix, prev result: %s, newConjsStr: %s, unknownExists: %s"
          tStr
          (show newConjsStr)
          (show unknownExists)
      )
      unifyTC

    r <-
      if null newConjTCs
        then return $ Just $ focus unifyTC
        else Just <$> mergeTCs (unifyTC : newConjTCs) unifyTC
    modifyTMVN (valNode $ fromJust r)
    reducePureVN
    t <- getTMVal
    if t == prevT
      -- We have reached a fixed point.
      then return (False, unknownExists)
      -- Only update the tree node. Other parts should remain the same.
      else do
        prevTRep <- treeToRepString prevT
        newTRep <- treeToRepString t
        debugInstantRM
          "runFix"
          (printf "Fix iteration updated tree from: %s\nto:\n%s" prevTRep newTRep)
          unifyTC
        return (True, unknownExists)

  if more
    then runFix (count + 1) conjs
    else return unknownExists
