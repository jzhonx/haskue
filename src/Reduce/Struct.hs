{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Struct where

import Control.Monad (foldM, unless, when)
import Cursor
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Feature
import {-# SOURCE #-} Reduce.Core (reduce)
import Reduce.Monad (
  RM,
  addRMDanglingLet,
  delTMDepPrefix,
  descendTMSegMust,
  getRMDanglingLets,
  getTMAbsAddr,
  getTMCursor,
  getTMVal,
  inSubTM,
  liftEitherRM,
  modifyTMVN,
  propUpTM,
 )
import Reduce.Reference (IdentType (..), searchTCIdent)
import Reduce.TraceSpan (
  debugInstantRM,
  debugInstantTM,
  emptySpanValue,
  traceSpanAdaptRM,
  traceSpanArgsRMTC,
  traceSpanRMTC,
  traceSpanTM,
 )
import Reduce.Unification (patMatchLabel)
import StringIndex (ShowWTIndexer (..), TextIndex, TextIndexerMonad, ToJSONWTIndexer (..), textToTextIndex)
import Text.Printf (printf)
import Util.Format (msprintf, packFmtA)
import Value
import Value.Export.Debug (treeToRepString)

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
      debugInstantTM "validateStructPerm" (msprintf "permission error: %s" [packFmtA rep])
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
    ( const $
        return $
          printf
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
          debugInstantTM
            "handleSObjChange"
            (msprintf "dsf: %s, rE: %s, dsf: %s" [packFmtA $ show dsf, packFmtA $ show rE, packFmtA $ show dsf])
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
                ( msprintf
                    "-: %s, +: %s, all: %s"
                    [packFmtA remAffLabels, packFmtA addAffLabels, packFmtA affectedLabels]
                )

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
              ( msprintf
                  "-: %s, +: %s, new struct: %s"
                  [packFmtA $ remAffLabels, packFmtA $ addAffLabels, packFmtA $ mkStructVal newStruct]
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
        ( msprintf
            "converted dynamic field to static field, name: %s, old field: %s, new field: %s"
            [packFmtA name, packFmtA (show res), packFmtA (show newSF)]
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
              ( const $
                  return $
                    printf
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
