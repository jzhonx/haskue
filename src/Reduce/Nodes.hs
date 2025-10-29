{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Nodes where

import Control.Monad (foldM, forM_, unless, when)
import Control.Monad.Reader (asks)
import Cursor
import Data.Aeson (KeyValue (..), ToJSON (..), object)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import Path
import Reduce.RMonad (
  HasReduceParams (..),
  ReduceMonad,
  ResolveMonad,
  addRMDanglingLet,
  allocRMObjID,
  createCnstr,
  debugInstantOpRM,
  debugInstantRM,
  debugInstantTM,
  debugSpanAdaptRM,
  debugSpanAdaptTM,
  debugSpanArgsAdaptRM,
  debugSpanArgsAdaptTM,
  debugSpanArgsSimpleRM,
  debugSpanMTreeRM,
  debugSpanSimpleRM,
  debugSpanTM,
  debugSpanTreeRM,
  delTMDependentPrefix,
  descendTMSegMust,
  getRMDanglingLets,
  getTMAbsAddr,
  getTMCursor,
  getTMTree,
  inSubTM,
  inTempTM,
  liftFatal,
  modifyTMTN,
  modifyTMTree,
  propUpTM,
  putTMCursor,
  putTMTree,
  throwFatal,
 )
import Reduce.RefSys (IdentType (..), searchTCIdent)
import {-# SOURCE #-} Reduce.Root (reduce, reducePureTN, reduceToNonMut)
import Reduce.UnifyOp (patMatchLabel)
import StringIndex (ShowWithTextIndexer (..), TextIndex, TextIndexerMonad, textIndexToText, textToTextIndex)
import Text.Printf (printf)
import Value
import Value.Util.TreeRep (treeToRepString)

reduceStruct :: (ReduceMonad r s m) => m ()
reduceStruct = debugSpanTM "reduceStruct" $ do
  -- First assign the base fields to the fields.
  whenStruct
    (\s -> modifyTMTN (TNStruct $ s{stcFields = stcStaticFieldBases s}))

  whenStruct
    ( \s ->
        mapM_
          (\i -> inSubTM (BlockTASeg (DynFieldTASeg i 0)) reduce)
          (IntMap.keys $ stcDynFields s)
    )
  whenStruct
    ( \s ->
        mapM_
          (\i -> inSubTM (BlockTASeg (PatternTASeg i 0)) reduce)
          (IntMap.keys $ stcCnstrs s)
    )
  -- Reduce lets.
  whenStruct
    ( \s -> do
        tc <- getTMCursor
        mapM_
          ( \k -> whenStruct $ \_ -> do
              errM <- checkRedecl True k tc
              case errM of
                Just err -> modifyTMTN (treeNode err)
                Nothing -> inSubTM (BlockTASeg $ refIdentToLetTASeg k) $ do
                  reduce
                  addr <- getTMAbsAddr
                  let isIterVar = (s.stcBindings Map.! k).isIterVar
                  unless isIterVar $ addRMDanglingLet addr
          )
          (Map.keys s.stcBindings)
    )
  -- Reduce all fields.
  whenStruct
    (\s -> mapM_ reduceStructField (Map.keys . stcFields $ s))

  -- Validate if all let bindings are referred.
  -- Return the last error if multiple unreferenced let bindings exist.
  whenStruct $ \s -> do
    baseAddr <- getTMAbsAddr
    mapM_
      ( \k -> do
          let addr = appendSeg baseAddr (BlockTASeg $ refIdentToLetTASeg k)
          danglings <- getRMDanglingLets
          when (addr `elem` danglings) $ do
            kStr <- tshow k
            modifyTMTN $ TNBottom $ Bottom $ printf "unreferenced let clause let %s" (show kStr)
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
        modifyTMTN (TNStruct newStruct)
    )

  validateStructPerm

whenStruct :: (ReduceMonad r s m) => (Struct -> m ()) -> m ()
whenStruct f = do
  t <- getTMTree
  case t of
    IsStruct struct -> f struct
    -- The struct might have been turned to another type due to embedding or reducing fields.
    _ -> return ()

validateStructPerm :: (ReduceMonad r s m) => m ()
validateStructPerm = debugSpanTM "validateStructPerm" $ whenStruct $ \s -> do
  tc <- getTMCursor
  r <-
    foldM
      ( \acc perm -> case acc of
          Just _ -> return acc
          Nothing -> validatePermItem s perm tc
      )
      Nothing
      (stcPerms s)
  case r of
    Just err -> do
      debugInstantTM "validateStructPerm" (printf "permission error: %s" (treeToRepString err))
      modifyTMTN (TNStruct $ s{stcPermErr = Just err})
    Nothing -> modifyTMTN (TNStruct $ s{stcPermErr = Nothing})

{- | Validate the permission item.

A struct must be provided so that dynamic fields and constraints can be found.

It constructs the allowing labels and constraints and checks if the joining labels are allowed.
-}
validatePermItem :: (ResolveMonad s r m) => Struct -> PermItem -> TrCur -> m (Maybe Tree)
validatePermItem struct p tc = debugSpanSimpleRM "validatePermItem" tc $ do
  labelMs <- mapM labelToTextIdx $ Set.toList $ piLabels p
  opLabelMs <- mapM labelToTextIdx $ Set.toList $ piOpLabels p
  let
    cnstrs = IntMap.fromList $ map (\i -> (i, stcCnstrs struct IntMap.! i)) (Set.toList $ piCnstrs p)
  case (sequence labelMs, sequence opLabelMs) of
    (Just labels, Just opLabels) -> do
      foldM
        ( \acc opLabel -> case acc of
            Just _ -> return acc
            Nothing -> do
              allowed <- checkLabelAllowed (Set.fromList labels) cnstrs opLabel tc
              if allowed
                then return acc
                else do
                  s <- textIndexToText opLabel
                  -- show s so that we have quotes around the label.
                  return $ Just (mkBottomTree $ printf "%s is not allowed" (show s))
        )
        Nothing
        (Set.fromList opLabels)
    -- If not all dynamic fields can be resolved to string labels, we can not check the permission.
    -- This is what CUE does.
    _ -> return Nothing
 where
  labelToTextIdx :: (TextIndexerMonad s m) => StructFieldLabel -> m (Maybe TextIndex)
  labelToTextIdx (StructStaticFieldLabel n) = return $ Just n
  labelToTextIdx (StructDynFieldOID i) = do
    let strM = do
          df <- IntMap.lookup i (stcDynFields struct)
          rtrString (dsfLabel df)
    case strM of
      Just s -> Just <$> textToTextIndex s
      Nothing -> return Nothing

checkLabelAllowed ::
  (ResolveMonad r s m) =>
  Set.Set TextIndex ->
  IntMap.IntMap StructCnstr ->
  TextIndex ->
  TrCur ->
  m Bool
checkLabelAllowed baseLabels baseAllCnstrs newLabel tc =
  debugSpanArgsSimpleRM
    "checkLabelAllowed"
    ( printf
        "newLabel: %s, baseLabels: %s, baseAllCnstrs: %s"
        (show newLabel)
        (show $ Set.toList baseLabels)
        (show $ IntMap.toList baseAllCnstrs)
    )
    tc
    $ _checkLabelAllowed baseLabels baseAllCnstrs newLabel tc

_checkLabelAllowed ::
  (ResolveMonad r s m) =>
  Set.Set TextIndex ->
  IntMap.IntMap StructCnstr ->
  TextIndex ->
  TrCur ->
  m Bool
_checkLabelAllowed baseLabels baseAllCnstrs newLabel tc
  | newLabel `Set.member` baseLabels = return True
  | otherwise =
      -- A "new" field is allowed if there is at least one pattern that matches the field.
      foldM
        ( \acc cnstr ->
            if acc
              then return acc
              else do
                let pat = scsPattern cnstr
                patMatchLabel pat newLabel tc
        )
        -- By default, "new" label is not allowed.
        False
        (IntMap.elems baseAllCnstrs)

checkRedecl :: (ResolveMonad r s m) => Bool -> RefIdent -> TrCur -> m (Maybe Tree)
checkRedecl nameIsLetVar ident tc = do
  -- Fields and let bindings are made exclusive in the same block in the evalExpr step, so we only need to make sure
  -- in the parent block that there is no field with the same name.
  parResM <-
    if isTCRoot tc
      then return Nothing
      else do
        ptc <- liftFatal (propUpTC tc)
        m <- searchTCIdent ident ptc
        return $ maybe Nothing (\(x, y) -> Just (tcAddr x, y)) m
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

aliasErr :: (ResolveMonad r s m) => RefIdent -> m Tree
aliasErr name = do
  nameStr <- tshow name
  return $ mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" (show nameStr)

lbRedeclErr :: (ResolveMonad r s m) => RefIdent -> m Tree
lbRedeclErr name = do
  nameStr <- tshow name
  return $ mkBottomTree $ printf "%s redeclared in same scope" (show nameStr)

{- | Reduce the struct field with the given name.

If the field is reduced to bottom, the whole struct becomes bottom.
-}
reduceStructField :: (ReduceMonad r s m) => TextIndex -> m ()
reduceStructField name = whenStruct $ \_ -> do
  tc <- getTMCursor
  errM <- checkRedecl False (RefIdent name) tc
  case errM of
    Just err -> modifyTMTN (treeNode err)
    Nothing -> do
      addr <- getTMAbsAddr
      r <- inSubTM (tIdxToStringTASeg name) (reduce >> getTMTree)
      case r of
        IsBottom _ | IsTGenImmutable <- r -> do
          modifyTMTN (treeNode r)
          delTMDependentPrefix addr
        _
          | isSCyclic r -> do
              modifyTMTN (treeNode $ mkBottomTree "structural cycle")
              delTMDependentPrefix addr
          | otherwise -> return ()

-- | Handle the post process of the mutable object change in the struct.
handleSObjChange :: (ReduceMonad r s m) => m [TreeAddr]
handleSObjChange = do
  tc <- getTMCursor
  seg <- liftFatal $ tcFocusSegMust tc
  stc <- liftFatal $ propUpTC tc
  let r = tcFocus tc
  case tcFocus stc of
    IsStruct struct
      | BlockTASeg (StringTASeg _) <- seg -> debugSpanAdaptTM (printf "handleSObjChange, seg: %s" (show seg)) (const $ toJSON ()) do
          let errM = case r of
                IsBottom _ | IsTGenImmutable <- r -> Just r
                _
                  | isSCyclic r -> Just $ mkBottomTree "structural cycle"
                  | otherwise -> Nothing
          case errM of
            Just err -> do
              modifyTMTN (treeNode err)
              delTMDependentPrefix $ tcAddr stc
            Nothing -> return ()
          return []
      | BlockTASeg (DynFieldTASeg i _) <- seg -> debugSpanAdaptTM (printf "handleSObjChange, seg: %s" (show seg)) (const $ toJSON ()) do
          (oldLRmd, remAffLabels) <- removeAppliedObject i struct stc
          let dsf = stcDynFields struct IntMap.! i
              allCnstrs = IntMap.elems $ stcCnstrs oldLRmd
          rE <- dynFieldToStatic (stcFields oldLRmd) dsf
          debugInstantTM "handleSObjChange" (printf "dsf: %s, rE: %s, dsf: %s" (show dsf) (show rE) (show dsf))
          case rE of
            Left err -> modifyTMTN (treeNode err) >> return []
            -- If the dynamic field label is incomplete, no change is made. But we still need to return the removed
            -- affected labels.
            Right Nothing -> return $ genAddrs (tcAddr stc) remAffLabels
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

              propUpTM >> modifyTMTN (TNStruct newS) >> descendTMSegMust seg
              return $ genAddrs (tcAddr stc) affectedLabels
      | BlockTASeg (PatternTASeg i _) <- seg -> debugSpanAdaptTM (printf "handleSObjChange, seg: %s" (show seg)) (const $ toJSON ()) do
          -- Constrain all fields with the new constraint if it exists.
          let cnstr = stcCnstrs struct IntMap.! i
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

          propUpTM >> modifyTMTN (TNStruct newStruct) >> descendTMSegMust seg
          unless (null affectedLabels) $
            debugInstantTM
              "handleSObjChange"
              ( printf
                  "-: %s, +: %s, new struct: %s"
                  (show remAffLabels)
                  (show addAffLabels)
                  (show $ mkStructTree newStruct)
              )
          return $ genAddrs (tcAddr stc) affectedLabels
    _ -> return []
 where
  genAddrs baseAddr = map (\name -> appendSeg baseAddr (tIdxToStringTASeg name))

getLabelFieldPairs :: Struct -> [(TextIndex, Field)]
getLabelFieldPairs struct = Map.toList $ stcFields struct

{- | Convert a dynamic field to a static field.

It returns a pair which contains reduced string and the newly created/updated field.
-}
dynFieldToStatic ::
  (ReduceMonad r s m) => Map.Map TextIndex Field -> DynamicField -> m (Either Tree (Maybe (TextIndex, Field)))
dynFieldToStatic fields df
  | Just name <- rtrString label = do
      nidx <- textToTextIndex name
      let
        unifier l r = mkMutableTree $ mkUnifyOp [l, r]
        newSF = dynToField df (Map.lookup nidx fields) unifier

      debugInstantTM
        "dynFieldToStatic"
        ( printf
            "converted dynamic field to static field, name: %s, old field: %s, new field: %s"
            name
            (show $ Map.lookup nidx fields)
            (show newSF)
        )
      return $ Right (Just (nidx, newSF))
  | Just _ <- rtrBottom label = return $ Left label
  -- Incomplete field label, no change is made. If the mutable was a reference with string value, then it would
  -- have been reduced to a string.
  | Nothing <- rtrNonUnion label = return $ Right Nothing
  | otherwise = return $ Left (mkBottomTree "label can only be a string")
 where
  label = dsfLabel df

{- | Apply pattern constraints ([pattern]: constraint) to the static field.

Returns the new field. If the field is not matched with the pattern, it returns the original field.
-}
constrainFieldWithCnstrs :: (ResolveMonad r s m) => TextIndex -> Field -> [StructCnstr] -> TrCur -> m Field
constrainFieldWithCnstrs name field cnstrs tc =
  foldM
    ( \accField cnstr -> do
        (newField, _) <- bindFieldWithCnstr name accField cnstr tc
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
bindFieldWithCnstr :: (ResolveMonad r s m) => TextIndex -> Field -> StructCnstr -> TrCur -> m (Field, Bool)
bindFieldWithCnstr name field cnstr tc = do
  let selPattern = scsPattern cnstr

  matched <- patMatchLabel selPattern name tc

  let
    fval = ssfValue field
    op = mkMutableTree $ mkUnifyOp [fval, scsValue cnstr]
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
filterMatchedNames :: (ResolveMonad r s m) => StructCnstr -> [TextIndex] -> TrCur -> m [TextIndex]
filterMatchedNames cnstr labels tc =
  foldM
    ( \acc name -> do
        matched <- patMatchLabel (scsPattern cnstr) name tc
        return $ if matched then name : acc else acc
    )
    []
    labels

{- | Remove the applied object from the fields.

Returns the updated struct and the list of labels whose fields are affected.

This is done by re-applying existing objects except the one that is removed because unification is a lossy operation.
-}
removeAppliedObject :: (ResolveMonad r s m) => Int -> Struct -> TrCur -> m (Struct, [TextIndex])
removeAppliedObject objID struct tc =
  debugSpanAdaptRM "removeAppliedObject" (Just . mkStructTree . fst) (const $ toJSON ()) tc $ do
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
              tc

            case baseRawM of
              Just raw -> do
                let
                  rawField = field{ssfValue = raw, ssfObjects = Set.empty}
                  fieldWithDyns =
                    foldr
                      (\dyn acc -> dynToField dyn (Just acc) unifier)
                      rawField
                      (IntMap.elems newDyns)
                newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems newCnstrs) tc
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
                    newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems newCnstrs) tc
                    return ((name, newField) : accUpdated, accRemoved)
        )
        ([], [])
        (fieldsUnifiedWithObject objID $ Map.toList $ stcFields struct)
    let res = removeStructFieldsByNames removedLabels $ updateStructWithFields remAffFields struct
    return (res, map fst remAffFields)
 where
  allCnstrs = stcCnstrs struct
  allDyns = stcDynFields struct
  unifier l r = mkMutableTree $ mkUnifyOp [l, r]

  -- Find the fields that are unified with the object
  fieldsUnifiedWithObject :: Int -> [(TextIndex, Field)] -> [(TextIndex, Field)]
  fieldsUnifiedWithObject j =
    foldr (\(k, field) acc -> if j `elem` ssfObjects field then (k, field) : acc else acc) []

-- | Apply the additional constraint to the fields.
applyCnstrToFields :: (ResolveMonad r s m) => StructCnstr -> Struct -> TrCur -> m (Struct, [TextIndex])
applyCnstrToFields cnstr struct tc = debugSpanSimpleRM "applyCnstrToFields" tc $ do
  (addAffFields, addAffLabels) <-
    foldM
      ( \(accFields, accLabels) (name, field) -> do
          (nf, isMatched) <- bindFieldWithCnstr name field cnstr tc
          if isMatched
            then return ((name, nf) : accFields, name : accLabels)
            else return (accFields, accLabels)
      )
      ([], [])
      (getLabelFieldPairs struct)
  let newStruct = updateStructWithFields addAffFields struct
  return (newStruct, addAffLabels)

reduceDisj :: (ReduceMonad r s m) => Disj -> m ()
reduceDisj d = do
  -- We have to reduce all disjuncts because they might be generated by merging one disjunction with another value.
  mapM_
    (\(i, _) -> inSubTM (DisjTASeg i) reduce)
    (zip [0 ..] (dsjDisjuncts d))

  tc <- getTMCursor
  case treeNode (tcFocus tc) of
    TNDisj nd -> do
      newDisjT <- normalizeDisj (isJust . rtrBottom) nd tc
      modifyTMTN (treeNode newDisjT)
    _ -> return ()

reduceList :: (ReduceMonad r s m) => List -> m ()
reduceList l = do
  r <-
    foldM
      ( \acc (i, origElem) -> do
          r <- inSubTM (IndexTASeg i) (reduce >> getTMTree)
          case origElem of
            -- If the element is a comprehension and the result of the comprehension is a list, per the spec, we insert
            -- the elements of the list into the list at the current index.
            IsTGenOp (MutOp (Compreh cph))
              | cph.isListCompreh
              , Just rList <- rtrList r ->
                  return $ acc ++ lstSubs rList
            _ -> return $ acc ++ [r]
      )
      []
      (zip [0 ..] (lstSubs l))
  putTMTree $ mkListTree r

-- | Closes a struct when the tree has struct.
resolveCloseFunc :: (ResolveMonad r s m) => [Tree] -> TrCur -> m (Maybe Tree)
resolveCloseFunc args _
  | length args /= 1 = throwFatal $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      let arg = head args
      return $ Just $ closeTree arg

-- | Close a struct when the tree has struct.
closeTree :: Tree -> Tree
closeTree a =
  case treeNode a of
    TNStruct s -> setTN a (TNStruct $ s{stcClosed = True})
    TNDisj dj ->
      let
        ds = map closeTree (dsjDisjuncts dj)
       in
        setTN a $ TNDisj (dj{dsjDisjuncts = ds})
    -- TODO: Mutable should be closed.
    -- TNMutable _ -> throwFatal "TODO"
    _ -> mkBottomTree $ printf "cannot use %s as struct in argument 1 to close" (show a)

{- | Discover conjuncts from a **unreduced** tree node that contains conjuncts as its children.

It reduces every conjunct node it finds.

It should not be directly called.
-}
discoverPConjs :: (ReduceMonad r s m) => m [Maybe TrCur]
discoverPConjs = debugSpanAdaptTM "discoverPConjs" adapt $ do
  conjTC <- getTMCursor
  case tcFocus conjTC of
    IsTGenOp (MutOp (UOp _)) -> discoverPConjsFromUnifyOp
    _ -> do
      reduce
      vM <- rtrNonMut <$> getTMTree
      return [maybe Nothing (Just . (`setTCFocus` conjTC)) vM]
 where
  -- adapt xs = toJSON (map (fmap (oneLinerStringOfTree . tcFocus)) xs)
  adapt xs = toJSON ()

{- | Discover pending conjuncts from a unify operation.

It recursively discovers conjuncts from the unify operation and its arguments.

It reduces any mutable argument it finds.
-}
discoverPConjsFromUnifyOp :: (ReduceMonad r s m) => m [Maybe TrCur]
discoverPConjsFromUnifyOp = do
  tc <- getTMCursor
  case tc of
    TCFocus (IsTGenOp mut@(MutOp (UOp _))) -> do
      -- A conjunct can be incomplete. For example, 1 & (x + 1) resulting an atom constraint.
      foldM
        ( \acc (i, _) -> do
            subs <- inSubTM (MutArgTASeg i) discoverPConjs
            return (acc ++ subs)
        )
        []
        (zip [0 ..] (toList $ getMutArgs mut))
    _ -> throwFatal "discoverPConjsFromUnifyOp: not a mutable unify operation"

data ResolvedPConjuncts
  = -- | AtomCnstrConj is created if one of the pending conjuncts is an atom and the runtime parameter
    -- 'createCnstr' is True.
    AtomCnstrConj AtomCnstr
  | ResolvedConjuncts [TrCur]
  | IncompleteConjuncts
  deriving (Show)

{- | Resolve pending conjuncts.

The tree cursor must be the unify operation node.
-}
resolvePendingConjuncts :: (ResolveMonad r s m) => [Maybe TrCur] -> TrCur -> m ResolvedPConjuncts
resolvePendingConjuncts pconjs tc = do
  cc <- asks (createCnstr . getReduceParams)

  let cnstr = tcFocus tc
      (readies, foundIncmpl, atomCnstrM) =
        foldr
          ( \pconj (acc, accFoundIncmpl, accACM) -> case tcFocus <$> pconj of
              Nothing -> (acc, True, accACM)
              Just (IsAtom a)
                | cc ->
                    ( fromJust pconj : acc
                    , accFoundIncmpl
                    , if isJust accACM then accACM else Just $ AtomCnstr a cnstr
                    )
              Just _ -> (fromJust pconj : acc, accFoundIncmpl, accACM)
          )
          ([], False, Nothing)
          pconjs
      r =
        if not foundIncmpl
          then ResolvedConjuncts readies
          else maybe IncompleteConjuncts AtomCnstrConj atomCnstrM
  debugInstantRM "resolvePendingConjuncts" (printf "resolved: %s" (show r)) tc
  return r

resolveDisjOp :: (ResolveMonad r s m) => TrCur -> m (Maybe Tree)
resolveDisjOp disjOpTC@(TCFocus (IsTGenOp (MutOp (DisjOp disjOp)))) =
  debugSpanMTreeRM "resolveDisjOp" disjOpTC $ do
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
normalizeDisj :: (ResolveMonad r s m) => (Tree -> Bool) -> Disj -> TrCur -> m Tree
normalizeDisj discardDisjunct d tc = debugSpanTreeRM "normalizeDisj" tc $ do
  debugInstantRM "normalizeDisj" (printf "before: %s" (show $ mkDisjTree d)) tc
  flattened <- flattenDisjunction discardDisjunct d
  final <- modifyDisjuncts discardDisjunct flattened tc
  debugInstantRM
    "normalizeDisj"
    ( printf
        "flattened: %s, flattened disjuncts: %s, final: %s"
        (show $ mkDisjTree flattened)
        (show $ dsjDisjuncts flattened)
        (show final.dsjDisjuncts)
    )
    tc
  if
    | null final.dsjDisjuncts ->
        let
          noVals = filter (\case IsNoVal -> True; _ -> False) flattened.dsjDisjuncts
          bottoms = filter (isJust . rtrBottom) flattened.dsjDisjuncts
         in
          if
            | length noVals == length flattened.dsjDisjuncts -> return $ mkNewTree TNNoVal
            | not (null bottoms) -> return $ head bottoms
            | otherwise ->
                throwFatal $ printf "normalizeDisj: no disjuncts left in %s" (show flattened.dsjDisjuncts)
    -- When there is only one disjunct and the disjunct is not default, the disjunction is converted to the disjunct.
    | length final.dsjDisjuncts == 1 && null (dsjDefIndexes final) -> return $ head final.dsjDisjuncts
    | otherwise -> return $ mkDisjTree final

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
flattenDisjunction :: (ResolveMonad r s m) => (Tree -> Bool) -> Disj -> m Disj
flattenDisjunction discardDisjunct (Disj{dsjDefIndexes = idxes, dsjDisjuncts = disjuncts}) = do
  debugInstantOpRM
    "flattenDisjunction"
    (printf "before disjuncts: %s, defIdxes: %s" (show $ map treeToRepString disjuncts) (show idxes))
    emptyTreeAddr

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
      emptyTreeAddr
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
modifyDisjuncts :: (ResolveMonad r s m) => (Tree -> Bool) -> Disj -> TrCur -> m Disj
modifyDisjuncts discardDisjunct idisj@(Disj{dsjDefIndexes = dfIdxes, dsjDisjuncts = disjuncts}) tc =
  debugSpanArgsAdaptRM
    "modifyDisjuncts"
    (show $ mkDisjTree idisj)
    (const Nothing)
    -- (\x -> toJSON $ oneLinerStringOfTree $ mkDisjTree x)
    (\x -> toJSON ())
    tc
    $ do
      (newIndexes, newDisjs) <- foldM go ([], []) (zip [0 ..] disjuncts)
      return $ emptyDisj{dsjDefIndexes = newIndexes, dsjDisjuncts = newDisjs}
 where
  defValues = map (disjuncts !!) dfIdxes
  origDefIdxesSet = Set.fromList dfIdxes

  go (accIs, accXs) (idx, v) = do
    let canCancelRC = isJust $ addrIsSufRef (tcAddr tc)
    case v of
      IsRefCycle | canCancelRC -> return (accIs, accXs)
      IsUnifiedWithRC True | canCancelRC -> return $ updateDisjuncts (accIs, accXs) (idx, v{isUnifiedWithRC = False})
      IsEmbedVal ev -> return $ updateDisjuncts (accIs, accXs) (idx, ev)
      _ -> return $ updateDisjuncts (accIs, accXs) (idx, v)

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
procMarkedTerms :: (ResolveMonad r s m) => [DisjTerm] -> m [Tree]
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
                    setTN
                      val
                      ( TNDisj $
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
                      : accDisjuncts
                -- Apply Rule M0 and M3
                | hasMarked ->
                    maybe
                      val
                      (\d -> setTN val $ TNDisj $ d{dsjDefIndexes = []})
                      (rtrDisj val)
                      : accDisjuncts
                | otherwise -> val : accDisjuncts
      )
      []
      terms

reduceCompreh :: (ReduceMonad r s m) => Comprehension -> m ()
reduceCompreh cph = debugSpanTM "reduceCompreh" $ do
  r <- comprehend 0 cph.args (IterCtx 0 Map.empty (Right []))
  res <- case r.res of
    Left t -> return t
    Right vs ->
      if cph.isListCompreh
        then return $ mkListTree vs
        else case vs of
          [] -> return $ mkStructTree emptyStruct
          [x] -> return x
          _ -> do
            let mutT = mkMutableTree $ mkUnifyOp vs
            inTempTM mutT $ reduce >> getTMTree

  -- The result could be a struct, list or noval. But we should get rid of the mutable if there is any.
  modifyTMTN (treeNode res)
  reducePureTN

data IterCtx = IterCtx
  { iterCnt :: Int
  -- ^ The count of the iterations.
  , bindings :: Map.Map TextIndex Tree
  , res :: Either Tree [Tree]
  -- ^ It contains a list of resulted structs that are generated by each iteration.
  }
  deriving (Show)

instance ToJSON IterCtx where
  toJSON IterCtx{iterCnt, bindings, res} =
    object
      [ "iterCnt" .= iterCnt
      -- , "bindings" .= Map.map oneLinerStringOfTree bindings
      -- , "res" .= case res of
      --     Left t -> object ["error" .= oneLinerStringOfTree t]
      --     Right ts -> object ["values" .= map oneLinerStringOfTree ts]
      ]

{- | Iterate through the comprehension clauses.

The iteration is done in a depth-first manner. If all clauses are processed, it creates a new struct with the
bindings and adds the struct to the result list.
-}
comprehend :: (ReduceMonad r s m) => Int -> Seq.Seq ComprehArg -> IterCtx -> m IterCtx
comprehend i args iterCtx
  -- The leaf case where the iteration is done.
  | i >= length args - 1 = debugSpanArgsAdaptTM
      (printf "comprehend itercnt:%s" (show iterCtx.iterCnt))
      (printf "iterctx: %s" (show iterCtx))
      toJSON
      $ case iterCtx.res of
        Left err ->
          throwFatal $
            printf "should not reach the leaf node if the result is already an error: %s" (treeToRepString err)
        Right vs -> do
          -- Reduce the template struct so that references in the struct can be resolved.
          r <-
            inSubTM
              (MutArgTASeg i)
              ( do
                  attachBindings iterCtx.bindings
                  createUnique
              )
          -- Make the reduced struct of this iteration immutable because it would simplify later unification of
          -- iteration results, mostly because of removal of the embedded value.
          r2 <- inTempTM r $ reduceToNonMut >> makeTreeImmutable <$> getTMTree
          return $ iterCtx{res = Right (vs ++ [r2]), iterCnt = iterCtx.iterCnt + 1}
  | otherwise = reduceClause i args iterCtx

createUnique :: (ReduceMonad r s m) => m Tree
createUnique = do
  t <- getTMTree
  case t of
    IsStruct struct
      | TGenImmutable <- t.valGenEnv -> do
          -- The original let bindings in the struct should take the precedence over the iteration bindings.
          newStruct <- mkUnique struct
          return $ setTN t (TNStruct newStruct)
    -- The template struct can have embedded values.
    _
      | TGenOp mut <- t.valGenEnv
      , let args = getMutArgs mut
      , a Seq.:<| _ <- args
      , IsStruct tmplStruct <- a -> do
          newStruct <- mkUnique tmplStruct
          inSubTM (MutArgTASeg 0) $ modifyTMTN $ TNStruct newStruct
          forM_ [1 .. length args - 1] $ \i ->
            inSubTM (MutArgTASeg i) $ modifyTMTree $ \x -> x{embType = ETEmbedded newStruct.stcID}
          getTMTree
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
reduceClause :: (ReduceMonad r s m) => Int -> Seq.Seq ComprehArg -> IterCtx -> m IterCtx
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
        _ -> return $ iterCtx{res = Left $ mkBottomTree $ printf "%s is not a boolean" (showTreeSymbol t)}
  ComprehArgFor k vM _ -> do
    t <- reduceClauseWithBindings i iterCtx.bindings
    if
      | IsNoVal <- t -> return iterCtx
      | IsBottom _ <- t -> return $ iterCtx{res = Left t}
      -- TODO: only iterate optional fields
      | IsStruct struct <- t ->
          foldM
            ( \acc (labelIdx, field) -> do
                label <- textIndexToText labelIdx
                comprehend
                  (i + 1)
                  args
                  ( acc
                      { bindings =
                          Map.union
                            ( Map.fromList $
                                maybe
                                  [(k, ssfValue field)]
                                  (\v -> [(k, mkAtomTree (String label)), (v, ssfValue field)])
                                  vM
                            )
                            acc.bindings
                      }
                  )
            )
            iterCtx
            (Map.toList $ stcFields struct)
      | Just (List{lstSubs = list}) <- rtrList t ->
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
                                  (\v -> [(k, mkAtomTree (Int idx)), (v, element)])
                                  vM
                            )
                            acc.bindings
                      }
                  )
            )
            iterCtx
            (zip [0 ..] list)
      | otherwise ->
          return $
            iterCtx
              { res = Left $ mkBottomTree $ printf "%s is not iterable" (showTreeSymbol t)
              }

-- | Embed a value to a new block and return a new tree cursor that points to the embedded value.
reduceClauseWithBindings :: (ReduceMonad r s m) => Int -> Map.Map TextIndex Tree -> m Tree
reduceClauseWithBindings i bindings = do
  tc <- getTMCursor
  case tc of
    TCFocus (IsTGenOp mut@(MutOp (Compreh cph))) -> do
      let newTC = modifyTCFocus (\t -> t{valGenEnv = TGenOp $ setMutOp (Compreh cph{iterBindings = bindings}) mut}) tc
      putTMCursor newTC
      inSubTM (MutArgTASeg i) (reduce >> getTMTree)
    _ -> throwFatal "reduceClauseWithBindings can only be used with a mutable comprehension"

-- | Insert bindings into the template struct.
attachBindings :: (ReduceMonad r s m) => Map.Map TextIndex Tree -> m ()
attachBindings bindings = do
  t <- getTMTree
  case t of
    IsStruct struct
      | TGenImmutable <- t.valGenEnv -> do
          -- The original let bindings in the struct should take the precedence over the iteration bindings.
          let
            cleanBindings = Map.filter (not . isIterVar) struct.stcBindings
            newBindings =
              Map.union
                cleanBindings
                (Map.mapKeys RefIdent $ Map.map (\x -> Binding x True) bindings)
          debugInstantTM "attachBindings" (printf "new bindings: %s" (show newBindings))
          modifyTMTN $ TNStruct $ struct{stcBindings = newBindings}
    -- The template struct can have embedded values.
    _
      | TGenOp mut <- t.valGenEnv
      , let args = getMutArgs mut
      , a Seq.:<| _ <- args
      , IsStruct tmplStruct <- a -> do
          -- The original let bindings in the struct should take the precedence over the iteration bindings.
          let
            cleanBindings = Map.filter (not . isIterVar) tmplStruct.stcBindings
            newBindings =
              Map.union
                cleanBindings
                (Map.mapKeys RefIdent $ Map.map (\x -> Binding x True) bindings)
          debugInstantTM "attachBindings" (printf "new bindings: %s" (show newBindings))
          inSubTM (MutArgTASeg 0) $ modifyTMTN $ TNStruct $ tmplStruct{stcBindings = newBindings}
    _ -> throwFatal "attachBindings can only be used with a struct template"

resolveInterpolation :: (ResolveMonad r s m) => Interpolation -> [Tree] -> m (Maybe Tree)
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
                      mkBottomTree $
                        printf "can not use struct in interpolation: %s" (showTreeSymbol r)
              | Just _ <- rtrList r ->
                  return $
                    Left $
                      mkBottomTree $
                        printf "can not use list in interpolation: %s" (showTreeSymbol r)
              | otherwise -> throwFatal $ printf "unsupported interpolation expression: %s" (showTreeSymbol r)
          IplSegStr s -> return $ (`T.append` s) <$> accRes
      )
      (Right T.empty)
      (itpSegs l)
  case r of
    Left err -> return $ Just err
    Right res -> return $ Just $ mkAtomTree (String res)
