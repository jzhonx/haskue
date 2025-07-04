{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Nodes where

import qualified Common
import Control.Monad (foldM, unless, void, when)
import Control.Monad.Reader (local)
import Cursor
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isJust, isNothing, listToMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import Path
import Reduce.RMonad (
  ReduceMonad,
  addRMUnreferredLet,
  debugInstantRM,
  debugSpanArgsRM,
  debugSpanRM,
  evalExprRM,
  getRMUnreferredLets,
  increaseRMGlobalVers,
 )
import Reduce.RefSys (searchTCIdentInPar)
import {-# SOURCE #-} Reduce.Root (reduce, reduceToNonMut)
import Reduce.UnifyOp (unifyTCs)
import Text.Printf (printf)
import Value

-- ###
-- Reduce tree nodes
-- ###

{- | Reduce the struct.

Most of the heavy work is done in the propUpStructPost function.
-}
reduceBlock :: forall s r m. (ReduceMonad s r m) => TrCur -> m Tree
reduceBlock _tc = debugSpanRM "reduceBlock" Just _tc $ do
  mergedM <- unifyTCs [_tc] _tc
  case mergedM of
    -- some of the embedded values are not ready.
    Nothing -> return $ tcFocus _tc
    Just merged -> do
      let tc = merged `setTCFocus` _tc
      utc <- case treeNode (tcFocus tc) of
        TNBlock _ -> reduceStruct tc
        -- The focus has become a mutable.
        TNMutable _ -> do
          r <- reduce tc
          return $ r `setTCFocus` tc
        _ -> return tc

      tcFocus <$> handleBlockReducedRes _tc utc

{- | Reduce the struct

Embedded values have been applied to the fields.
-}
reduceStruct :: (ReduceMonad s r m) => TrCur -> m TrCur
reduceStruct stc = do
  whenBlock
    ( \(block, s, tc) -> do
        -- Close the struct if the tree is closed.
        let
          focus = tcFocus tc
          isClosed = treeRecurClosed focus
        return $
          if isClosed
            -- Use modifyTMTN instead of mkNewTree because tree attributes need to be preserved, such as
            -- treeRecurClosed.
            then
              setTN
                focus
                (TNBlock $ modifyBlockStruct (const s{stcClosed = True}) block)
                `setTCFocus` tc
            else tc
    )
    stc
    >>= whenBlock (\(_, s, tc) -> foldM (flip validateLetName) tc (Map.keys $ stcLets s))
    -- reduce the labels of the dynamic fields first. If the dynfields become actual fields, later they will be
    -- reduced.
    >>= whenBlock
      ( \(_, s, tc) ->
          foldM
            ( \acc (i, _) -> do
                -- Inserting reduced dynamic field element into the struct is handled by propUpStructPost.
                utc <- inStructSub (DynFieldTASeg i 0) reduce acc
                -- we will reduce every fields, so no need to return affected labels.
                fst <$> handleStructMutObjChange (DynFieldTASeg i 0) utc
            )
            tc
            (IntMap.toList $ stcDynFields s)
      )
    >>= whenBlock
      ( \(_, s, tc) ->
          foldM
            ( \acc (i, _) -> do
                -- pattern value should never be reduced because the references inside the pattern value should only
                -- be resolved in the unification node of the static field.
                -- See unify for more details.
                -- reduced constraint will constrain fields, which is done in the propUpStructPost.
                utc <- inStructSub (PatternTASeg i 0) reduce acc
                fst <$> handleStructMutObjChange (PatternTASeg i 0) utc
            )
            tc
            (IntMap.toList $ stcCnstrs s)
      )
    -- Add the let bindings to the unreferred let bindings.
    >>= whenBlock
      ( \(_, s, tc) -> do
          mapM_
            ( \x ->
                addRMUnreferredLet (appendSeg (tcCanAddr tc) (StructTASeg (LetTASeg (TE.encodeUtf8 x))))
            )
            (Map.keys $ stcLets s)

          unrefLets <- getRMUnreferredLets
          debugInstantRM "reduceBlock" (printf "unrefLets: %s" (show unrefLets)) tc

          return tc
      )
    -- Reduce all fields.
    >>= whenBlock
      (\(_, s, tc) -> foldM (flip reduceStructField) tc (Map.keys . stcFields $ s))
    >>= whenBlock
      ( \(block, s, tc) -> do
          -- According to the spec,
          -- A value is concrete if it is either an atom, or a struct whose field values are all concrete, recursively.
          let isStructConcrete =
                foldl
                  (\acc field -> acc && isJust (rtrConcrete $ ssfValue field))
                  True
                  (Map.elems . stcFields $ s)
                  -- dynamic fields must have concrete labels.
                  && foldl
                    (\acc field -> acc && isJust (rtrConcrete $ dsfLabel field))
                    True
                    (IntMap.elems . stcDynFields $ s)
              newStruct = s{stcIsConcrete = isStructConcrete}
              newBlock = block{blkStruct = newStruct}
          return $ setTCFocusTN (TNBlock newBlock) tc
      )

handleBlockReducedRes :: (ReduceMonad s r m) => TrCur -> TrCur -> m TrCur
handleBlockReducedRes orig reduced = do
  let focus = tcFocus reduced
  case treeNode focus of
    TNBottom _ -> return reduced
    TNBlock block ->
      mustBlock
        orig
        ( \(origBlock, _) ->
            -- Add back the embeds which are removed in the unify step.
            return $ setTCFocusTN (TNBlock (block{blkEmbeds = blkEmbeds origBlock})) reduced
        )
    _ ->
      mustBlock
        orig
        ( \(origBlock, _) ->
            -- If the focus is not a struct, it means the struct has been reduced to an embedded value.
            return $ setTCFocusTN (TNBlock (origBlock{blkNonStructValue = Just focus})) reduced
        )

mustBlock :: (ReduceMonad r s m) => TrCur -> ((Block, TrCur) -> m a) -> m a
mustBlock tc f =
  let t = tcFocus tc
   in case treeNode t of
        TNBlock es -> f (es, tc)
        _ -> throwErrSt $ printf "%s is not a struct" (show t)

whenBlock ::
  (ReduceMonad s r m) =>
  ((Block, Struct, TrCur) -> m TrCur) ->
  TrCur ->
  m TrCur
whenBlock f tc = do
  let t = tcFocus tc
  case treeNode t of
    TNBlock block@(Block{blkStruct = struct}) -> f (block, struct, tc)
    -- The struct might have been turned to another type due to embedding.
    _ -> return tc

inStructSub ::
  (ReduceMonad s r m) =>
  StructTASeg ->
  (TrCur -> m Tree) ->
  TrCur ->
  m TrCur
inStructSub sseg f tc = do
  let seg = StructTASeg sseg
  subTC <- goDownTCSegMust seg tc
  sub <- f subTC
  let addr = tcCanAddr subTC
  case sub of
    IsBottom _ | isInDisj addr -> return (sub `setTCFocus` tc)
    _ -> propUpTC (sub `setTCFocus` subTC)

validateLetName :: (ReduceMonad s r m) => T.Text -> TrCur -> m TrCur
validateLetName name =
  whenBlock
    ( \(_, _, tc) -> do
        -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make sure
        -- in the parent scope that there is no field with the same name.
        parResM <- searchTCIdentInPar name tc
        return $ case parResM of
          -- If the let binding with the name is found in the scope.
          Just (_, True) -> lbRedeclErr name `setTCFocus` tc
          -- If the field with the same name is found in the scope.
          Just (_, False) -> aliasErr name `setTCFocus` tc
          _ -> tc
    )

aliasErr :: T.Text -> Tree
aliasErr name = mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name

lbRedeclErr :: T.Text -> Tree
lbRedeclErr name = mkBottomTree $ printf "%s redeclared in same scope" name

reduceStructField :: (ReduceMonad s r m) => T.Text -> TrCur -> m TrCur
reduceStructField name stc = do
  whenBlock
    ( \(_, _, tc) -> do
        -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make
        -- sure in the parent scope that there is no field with the same name.
        parResM <- searchTCIdentInPar name tc

        case parResM of
          -- If the let binding with the name is found in the scope.
          Just (_, True) -> return $ aliasErr name `setTCFocus` tc
          _ -> return tc
    )
    stc
    >>= whenBlock
      (\(_, _, tc) -> inStructSub (StringTASeg (TE.encodeUtf8 name)) reduce tc)

{- | Handle the post process of the mutable object change in the struct.

It increases the global version. Later when we reduce the fields of the updated struct, the fields will be assigned with
the new global version. If a field "a" references another field "b" in the same struct, but the evaluation order is
["a", "b"], after reducing the "a" field, the "a"'s refVers value will still be the old version of the "b" field. Later
once the "b" is reduced, it will trigger the re-reduction of the "a" field.

The focus of the tree must be a struct.
-}
handleStructMutObjChange ::
  (ReduceMonad s r m) => StructTASeg -> TrCur -> m (TrCur, [T.Text])
handleStructMutObjChange seg stc@TrCur{tcFocus = focus}
  | DynFieldTASeg i _ <- seg
  , TNBlock block@(Block{blkStruct = _struct}) <- treeNode focus = debugSpanRM
      (printf "handleStructMutObjChange, seg: %s" (show seg))
      (Just . tcFocus . fst)
      stc
      $ do
        void increaseRMGlobalVers
        (remAffStruct, remAffLabels) <- removeAppliedObject i _struct stc
        let
          dsf = stcDynFields _struct IntMap.! i
          rE = dynFieldToStatic remAffStruct dsf
          allCnstrs = IntMap.elems $ stcCnstrs remAffStruct

        debugInstantRM "handleStructMutObjChange" (printf "dsf: %s, rE: %s" (show dsf) (show rE)) stc

        either
          (\err -> return (setTCFocusTN (treeNode err) stc, []))
          ( \labelFieldM -> do
              -- Constrain the dynamic field with all existing constraints.
              (addAffFields, addAffLabels) <-
                maybe
                  (return ([], []))
                  ( \(name, field) -> do
                      newField <- constrainFieldWithCnstrs name field allCnstrs stc
                      return
                        ( [(name, newField)]
                        , if not (null $ ssfObjects newField) then [name] else []
                        )
                  )
                  labelFieldM

              let
                -- TODO: dedup
                affectedLabels = remAffLabels ++ addAffLabels
                newSTC =
                  setTCFocusTN
                    ( TNBlock $
                        block
                          { blkStruct = updateStructWithFields addAffFields remAffStruct
                          }
                    )
                    stc

              debugInstantRM
                "handleStructMutObjChange"
                (printf "-: %s, +: %s, all: %s" (show remAffLabels) (show addAffFields) (show affectedLabels))
                stc

              return (newSTC, affectedLabels)
          )
          rE
  | PatternTASeg i _ <- seg
  , TNBlock (Block{blkStruct = _struct}) <- treeNode focus = debugSpanRM
      (printf "handleStructMutObjChange, seg: %s" (show seg))
      (Just . tcFocus . fst)
      stc
      $ do
        void increaseRMGlobalVers
        -- Constrain all fields with the new constraint if it exists.
        let cnstr = stcCnstrs _struct IntMap.! i
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

        (remAffStruct, remAffLabels) <- removeAppliedObject i _struct stc
        (newStruct, addAffLabels) <- applyMoreCnstr cnstr remAffStruct stc
        let
          affectedLabels = remAffLabels ++ addAffLabels
          nstc = mkStructTree newStruct `setTCFocus` stc
        unless (null affectedLabels) $
          debugInstantRM
            "handleStructMutObjChange"
            ( printf
                "-: %s, +: %s, new struct: %s"
                (show remAffLabels)
                (show addAffLabels)
                (show $ mkStructTree newStruct)
            )
            nstc

        return (nstc, affectedLabels)
  | EmbedTASeg i <- seg
  , TNBlock block@(Block{blkStruct = _struct}) <- treeNode focus = debugSpanRM
      (printf "handleStructMutObjChange, seg: %s" (show seg))
      (Just . tcFocus . fst)
      stc
      $ do
        void increaseRMGlobalVers
        let embed = blkEmbeds block IntMap.! i
        rmdEmbedStruct <- case embValue embed of
          IsBlock (Block{blkStruct = embedStruct}) -> do
            let rmIDs = i : (IntMap.keys (stcCnstrs embedStruct) ++ IntMap.keys (stcDynFields embedStruct))
            (allRmStruct, _) <-
              foldM
                ( \(accStruct, accLabels) idx -> do
                    (s, affLabels) <- removeAppliedObject idx accStruct stc
                    return (s, affLabels ++ accLabels)
                )
                (_struct, [])
                rmIDs

            return allRmStruct
          -- If the embedded value is not a struct, which could be a comprehension, then we only need to remove the
          -- object.
          _ -> fst <$> removeAppliedObject i _struct stc

        let structTC = setTCFocusTN (TNBlock (block{blkStruct = rmdEmbedStruct})) stc

        debugInstantRM "handleStructMutObjChange" (printf "new struct: %s" (show $ tcFocus structTC)) structTC

        mergedM <- unifyTCs [structTC] structTC
        case mergedM of
          Nothing -> return (stc, [])
          Just merged -> do
            utc <- handleBlockReducedRes structTC (merged `setTCFocus` structTC)
            return
              ( utc
              , case treeNode (tcFocus utc) of
                  -- Currently we have to re-reduce all fields because unify does not return the reduced fields.
                  TNBlock resblock
                    | isNothing (blkNonStructValue resblock) -> Map.keys $ stcFields . blkStruct $ resblock
                  _ -> []
              )
  | otherwise = return (stc, [])

getLabelFieldPairs :: Struct -> [(T.Text, Field)]
getLabelFieldPairs struct = Map.toList $ stcFields struct

{- | Convert a dynamic field to a static field.

It returns a pair which contains reduced string and the newly created/updated field.
-}
dynFieldToStatic ::
  Struct ->
  DynamicField ->
  Either Tree (Maybe (T.Text, Field))
dynFieldToStatic struct df = case treeNode label of
  TNBottom _ -> Left label
  TNMutable mut
    -- TODO: atom can become bottom or not found.
    | Just (TNAtom (String s)) <- treeNode <$> getMutVal mut -> mkField s
    -- Incomplete field label, no change is made. If the mutable was a reference with string value, then it would
    -- have been reduced to a string.
    | otherwise -> return Nothing
  TNAtom (String s) -> mkField s
  _ -> Left (mkBottomTree "label can only be a string")
 where
  label = dsfLabel df
  mkField s =
    let
      unifier l r = mkMutableTree $ mkUnifyOp [l, r]
      newSF = dynToField df (lookupStructField s struct) unifier
     in
      return (Just (s, newSF))

{- | Apply pattern constraints ([pattern]: constraint) to the static field.

Returns the new field. If the field is not matched with the pattern, it returns the original field.
-}
constrainFieldWithCnstrs ::
  (ReduceMonad s r m) => T.Text -> Field -> [StructCnstr] -> TrCur -> m Field
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
bindFieldWithCnstr ::
  (ReduceMonad s r m) =>
  T.Text ->
  Field ->
  StructCnstr ->
  TrCur ->
  m (Field, Bool)
bindFieldWithCnstr name field cnstr tc = do
  let selPattern = scsPattern cnstr

  matched <- patMatchLabel selPattern name tc

  let
    fval = ssfValue field
    op = mkMutableTree $ mkUnifyOp [fval, scsValue cnstr]
    -- TODO: comment on why mkCnstredValTree is used.
    -- op = mkMutableTree $ mkUnifyOp [fval, mkCnstredValTree (scsValue cnstr) Nothing]
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
  [(T.Text, Field)] ->
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
filterMatchedNames :: (ReduceMonad s r m) => StructCnstr -> [T.Text] -> TrCur -> m [T.Text]
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
removeAppliedObject ::
  (ReduceMonad s r m) =>
  Int ->
  Struct ->
  TrCur ->
  m (Struct, [T.Text])
removeAppliedObject objID struct tc = debugSpanRM "removeAppliedObject" (Just . mkStructTree . fst) tc $ do
  (remAffFields, removedLabels) <-
    foldM
      ( \(accUpdated, accRemoved) (name, field) -> do
          let
            newObjectIDs = Set.delete objID (ssfObjects field)
            newCnstrs = IntMap.filterWithKey (\k _ -> k `Set.member` newObjectIDs) allCnstrs
            newDyns = IntMap.filterWithKey (\k _ -> k `Set.member` newObjectIDs) allDyns
            baseRawM = ssfBaseRaw field
          debugInstantRM
            "removeAppliedObject"
            ( printf
                "field: %s, objID: %s, newObjectIDs: %s, raw: %s"
                name
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
                    startField = field{ssfValue = dsfValue $ head dyns}
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
  let res = removeStructFields removedLabels $ updateStructWithFields remAffFields struct
  return (res, map fst remAffFields)
 where
  allCnstrs = stcCnstrs struct
  allDyns = stcDynFields struct
  unifier l r = mkMutableTree $ mkUnifyOp [l, r]

  -- Find the fields that are unified with the object
  fieldsUnifiedWithObject :: Int -> [(T.Text, Field)] -> [(T.Text, Field)]
  fieldsUnifiedWithObject j =
    foldr (\(k, field) acc -> if j `elem` ssfObjects field then (k, field) : acc else acc) []

-- | Apply the additional constraint to the fields.
applyMoreCnstr ::
  (ReduceMonad s r m) =>
  StructCnstr ->
  Struct ->
  TrCur ->
  m (Struct, [T.Text])
applyMoreCnstr cnstr struct tc = debugSpanRM "applyMoreCnstr" (const Nothing) tc $ do
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

reduceDisj :: (ReduceMonad s r m) => Disj -> TrCur -> m Tree
reduceDisj d tc = do
  r <-
    tcFocus
      <$> foldM
        (\acc (i, _) -> inSubTC (DisjRegTASeg i) reduce acc)
        tc
        (zip [0 ..] (dsjDisjuncts d))
  case treeNode r of
    TNDisj nd -> do
      let disjuncts = dsjDisjuncts nd
      newDisjT <- normalizeDisj mkDisjTree (d{dsjDisjuncts = disjuncts})
      return $ setTN (tcFocus tc) (treeNode newDisjT)
    _ -> return r

reduceList :: (ReduceMonad s r m) => List -> TrCur -> m Tree
reduceList l tc = do
  r <-
    foldM
      ( \acc (i, origElem) -> do
          let elemTC = mkSubTC (IndexTASeg i) origElem tc
          r <- reduce elemTC
          case origElem of
            -- If the element is a comprehension and the result of the comprehension is a list, per the spec, we insert
            -- the elements of the list into the list at the current index.
            IsMutable (MutOp (Compreh cph))
              | cphIsListCompreh cph
              , Just rList <- rtrList r ->
                  return $ acc ++ lstSubs rList
            _ -> return $ acc ++ [r]
      )
      []
      (zip [0 ..] (lstSubs l))
  return $ mkListTree r

-- | Closes a struct when the tree has struct.
close :: (ReduceMonad s r m) => [Tree] -> TrCur -> m (Maybe Tree)
close args tc
  | length args /= 1 = throwErrSt $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      argTC <- goDownTCSegMust unaryOpTASeg tc
      rM <- reduceToNonMut argTC
      maybe
        -- If the argument is pending, wait for the result.
        (return Nothing)
        (return . Just . closeTree)
        rM

-- | Close a struct when the tree has struct.
closeTree :: Tree -> Tree
closeTree a =
  case treeNode a of
    TNBlock b -> setTN a $ TNBlock $ modifyBlockStruct (\s -> s{stcClosed = True}) b
    TNDisj dj ->
      let
        dft = closeTree <$> dsjDefault dj
        ds = map closeTree (dsjDisjuncts dj)
       in
        setTN a $ TNDisj (dj{dsjDefault = dft, dsjDisjuncts = ds})
    -- TODO: Mutable should be closed.
    -- TNMutable _ -> throwErrSt "TODO"
    _ -> mkBottomTree $ printf "cannot use %s as struct in argument 1 to close" (show a)

reduceDisjOp :: (ReduceMonad s r m) => Bool -> DisjoinOp -> TrCur -> m (Maybe Tree)
reduceDisjOp asConj disjOp disjOpTC = debugSpanRM "reduceDisjOp" id disjOpTC $ do
  let terms = toList $ djoTerms disjOp
  when (length terms < 2) $
    throwErrSt $
      printf "disjunction operation requires at least 2 terms, got %d" (length terms)
  disjuncts <- procMarkedTerms asConj terms disjOpTC
  debugInstantRM "reduceDisjOp" (printf "disjuncts: %s" (show disjuncts)) disjOpTC

  if null disjuncts
    -- If none of the disjuncts are ready, return Nothing.
    then return Nothing
    else do
      let
        d = emptyDisj{dsjDisjuncts = disjuncts}
      r <- normalizeDisj mkDisjTree d
      return $ Just r

{- | Normalize the disjunction.

1. Flatten the disjunction.
2. Deduplicate the disjuncts.
3. Remove the bottom disjuncts.
4. If the disjunct is left with only one element, return the value.
5. If the disjunct is left with no elements, return the first bottom it found.
-}
normalizeDisj :: (Common.Env r s m) => (Disj -> Tree) -> Disj -> m Tree
normalizeDisj toTree d = do
  flattened <- flattenDisjuncts d
  final <- removeUnwantedDisjuncts flattened
  let
    finalDisjs = dsjDisjuncts final
   in
    return
      if
        | null finalDisjs -> head $ filter (\case IsBottom _ -> True; _ -> False) (dsjDisjuncts flattened)
        -- When there is only one disjunct and the disjunct is not default, the disjunction is converted to the disjunct.
        | length finalDisjs == 1 && null (dsjDefIndexes final) -> head finalDisjs
        | otherwise -> toTree $ buildDefVal toTree final

{- | Flatten the disjuncts.

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
flattenDisjuncts :: (Common.Env r s m) => Disj -> m Disj
flattenDisjuncts (Disj{dsjDefIndexes = idxes, dsjDisjuncts = disjuncts}) = do
  -- Use foldl because the new default indexes are based on the length of the accumulated disjuncts.
  (newIndexes, newDisjs) <- foldM flatten ([], []) (zip [0 ..] disjuncts)
  return $ emptyDisj{dsjDefIndexes = newIndexes, dsjDisjuncts = newDisjs}
 where
  origDefIdxesSet = Set.fromList idxes
  -- Suppose we are processing the ith disjunct, and we have accumulated the disjuncts xs.
  -- If the ith disjunct is not a disjunction, then we can just add it to the disjuncts. We also need to add the index
  -- to the default indexes if it belongs to the default disjunction.
  flatten (accIs, accDs) (origIdx, t) =
    case rtrDisj t of
      Just sub -> do
        Disj{dsjDefIndexes = subDefIndexes, dsjDisjuncts = subDisjs} <- flattenDisjuncts sub
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

{- | Remove the duplicate default disjuncts, duplicate disjuncts and bottom disjuncts.

TODO: consider make t an instance of Ord and use Set to remove duplicates.
-}
removeUnwantedDisjuncts :: (Common.Env r s m) => Disj -> m Disj
removeUnwantedDisjuncts (Disj{dsjDefIndexes = dfIdxes, dsjDisjuncts = disjuncts}) = do
  let (newIndexes, newDisjs) = foldl go ([], []) (zip [0 ..] disjuncts)
   in return $ emptyDisj{dsjDefIndexes = newIndexes, dsjDisjuncts = newDisjs}
 where
  defValues = map (disjuncts !!) dfIdxes
  origDefIdxesSet = Set.fromList dfIdxes

  go (accIs, accXs) (idx, x) =
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
        (case x of IsBottom _ -> False; _ -> True)
          && notAddedDisj
          && (not isValEqDef || idx `Set.member` origDefIdxesSet)
      -- The disjunct is default if it is one of the default disjuncts and it is not seen before.
      isDefIndex = keepDisjunct && isValEqDef
     in
      -- Add the current disjunct index to the default indexes if condition is met.
      ( if isDefIndex then accIs ++ [length accXs] else accIs
      , if keepDisjunct then accXs ++ [x] else accXs
      )

{- | Construct a disjunction from the default and the disjuncts.

It filters out incomplete disjuncts.

Some existing rules for marked disjunctions:
M0:  ⟨v⟩    => ⟨v⟩        don't introduce defaults for unmarked term
M1: *⟨v⟩    => ⟨v, v⟩     introduce identical default for marked term
M2: *⟨v, d⟩ => ⟨v, d⟩     keep existing defaults for marked term
M3:  ⟨v, d⟩ => ⟨v⟩        strip existing defaults from unmarked term
-}
procMarkedTerms :: (ReduceMonad s r m) => Bool -> [DisjTerm] -> TrCur -> m [Tree]
procMarkedTerms asConj terms tc = do
  -- disjoin operation allows incompleteness.

  let hasMarked = any dstMarked terms
  reducedTerms <-
    -- If the disjunction is a conjunct, there is no need to reduce the terms.
    if asConj
      then return terms
      else
        -- We need to reduce the terms to know if they are disjunctions or not so that marked terms can be processed.
        foldM
          ( \acc (i, term) -> do
              argTC <- goDownTCSegMust (MutArgTASeg i) tc
              rM <- reduceToNonMut argTC
              case rM of
                Nothing -> return acc -- Incomplete term
                Just r -> return $ acc ++ [term{dstValue = r}]
          )
          []
          (zip [0 ..] terms)
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
      reducedTerms

reduceCompreh :: (ReduceMonad s r m) => Comprehension -> TrCur -> m (Maybe Tree)
reduceCompreh cph tc = debugSpanRM "reduceCompreh" id tc $ do
  r <- reduceClause 0 cph tc (IterCtx 0 (Right []))
  case icRes r of
    Left Nothing -> return Nothing
    Left (Just t) -> return $ Just t
    Right vs ->
      if cphIsListCompreh cph
        then return $ Just $ mkListTree vs
        else return $ Just $ case vs of
          [] -> mkBlockTree emptyBlock
          [x] -> x
          _ -> mkMutableTree $ mkUnifyOp vs

data IterCtx = IterCtx
  { icCnt :: Int
  , icRes :: Either (Maybe Tree) [Tree]
  }
  deriving (Show)

reduceClause ::
  (ReduceMonad s r m) =>
  Int ->
  Comprehension ->
  TrCur ->
  IterCtx ->
  m IterCtx
reduceClause i cph tc iterCtx
  | i == length (cphIterClauses cph) = debugSpanArgsRM
      (printf "reduceIterVal iter:%s" (show $ icCnt iterCtx))
      (printf "bindings: %s" (show $ cphIterBindings cph))
      ( \x -> case icRes x of
          Left v -> v
          Right [] -> Nothing
          Right vs -> Just $ last vs
      )
      tc
      $ do
        let s = cphStruct cph
        r <- newIterStruct (cphIterBindings cph) s tc
        case icRes iterCtx of
          Left _ -> throwErrSt "should not reach the leaf node"
          Right vs -> return $ iterCtx{icRes = Right (vs ++ [r]), icCnt = icCnt iterCtx + 1}
  | otherwise = do
      clauseTC <- goDownTCSegMust (ComprehTASeg $ ComprehIterClauseValTASeg i) tc
      tM <- reduceToNonMut clauseTC
      case tM of
        -- Incomplete clause.
        Nothing -> return $ iterCtx{icRes = Left Nothing}
        Just t
          | TNBottom _ <- treeNode t -> return $ iterCtx{icRes = Left (Just t)}
          | otherwise -> case cphIterClauses cph !! i of
              IterClauseIf{} -> case rtrAtom t of
                Just (Bool True) -> reduceClause (i + 1) cph tc iterCtx
                -- Do not go to next clause if the condition is false.
                Just (Bool False) -> return iterCtx
                _ ->
                  return $
                    iterCtx
                      { icRes = Left $ Just $ mkBottomTree $ printf "%s is not a boolean" (showTreeSymbol t)
                      }
              IterClauseLet letName _ -> do
                let
                  newBind = ComprehIterBinding letName t
                  newCompreh =
                    cph
                      { cphIterBindings = cphIterBindings cph ++ [newBind]
                      }
                  newTC = setTCFocusTN (TNMutable $ withEmptyMutFrame $ Compreh newCompreh) tc
                reduceClause (i + 1) newCompreh newTC iterCtx
              IterClauseFor k vM _ ->
                if
                  -- TODO: only iterate optional fields
                  | IsBlock (Block{blkStruct = struct}) <- t -> do
                      foldM
                        ( \acc (label, field) -> do
                            let
                              newBinds =
                                maybe
                                  [ComprehIterBinding k (ssfValue field)]
                                  ( \v ->
                                      [ ComprehIterBinding k (mkAtomTree (String label))
                                      , ComprehIterBinding v (ssfValue field)
                                      ]
                                  )
                                  vM
                              newCompreh =
                                cph
                                  { cphIterBindings = cphIterBindings cph ++ newBinds
                                  }
                              newTC = setTCFocusTN (TNMutable $ withEmptyMutFrame $ Compreh newCompreh) tc

                            reduceClause (i + 1) newCompreh newTC acc
                        )
                        iterCtx
                        (Map.toList $ stcFields struct)
                  | Just (List{lstSubs = list}) <- rtrList t -> do
                      foldM
                        ( \acc (idx, element) -> do
                            let
                              newBinds =
                                maybe
                                  [ComprehIterBinding k element]
                                  ( \v ->
                                      [ ComprehIterBinding k (mkAtomTree (Int idx))
                                      , ComprehIterBinding v element
                                      ]
                                  )
                                  vM
                              newCompreh =
                                cph
                                  { cphIterBindings = cphIterBindings cph ++ newBinds
                                  }
                              newTC = setTCFocusTN (TNMutable $ withEmptyMutFrame $ Compreh newCompreh) tc

                            reduceClause (i + 1) newCompreh newTC acc
                        )
                        iterCtx
                        (zip [0 ..] list)
                  | otherwise ->
                      return $
                        iterCtx
                          { icRes = Left $ Just $ mkBottomTree $ printf "%s is not iterable" (showTreeSymbol t)
                          }

{- | Create a new struct with the given bindings.

The generated struct will not have comoprehensions, otherwise it will be reduced again, and the bindings will be lost.
-}
newIterStruct ::
  (ReduceMonad s r m) => [ComprehIterBinding] -> Tree -> TrCur -> m Tree
newIterStruct bindings rawStruct _tc =
  debugSpanArgsRM
    "newIterStruct"
    (printf "bindings: %s" (show bindings))
    Just
    _tc
    $ do
      se <- buildASTExpr rawStruct
      structT <- evalExprRM se
      let sTC = mkSubTC (ComprehTASeg ComprehIterValTASeg) structT _tc
      r <- reduce sTC
      ripped <- case treeNode r of
        TNBlock block -> do
          let
            newBlock = block{blkEmbeds = IntMap.filter (not . isComprehension) (blkEmbeds block)}
          return $ setTN r (TNBlock newBlock)
        _ -> return r

      -- replace the refs that are found in the bindings with the binding values. This includes all references in all
      -- possible trees.
      x <-
        traverseTCSimple
          (\x -> subNodes x ++ rawNodes x)
          ( \tc -> do
              let focus = tcFocus tc
              case focus of
                IsRef _ ref
                  -- oirgAddrs should be empty because the reference should not be copied from other places.
                  | Nothing <- refOrigAddrs ref
                  , RefPath var rest <- refArg ref -> do
                      rM <-
                        foldM
                          ( \acc bind ->
                              if
                                | isJust acc -> return acc
                                | cphBindName bind == var
                                , null rest ->
                                    return $ Just (cphBindValue bind)
                                | cphBindName bind == var ->
                                    return $
                                      Just $
                                        setTN
                                          focus
                                          (TNMutable $ withEmptyMutFrame $ Ref $ mkIndexRef (cphBindValue bind Seq.<| rest))
                                | otherwise -> return acc
                          )
                          Nothing
                          (reverse bindings)
                      maybe (return focus) return rM
                _ -> return focus
          )
          (TrCur ripped [])
      return $ tcFocus x
 where
  isComprehension emb = case (embValue emb) of
    IsMutable (MutOp (Compreh _)) -> True
    _ -> False

reduceInterpolation :: (ReduceMonad s r m) => Interpolation -> TrCur -> m (Maybe Tree)
reduceInterpolation l tc = do
  r <-
    foldM
      ( \accRes seg -> case seg of
          IplSegExpr j -> do
            argTC <- goDownTCSegMust (MutArgTASeg j) tc
            r <- reduce argTC
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
              | otherwise -> return undefined
          IplSegStr s -> return $ (`T.append` s) <$> accRes
      )
      (Right T.empty)
      (itpSegs l)
  case r of
    Left err -> return $ Just err
    Right res -> return $ Just $ mkAtomTree (String res)

{- | Check the labels' permission.

The focus of the tree must be a struct.
-}
checkLabelsPerm ::
  (ReduceMonad s r m) =>
  Set.Set T.Text ->
  IntMap.IntMap StructCnstr ->
  Bool ->
  Bool ->
  Set.Set T.Text ->
  TrCur ->
  m TrCur
checkLabelsPerm baseLabels baseCnstrs isBaseClosed isEitherEmbedded labelsSet tc =
  foldM
    ( \acc opLabel ->
        case tcFocus acc of
          IsBottom _ -> return acc
          _ ->
            checkPerm baseLabels baseCnstrs isBaseClosed isEitherEmbedded opLabel acc
              >>= maybe
                (return acc)
                -- If the checkPerm returns a bottom, update the bottom to the struct.
                (\err -> return (err `setTCFocus` acc))
    )
    tc
    labelsSet

checkPerm ::
  (ReduceMonad s r m) =>
  Set.Set T.Text ->
  IntMap.IntMap StructCnstr ->
  Bool ->
  Bool ->
  T.Text ->
  TrCur ->
  m (Maybe Tree)
checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel tc =
  debugSpanArgsRM
    "checkPerm"
    ( printf
        "newLabel: %s, baseLabels: %s, baseAllCnstrs: %s, isBaseClosed: %s, isEitherEmbedded: %s"
        (show newLabel)
        (show $ Set.toList baseLabels)
        (show $ IntMap.toList baseAllCnstrs)
        (show isBaseClosed)
        (show isEitherEmbedded)
    )
    id
    tc
    $ _checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel tc

_checkPerm ::
  (ReduceMonad s r m) =>
  Set.Set T.Text ->
  IntMap.IntMap StructCnstr ->
  Bool ->
  Bool ->
  T.Text ->
  TrCur ->
  m (Maybe Tree)
_checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel tc
  | not isBaseClosed || isEitherEmbedded = return Nothing
  | newLabel `Set.member` baseLabels = return Nothing
  | otherwise = do
      -- A "new" field is allowed if there is at least one pattern that matches the field.
      allowed <-
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

      -- A field is disallowed if no pattern exists or no pattern matches the label.
      if allowed
        then return Nothing
        else return . Just $ mkBottomTree $ printf "%s is not allowed" newLabel

{- | Returns whether the pattern matches the label.

The pattern is expected to be an Atom or a Bounds.
-}
patMatchLabel :: (ReduceMonad s r m) => Tree -> T.Text -> TrCur -> m Bool
patMatchLabel pat name tc = debugSpanRM "patMatchLabel" (const Nothing) tc $ do
  let r = listToMaybe $ catMaybes [rtrAtom pat >>= Just . mkAtomTree, rtrBounds pat >>= Just . mkBoundsTree]
  maybe (return False) match r
 where
  match :: (ReduceMonad s r m) => Tree -> m Bool
  match v = do
    let
      segOp = mkMutableTree $ mkUnifyOp [mkAtomTree $ String name, v]
    -- Since segOps a list of unify nodes that unify the string with the bounds, we can use inDiscardSubTM to
    -- evaluate the unify nodes and get the strings.
    r <-
      -- We should not create constraints in this context because we should not delay the evaluation of the
      -- pattern.
      local
        ( \r ->
            let conf = Common.getConfig r
             in Common.setConfig r conf{Common.cfRuntimeParams = (Common.cfRuntimeParams conf){Common.rpCreateCnstr = False}}
        )
        $ reduce (segOp `setTCFocus` tc)
    -- Filter the strings from the results. Non-string results are ignored meaning the fields do not match the
    -- pattern.
    case rtrAtom r of
      Just (String _) -> return True
      _ -> return False
