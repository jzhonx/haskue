{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Nodes where

import qualified Common
import Control.Monad (foldM, unless, void, when)
import Control.Monad.Reader (asks)
import qualified Cursor
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified Reduce.UnifyOp as UnifyOp
import qualified TCOps
import Text.Printf (printf)
import qualified Value.Tree as VT

-- ###
-- Reduce tree nodes
-- ###

{- | Reduce the struct.

Most of the heavy work is done in the propUpStructPost function.
-}
reduceBlock :: forall s r m. (RM.ReduceMonad s r m) => TCOps.TrCur -> m VT.Tree
reduceBlock _tc = RM.debugSpanRM "reduceBlock" Just _tc $ do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs

  mergedM <- UnifyOp.unifyTCs [_tc] _tc
  case mergedM of
    -- some of the embedded values are not ready.
    Nothing -> return $ Cursor.tcFocus _tc
    Just merged -> do
      let tc = merged `Cursor.setTCFocus` _tc
      utc <- case VT.treeNode (Cursor.tcFocus tc) of
        VT.TNBlock _ -> reduceStruct tc
        -- The focus has become a mutable.
        VT.TNMutable _ -> do
          r <- reduce tc
          return $ r `Cursor.setTCFocus` tc
        _ -> return tc

      Cursor.tcFocus <$> handleBlockReducedRes _tc utc

{- | Reduce the struct

Embedded values have been applied to the fields.
-}
reduceStruct :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m TCOps.TrCur
reduceStruct stc = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs

  whenBlock
    ( \(block, s, tc) -> do
        -- Close the struct if the tree is closed.
        let
          focus = Cursor.tcFocus tc
          isClosed = VT.treeRecurClosed focus
        return $
          if isClosed
            -- Use RM.modifyTMTN instead of VT.mkNewTree because tree attributes need to be preserved, such as
            -- VT.treeRecurClosed.
            then
              VT.setTN
                focus
                (VT.TNBlock $ VT.modifyBlockStruct (const s{VT.stcClosed = True}) block)
                `Cursor.setTCFocus` tc
            else tc
    )
    stc
    >>= whenBlock (\(_, s, tc) -> foldM (flip validateLetName) tc (Map.keys $ VT.stcLets s))
    -- reduce the labels of the dynamic fields first. If the dynfields become actual fields, later they will be
    -- reduced.
    >>= whenBlock
      ( \(_, s, tc) ->
          foldM
            ( \acc (i, _) -> do
                -- Inserting reduced dynamic field element into the struct is handled by propUpStructPost.
                utc <- inStructSub (Path.DynFieldTASeg i 0) reduce acc
                -- we will reduce every fields, so no need to return affected labels.
                fst <$> handleStructMutObjChange (Path.DynFieldTASeg i 0) utc
            )
            tc
            (IntMap.toList $ VT.stcDynFields s)
      )
    >>= whenBlock
      ( \(_, s, tc) ->
          foldM
            ( \acc (i, _) -> do
                -- pattern value should never be reduced because the references inside the pattern value should only
                -- be resolved in the unification node of the static field.
                -- See unify for more details.
                -- reduced constraint will constrain fields, which is done in the propUpStructPost.
                utc <- inStructSub (Path.PatternTASeg i 0) reduce acc
                fst <$> handleStructMutObjChange (Path.PatternTASeg i 0) utc
            )
            tc
            (IntMap.toList $ VT.stcCnstrs s)
      )
    -- Add the let bindings to the unreferred let bindings.
    >>= whenBlock
      ( \(_, s, tc) -> do
          mapM_
            ( \x ->
                RM.addRMUnreferredLet (Path.appendSeg (Cursor.tcCanAddr tc) (Path.StructTASeg (Path.LetTASeg (TE.encodeUtf8 x))))
            )
            (Map.keys $ VT.stcLets s)

          unrefLets <- RM.getRMUnreferredLets
          RM.debugInstantRM "reduceBlock" (printf "unrefLets: %s" (show unrefLets)) tc

          return tc
      )
    -- Reduce all fields.
    >>= whenBlock
      (\(_, s, tc) -> foldM (flip reduceStructField) tc (Map.keys . VT.stcFields $ s))
    >>= whenBlock
      ( \(block, s, tc) -> do
          -- According to the spec,
          -- A value is concrete if it is either an atom, or a struct whose field values are all concrete, recursively.
          let isStructConcrete =
                foldl
                  (\acc field -> acc && isJust (VT.getConcreteValue $ VT.ssfValue field))
                  True
                  (Map.elems . VT.stcFields $ s)
                  -- dynamic fields must have concrete labels.
                  && foldl
                    (\acc field -> acc && isJust (VT.getConcreteValue $ VT.dsfLabel field))
                    True
                    (IntMap.elems . VT.stcDynFields $ s)
              newStruct = s{VT.stcIsConcrete = isStructConcrete}
              newBlock = block{VT.blkStruct = newStruct}
          return $ TCOps.setTCFocusTN (VT.TNBlock newBlock) tc
      )

handleBlockReducedRes :: (RM.ReduceMonad s r m) => TCOps.TrCur -> TCOps.TrCur -> m TCOps.TrCur
handleBlockReducedRes orig reduced = do
  let focus = Cursor.tcFocus reduced
  case VT.treeNode focus of
    VT.TNBottom _ -> return reduced
    VT.TNBlock block ->
      mustBlock
        orig
        ( \(origBlock, _) ->
            -- Add back the embeds which are removed in the unify step.
            return $ TCOps.setTCFocusTN (VT.TNBlock (block{VT.blkEmbeds = VT.blkEmbeds origBlock})) reduced
        )
    _ ->
      mustBlock
        orig
        ( \(origBlock, _) ->
            -- If the focus is not a struct, it means the struct has been reduced to an embedded value.
            return $ TCOps.setTCFocusTN (VT.TNBlock (origBlock{VT.blkNonStructValue = Just focus})) reduced
        )

mustBlock :: (RM.ReduceMonad r s m) => TCOps.TrCur -> ((VT.Block VT.Tree, TCOps.TrCur) -> m a) -> m a
mustBlock tc f =
  let t = Cursor.tcFocus tc
   in case VT.treeNode t of
        VT.TNBlock es -> f (es, tc)
        _ -> throwErrSt $ printf "%s is not a struct" (show t)

whenBlock ::
  (RM.ReduceMonad s r m) =>
  ((VT.Block VT.Tree, VT.Struct VT.Tree, TCOps.TrCur) -> m TCOps.TrCur) ->
  TCOps.TrCur ->
  m TCOps.TrCur
whenBlock f tc = do
  let t = Cursor.tcFocus tc
  case VT.treeNode t of
    VT.TNBlock block@(VT.Block{VT.blkStruct = struct}) -> f (block, struct, tc)
    -- The struct might have been turned to another type due to embedding.
    _ -> return tc

inStructSub ::
  (RM.ReduceMonad s r m) =>
  Path.StructTASeg ->
  (TCOps.TrCur -> m VT.Tree) ->
  TCOps.TrCur ->
  m TCOps.TrCur
inStructSub sseg f tc =
  do
    let seg = Path.StructTASeg sseg
    subTC <- TCOps.goDownTCSegMust seg tc
    sub <- f subTC
    do
      let addr = Cursor.tcCanAddr subTC
      if Common.isTreeBottom sub && Path.isInDisj addr
        then do
          return (sub `Cursor.setTCFocus` tc)
        else TCOps.propUpTC (sub `Cursor.setTCFocus` subTC)

validateLetName :: (RM.ReduceMonad s r m) => T.Text -> TCOps.TrCur -> m TCOps.TrCur
validateLetName name =
  whenBlock
    ( \(_, _, tc) -> do
        -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make sure
        -- in the parent scope that there is no field with the same name.
        parResM <- RefSys.searchTCIdentInPar name tc
        return $ case parResM of
          -- If the let binding with the name is found in the scope.
          Just (_, True) -> lbRedeclErr name `Cursor.setTCFocus` tc
          -- If the field with the same name is found in the scope.
          Just (_, False) -> aliasErr name `Cursor.setTCFocus` tc
          _ -> tc
    )

aliasErr :: T.Text -> VT.Tree
aliasErr name = VT.mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name

lbRedeclErr :: T.Text -> VT.Tree
lbRedeclErr name = VT.mkBottomTree $ printf "%s redeclared in same scope" name

reduceStructField :: (RM.ReduceMonad s r m) => T.Text -> TCOps.TrCur -> m TCOps.TrCur
reduceStructField name stc = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  whenBlock
    ( \(_, _, tc) -> do
        -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make
        -- sure in the parent scope that there is no field with the same name.
        parResM <- RefSys.searchTCIdentInPar name tc

        case parResM of
          -- If the let binding with the name is found in the scope.
          Just (_, True) -> return $ aliasErr name `Cursor.setTCFocus` tc
          _ -> return tc
    )
    stc
    >>= whenBlock
      (\(_, _, tc) -> inStructSub (Path.StringTASeg (TE.encodeUtf8 name)) reduce tc)

{- | Handle the post process of the mutable object change in the struct.

It increases the global version. Later when we reduce the fields of the updated struct, the fields will be assigned with
the new global version. If a field "a" references another field "b" in the same struct, but the evaluation order is
["a", "b"], after reducing the "a" field, the "a"'s refVers value will still be the old version of the "b" field. Later
once the "b" is reduced, it will trigger the re-reduction of the "a" field.

The focus of the tree must be a struct.
-}
handleStructMutObjChange ::
  (RM.ReduceMonad s r m) => Path.StructTASeg -> TCOps.TrCur -> m (TCOps.TrCur, [T.Text])
handleStructMutObjChange seg stc@Cursor.TreeCursor{Cursor.tcFocus = focus}
  | Path.DynFieldTASeg i _ <- seg
  , VT.TNBlock block@(VT.Block{VT.blkStruct = _struct}) <- VT.treeNode focus = RM.debugSpanRM
      (printf "handleStructMutObjChange, seg: %s" (show seg))
      (Just . Cursor.tcFocus . fst)
      stc
      $ do
        void RM.increaseRMGlobalVers
        (remAffStruct, remAffLabels) <- removeAppliedObject i _struct stc
        let
          dsf = VT.stcDynFields _struct IntMap.! i
          rE = dynFieldToStatic remAffStruct dsf
          allCnstrs = IntMap.elems $ VT.stcCnstrs remAffStruct

        RM.debugInstantRM "handleStructMutObjChange" (printf "dsf: %s, rE: %s" (show dsf) (show rE)) stc

        either
          (\err -> return (TCOps.setTCFocusTN (VT.treeNode err) stc, []))
          ( \labelFieldM -> do
              -- Constrain the dynamic field with all existing constraints.
              (addAffFields, addAffLabels) <-
                maybe
                  (return ([], []))
                  ( \(name, field) -> do
                      newField <- constrainFieldWithCnstrs name field allCnstrs stc
                      return
                        ( [(name, newField)]
                        , if not (null $ VT.ssfObjects newField) then [name] else []
                        )
                  )
                  labelFieldM

              let
                -- TODO: dedup
                affectedLabels = remAffLabels ++ addAffLabels
                newSTC =
                  TCOps.setTCFocusTN
                    ( VT.TNBlock $
                        block
                          { VT.blkStruct = VT.updateStructWithFields addAffFields remAffStruct
                          }
                    )
                    stc

              RM.debugInstantRM
                "handleStructMutObjChange"
                (printf "-: %s, +: %s, all: %s" (show remAffLabels) (show addAffFields) (show affectedLabels))
                stc

              return (newSTC, affectedLabels)
          )
          rE
  | Path.PatternTASeg i _ <- seg
  , VT.TNBlock (VT.Block{VT.blkStruct = _struct}) <- VT.treeNode focus = RM.debugSpanRM
      (printf "handleStructMutObjChange, seg: %s" (show seg))
      (Just . Cursor.tcFocus . fst)
      stc
      $ do
        void RM.increaseRMGlobalVers
        -- Constrain all fields with the new constraint if it exists.
        let cnstr = VT.stcCnstrs _struct IntMap.! i
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
          nstc = VT.mkStructTree newStruct `Cursor.setTCFocus` stc
        unless (null affectedLabels) $
          RM.debugInstantRM
            "handleStructMutObjChange"
            ( printf
                "-: %s, +: %s, new struct: %s"
                (show remAffLabels)
                (show addAffLabels)
                (show $ VT.mkStructTree newStruct)
            )
            nstc

        return (nstc, affectedLabels)
  | Path.EmbedTASeg i <- seg
  , VT.TNBlock block@(VT.Block{VT.blkStruct = _struct}) <- VT.treeNode focus = RM.debugSpanRM
      (printf "handleStructMutObjChange, seg: %s" (show seg))
      (Just . Cursor.tcFocus . fst)
      stc
      $ do
        void RM.increaseRMGlobalVers
        let embed = VT.blkEmbeds block IntMap.! i
        rmdEmbedStruct <- case VT.getBlockFromTree (VT.embValue embed) of
          -- If the embedded value is not a struct, which could be a comprehension, then we only need to remove the
          -- object.
          Nothing -> fst <$> removeAppliedObject i _struct stc
          Just (VT.Block{VT.blkStruct = embedStruct}) -> do
            let rmIDs = i : (IntMap.keys (VT.stcCnstrs embedStruct) ++ IntMap.keys (VT.stcDynFields embedStruct))
            (allRmStruct, _) <-
              foldM
                ( \(accStruct, accLabels) idx -> do
                    (s, affLabels) <- removeAppliedObject idx accStruct stc
                    return (s, affLabels ++ accLabels)
                )
                (_struct, [])
                rmIDs

            return allRmStruct

        let structTC = TCOps.setTCFocusTN (VT.TNBlock (block{VT.blkStruct = rmdEmbedStruct})) stc

        RM.debugInstantRM "handleStructMutObjChange" (printf "new struct: %s" (show $ Cursor.tcFocus structTC)) structTC

        mergedM <- UnifyOp.unifyTCs [structTC] structTC
        case mergedM of
          Nothing -> return (stc, [])
          Just merged -> do
            utc <- handleBlockReducedRes structTC (merged `Cursor.setTCFocus` structTC)
            return
              ( utc
              , case VT.treeNode (Cursor.tcFocus utc) of
                  -- Currently we have to re-reduce all fields because unify does not return the reduced fields.
                  VT.TNBlock resblock
                    | isNothing (VT.blkNonStructValue resblock) -> Map.keys $ VT.stcFields . VT.blkStruct $ resblock
                  _ -> []
              )
  | otherwise = return (stc, [])

getLabelFieldPairs :: VT.Struct VT.Tree -> [(T.Text, VT.Field VT.Tree)]
getLabelFieldPairs struct = Map.toList $ VT.stcFields struct

{- | Convert a dynamic field to a static field.

It returns a pair which contains reduced string and the newly created/updated field.
-}
dynFieldToStatic ::
  VT.Struct VT.Tree ->
  VT.DynamicField VT.Tree ->
  Either VT.Tree (Maybe (T.Text, VT.Field VT.Tree))
dynFieldToStatic struct df = case VT.treeNode label of
  VT.TNBottom _ -> Left label
  VT.TNMutable mut
    -- TODO: atom can become bottom or not found.
    | Just (VT.TNAtom (VT.AtomV (VT.String s))) <- VT.treeNode <$> VT.getMutVal mut -> mkField s
    -- Incomplete field label, no change is made. If the mutable was a reference with string value, then it would
    -- have been reduced to a string.
    | otherwise -> return Nothing
  VT.TNAtom (VT.AtomV (VT.String s)) -> mkField s
  _ -> Left (VT.mkBottomTree "label can only be a string")
 where
  label = VT.dsfLabel df
  mkField s =
    let
      unifier l r = VT.mkMutableTree $ VT.mkUnifyOp [l, r]
      newSF = VT.dynToField df (VT.lookupStructField s struct) unifier
     in
      return (Just (s, newSF))

{- | Apply pattern constraints ([pattern]: constraint) to the static field.

Returns the new field. If the field is not matched with the pattern, it returns the original field.
-}
constrainFieldWithCnstrs ::
  (RM.ReduceMonad s r m) => T.Text -> VT.Field VT.Tree -> [VT.StructCnstr VT.Tree] -> TCOps.TrCur -> m (VT.Field VT.Tree)
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
  (RM.ReduceMonad s r m) =>
  T.Text ->
  VT.Field VT.Tree ->
  VT.StructCnstr VT.Tree ->
  TCOps.TrCur ->
  m (VT.Field VT.Tree, Bool)
bindFieldWithCnstr name field cnstr tc = do
  let selPattern = VT.scsPattern cnstr

  matched <- UnifyOp.patMatchLabel selPattern name tc

  let
    fval = VT.ssfValue field
    -- TODO: comment on why mkCnstredValTree is used.
    op = VT.mkMutableTree $ VT.mkUnifyOp [fval, VT.mkCnstredValTree (VT.scsValue cnstr) Nothing]
    newField =
      if matched
        then field{VT.ssfValue = op, VT.ssfObjects = Set.insert (VT.scsID cnstr) (VT.ssfObjects field)}
        else field

  return (newField, matched)

{- | Update the struct with the constrained result.

If the constrained result introduce new fields that are not in the struct, then they are ignored.
-}
updateStructWithCnstredRes ::
  -- | The constrained result is a list of tuples that contains the name of the field, the field.
  [(T.Text, VT.Field VT.Tree)] ->
  VT.Struct VT.Tree ->
  VT.Struct VT.Tree
updateStructWithCnstredRes res struct =
  foldr
    ( \(name, newField) acc ->
        maybe
          acc
          (\_ -> VT.updateStructField name newField acc)
          (VT.lookupStructField name struct)
    )
    struct
    res

-- | Filter the names that are matched with the constraint's pattern.
filterMatchedNames :: (RM.ReduceMonad s r m) => VT.StructCnstr VT.Tree -> [T.Text] -> TCOps.TrCur -> m [T.Text]
filterMatchedNames cnstr labels tc =
  foldM
    ( \acc name -> do
        matched <- UnifyOp.patMatchLabel (VT.scsPattern cnstr) name tc
        return $ if matched then name : acc else acc
    )
    []
    labels

{- | Remove the applied object from the fields.

Returns the updated struct and the list of labels whose fields are affected.

This is done by re-applying existing objects except the one that is removed because unification is a lossy operation.
-}
removeAppliedObject ::
  (RM.ReduceMonad s r m) =>
  Int ->
  VT.Struct VT.Tree ->
  TCOps.TrCur ->
  m (VT.Struct VT.Tree, [T.Text])
removeAppliedObject objID struct tc = RM.debugSpanRM "removeAppliedObject" (Just . VT.mkStructTree . fst) tc $ do
  (remAffFields, removedLabels) <-
    foldM
      ( \(accUpdated, accRemoved) (name, field) -> do
          let
            newObjectIDs = Set.delete objID (VT.ssfObjects field)
            newCnstrs = IntMap.filterWithKey (\k _ -> k `Set.member` newObjectIDs) allCnstrs
            newDyns = IntMap.filterWithKey (\k _ -> k `Set.member` newObjectIDs) allDyns
            baseRawM = VT.ssfBaseRaw field
          RM.debugInstantRM
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
                rawField = field{VT.ssfValue = raw, VT.ssfObjects = Set.empty}
                fieldWithDyns =
                  foldr
                    (\dyn acc -> VT.dynToField dyn (Just acc) unifier)
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
                    startField = field{VT.ssfValue = VT.dsfValue $ head dyns}
                    fieldWithDyns =
                      foldr
                        (\dyn acc -> VT.dynToField dyn (Just acc) unifier)
                        startField
                        (tail dyns)
                  newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems newCnstrs) tc
                  return ((name, newField) : accUpdated, accRemoved)
      )
      ([], [])
      (fieldsUnifiedWithObject objID $ Map.toList $ VT.stcFields struct)
  let res = VT.removeStructFields removedLabels $ VT.updateStructWithFields remAffFields struct
  return (res, map fst remAffFields)
 where
  allCnstrs = VT.stcCnstrs struct
  allDyns = VT.stcDynFields struct
  unifier l r = VT.mkMutableTree $ VT.mkUnifyOp [l, r]

  -- Find the fields that are unified with the object
  fieldsUnifiedWithObject :: Int -> [(T.Text, VT.Field VT.Tree)] -> [(T.Text, VT.Field VT.Tree)]
  fieldsUnifiedWithObject j =
    foldr (\(k, field) acc -> if j `elem` VT.ssfObjects field then (k, field) : acc else acc) []

-- | Apply the additional constraint to the fields.
applyMoreCnstr ::
  (RM.ReduceMonad s r m) =>
  VT.StructCnstr VT.Tree ->
  VT.Struct VT.Tree ->
  TCOps.TrCur ->
  m (VT.Struct VT.Tree, [T.Text])
applyMoreCnstr cnstr struct tc = RM.debugSpanRM "applyMoreCnstr" (const Nothing) tc $ do
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
  let newStruct = VT.updateStructWithFields addAffFields struct
  return (newStruct, addAffLabels)

reduceCnstredVal :: (RM.ReduceMonad s r m) => VT.CnstredVal VT.Tree -> TCOps.TrCur -> m VT.Tree
reduceCnstredVal _ tc = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  Cursor.tcFocus <$> TCOps.inSubTC Path.SubValTASeg reduce tc

reduceDisj :: (RM.ReduceMonad s r m) => VT.Disj VT.Tree -> TCOps.TrCur -> m VT.Tree
reduceDisj d tc = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  r <-
    Cursor.tcFocus
      <$> foldM
        (\acc (i, _) -> TCOps.inSubTC (Path.DisjDisjunctTASeg i) reduce acc)
        tc
        (zip [0 ..] (VT.dsjDisjuncts d))
  case VT.treeNode r of
    VT.TNDisj nd -> do
      let disjuncts = VT.dsjDisjuncts nd
      newDisjT <- VT.normalizeDisj VT.getDisjFromTree VT.mkDisjTree (d{VT.dsjDisjuncts = disjuncts})
      return $ VT.setTN (Cursor.tcFocus tc) (VT.treeNode newDisjT)
    _ -> return r

reduceList :: (RM.ReduceMonad s r m) => VT.List VT.Tree -> TCOps.TrCur -> m VT.Tree
reduceList l tc = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  r <-
    foldM
      ( \acc (i, origElem) -> do
          let elemTC = Cursor.mkSubTC (Path.IndexTASeg i) origElem tc
          r <- reduce elemTC
          case VT.treeNode origElem of
            -- If the element is a comprehension and the result of the comprehension is a list, per the spec, we insert
            -- the elements of the list into the list at the current index.
            VT.TNMutable (VT.Compreh cph)
              | VT.cphIsListCompreh cph
              , Just rList <- VT.getListFromTree r ->
                  return $ acc ++ VT.lstSubs rList
            _ -> return $ acc ++ [r]
      )
      []
      (zip [0 ..] (VT.lstSubs l))
  return $ VT.mkListTree r

-- built-in functions
builtinMutableTable :: [(String, VT.Tree)]
builtinMutableTable =
  [
    ( "close"
    , VT.mkMutableTree . VT.RegOp $
        -- built-in close does not recursively close the struct.
        VT.emptyRegularOp
          { VT.ropName = "close"
          , VT.ropArgs = Seq.fromList [VT.mkNewTree VT.TNTop]
          , VT.ropOpType = VT.CloseFunc
          }
    )
  ]

-- | Closes a struct when the tree has struct.
close :: (RM.ReduceMonad s r m) => [VT.Tree] -> TCOps.TrCur -> m (Maybe VT.Tree)
close args tc
  | length args /= 1 = throwErrSt $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      argTC <- TCOps.goDownTCSegMust Path.unaryOpTASeg tc
      rM <- Mutate.reduceToNonMut argTC
      maybe
        -- If the argument is pending, wait for the result.
        (return Nothing)
        (return . Just . closeTree)
        rM

-- | Close a struct when the tree has struct.
closeTree :: VT.Tree -> VT.Tree
closeTree a =
  case VT.treeNode a of
    VT.TNBlock b -> VT.setTN a $ VT.TNBlock $ VT.modifyBlockStruct (\s -> s{VT.stcClosed = True}) b
    VT.TNDisj dj ->
      let
        dft = closeTree <$> VT.dsjDefault dj
        ds = map closeTree (VT.dsjDisjuncts dj)
       in
        VT.setTN a $ VT.TNDisj (dj{VT.dsjDefault = dft, VT.dsjDisjuncts = ds})
    -- TODO: VT.Mutable should be closed.
    -- VT.TNMutable _ -> throwErrSt "TODO"
    _ -> VT.mkBottomTree $ printf "cannot use %s as struct in argument 1 to close" (show a)

reduceeDisjOp :: (RM.ReduceMonad s r m) => Bool -> VT.DisjoinOp VT.Tree -> TCOps.TrCur -> m (Maybe VT.Tree)
reduceeDisjOp asConj disjOp disjOpTC = RM.debugSpanRM "reduceeDisjOp" id disjOpTC $ do
  let terms = toList $ VT.djoTerms disjOp
  when (length terms < 2) $
    throwErrSt $
      printf "disjunction operation requires at least 2 terms, got %d" (length terms)
  disjuncts <- procMarkedTerms asConj terms disjOpTC
  RM.debugInstantRM "reduceeDisjOp" (printf "disjuncts: %s" (show disjuncts)) disjOpTC

  if null disjuncts
    -- If none of the disjuncts are ready, return Nothing.
    then return Nothing
    else do
      let
        d = VT.emptyDisj{VT.dsjDisjuncts = disjuncts}
      r <- VT.normalizeDisj VT.getDisjFromTree VT.mkDisjTree d
      return $ Just r

{- | Construct a disjunction from the default and the disjuncts.

It filters out incomplete disjuncts.

Some existing rules for marked disjunctions:
M0:  ⟨v⟩    => ⟨v⟩        don't introduce defaults for unmarked term
M1: *⟨v⟩    => ⟨v, v⟩     introduce identical default for marked term
M2: *⟨v, d⟩ => ⟨v, d⟩     keep existing defaults for marked term
M3:  ⟨v, d⟩ => ⟨v⟩        strip existing defaults from unmarked term
-}
procMarkedTerms :: (RM.ReduceMonad s r m) => Bool -> [VT.DisjTerm VT.Tree] -> TCOps.TrCur -> m [VT.Tree]
procMarkedTerms asConj terms tc = do
  -- disjoin operation allows incompleteness.

  let hasMarked = any VT.dstMarked terms
  reducedTerms <-
    -- If the disjunction is a conjunct, there is no need to reduce the terms.
    if asConj
      then return terms
      else
        -- We need to reduce the terms to know if they are disjunctions or not so that marked terms can be processed.
        foldM
          ( \acc (i, term) -> do
              argTC <- TCOps.goDownTCSegMust (Path.MutableArgTASeg i) tc
              rM <- Mutate.reduceToNonMut argTC
              case rM of
                Nothing -> return acc -- Incomplete term
                Just r -> return $ acc ++ [term{VT.dstValue = r}]
          )
          []
          (zip [0 ..] terms)
  return $
    foldr
      ( \term accDisjuncts ->
          let val = VT.dstValue term
           in if
                -- Apply Rule M1 and M2
                | hasMarked && VT.dstMarked term ->
                    VT.setTN
                      val
                      ( VT.TNDisj $
                          maybe
                            -- Rule M1
                            (VT.emptyDisj{VT.dsjDefIndexes = [0], VT.dsjDisjuncts = [val]})
                            ( \d ->
                                if null (VT.dsjDefIndexes d)
                                  -- Rule M1
                                  then d{VT.dsjDefIndexes = [0 .. length (VT.dsjDisjuncts d)]}
                                  -- Rule M2
                                  else d
                            )
                            (VT.getDisjFromTree val)
                      )
                      : accDisjuncts
                -- Apply Rule M0 and M3
                | hasMarked ->
                    maybe
                      val
                      (\d -> VT.setTN val $ VT.TNDisj $ d{VT.dsjDefIndexes = []})
                      (VT.getDisjFromTree val)
                      : accDisjuncts
                | otherwise -> val : accDisjuncts
      )
      []
      reducedTerms

reduceCompreh :: (RM.ReduceMonad s r m) => VT.Comprehension VT.Tree -> TCOps.TrCur -> m (Maybe VT.Tree)
reduceCompreh cph tc = RM.debugSpanRM "reduceCompreh" id tc $ do
  r <- reduceClause 0 cph tc (IterCtx 0 (Right []))
  case icRes r of
    Left Nothing -> return Nothing
    Left (Just t) -> return $ Just t
    Right vs ->
      if VT.cphIsListCompreh cph
        then return $ Just $ VT.mkListTree vs
        else return $ Just $ case vs of
          [] -> VT.mkBlockTree VT.emptyBlock
          [x] -> x
          _ -> VT.mkMutableTree $ VT.mkUnifyOp vs

data IterCtx = IterCtx
  { icCnt :: Int
  , icRes :: Either (Maybe VT.Tree) [VT.Tree]
  }
  deriving (Show)

reduceClause ::
  (RM.ReduceMonad s r m) =>
  Int ->
  VT.Comprehension VT.Tree ->
  TCOps.TrCur ->
  IterCtx ->
  m IterCtx
reduceClause i cph tc iterCtx
  | i == length (VT.cphIterClauses cph) = RM.debugSpanArgsRM
      (printf "reduceIterVal iter:%s" (show $ icCnt iterCtx))
      (printf "bindings: %s" (show $ VT.cphIterBindings cph))
      ( \x -> case icRes x of
          Left v -> v
          Right [] -> Nothing
          Right vs -> Just $ last vs
      )
      tc
      $ do
        let s = VT.cphStruct cph
        r <- newIterStruct (VT.cphIterBindings cph) s tc
        case icRes iterCtx of
          Left _ -> throwErrSt "should not reach the leaf node"
          Right vs -> return $ iterCtx{icRes = Right (vs ++ [r]), icCnt = icCnt iterCtx + 1}
  | otherwise = do
      clauseTC <- TCOps.goDownTCSegMust (Path.ComprehTASeg $ Path.ComprehIterClauseValTASeg i) tc
      tM <- Mutate.reduceToNonMut clauseTC
      case tM of
        -- Incomplete clause.
        Nothing -> return $ iterCtx{icRes = Left Nothing}
        Just t
          | VT.TNBottom _ <- VT.treeNode t -> return $ iterCtx{icRes = Left (Just t)}
          | otherwise -> case VT.cphIterClauses cph !! i of
              VT.IterClauseIf{} -> case VT.getAtomFromTree t of
                Just (VT.Bool True) -> reduceClause (i + 1) cph tc iterCtx
                -- Do not go to next clause if the condition is false.
                Just (VT.Bool False) -> return iterCtx
                _ ->
                  return $
                    iterCtx
                      { icRes = Left $ Just $ VT.mkBottomTree $ printf "%s is not a boolean" (VT.showTreeSymbol t)
                      }
              VT.IterClauseLet letName _ -> do
                let
                  newBind = VT.ComprehIterBinding letName t
                  newCompreh =
                    cph
                      { VT.cphIterBindings = VT.cphIterBindings cph ++ [newBind]
                      }
                  newTC = TCOps.setTCFocusTN (VT.TNMutable $ VT.Compreh newCompreh) tc
                reduceClause (i + 1) newCompreh newTC iterCtx
              VT.IterClauseFor k vM _ ->
                if
                  -- TODO: only iterate optional fields
                  | Just (VT.Block{VT.blkStruct = struct}) <- VT.getBlockFromTree t -> do
                      foldM
                        ( \acc (label, field) -> do
                            let
                              newBinds =
                                maybe
                                  [VT.ComprehIterBinding k (VT.ssfValue field)]
                                  ( \v ->
                                      [ VT.ComprehIterBinding k (VT.mkAtomTree (VT.String label))
                                      , VT.ComprehIterBinding v (VT.ssfValue field)
                                      ]
                                  )
                                  vM
                              newCompreh =
                                cph
                                  { VT.cphIterBindings = VT.cphIterBindings cph ++ newBinds
                                  }
                              newTC = TCOps.setTCFocusTN (VT.TNMutable $ VT.Compreh newCompreh) tc

                            reduceClause (i + 1) newCompreh newTC acc
                        )
                        iterCtx
                        (Map.toList $ VT.stcFields struct)
                  | Just (VT.List{VT.lstSubs = list}) <- VT.getListFromTree t -> do
                      foldM
                        ( \acc (index, element) -> do
                            let
                              newBinds =
                                maybe
                                  [VT.ComprehIterBinding k element]
                                  ( \v ->
                                      [ VT.ComprehIterBinding k (VT.mkAtomTree (VT.Int index))
                                      , VT.ComprehIterBinding v element
                                      ]
                                  )
                                  vM
                              newCompreh =
                                cph
                                  { VT.cphIterBindings = VT.cphIterBindings cph ++ newBinds
                                  }
                              newTC = TCOps.setTCFocusTN (VT.TNMutable $ VT.Compreh newCompreh) tc

                            reduceClause (i + 1) newCompreh newTC acc
                        )
                        iterCtx
                        (zip [0 ..] list)
                  | otherwise ->
                      return $
                        iterCtx
                          { icRes = Left $ Just $ VT.mkBottomTree $ printf "%s is not iterable" (VT.showTreeSymbol t)
                          }

{- | Create a new struct with the given bindings.

The generated struct will not have comoprehensions, otherwise it will be reduced again, and the bindings will be lost.
-}
newIterStruct ::
  (RM.ReduceMonad s r m) => [VT.ComprehIterBinding VT.Tree] -> VT.Tree -> TCOps.TrCur -> m VT.Tree
newIterStruct bindings rawStruct _tc =
  RM.debugSpanArgsRM
    "newIterStruct"
    (printf "bindings: %s" (show bindings))
    Just
    _tc
    $ do
      se <- Common.buildASTExpr False rawStruct
      structT <- RM.evalExprRM se
      MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
      let sTC = Cursor.mkSubTC (Path.ComprehTASeg Path.ComprehIterValTASeg) structT _tc
      r <- reduce sTC
      ripped <- case VT.treeNode r of
        VT.TNBlock block -> do
          let
            newBlock = block{VT.blkEmbeds = IntMap.filter (not . isComprehension) (VT.blkEmbeds block)}
          return $ VT.setTN r (VT.TNBlock newBlock)
        _ -> return r

      -- replace the refs that are found in the bindings with the binding values. This includes all references in all
      -- possible trees.
      x <-
        TCOps.traverseTCSimple
          (\x -> VT.subNodes x ++ VT.rawNodes x)
          ( \tc -> do
              let focus = Cursor.tcFocus tc
              case VT.treeNode focus of
                VT.TNMutable (VT.Ref ref)
                  -- oirgAddrs should be empty because the reference should not be copied from other places.
                  | Nothing <- VT.refOrigAddrs ref
                  , VT.RefPath var rest <- VT.refArg ref -> do
                      rM <-
                        foldM
                          ( \acc bind ->
                              if
                                | isJust acc -> return acc
                                | VT.cphBindName bind == var
                                , null rest ->
                                    return $ Just (VT.cphBindValue bind)
                                | VT.cphBindName bind == var ->
                                    return $
                                      Just $
                                        VT.setTN
                                          focus
                                          (VT.TNMutable $ VT.Ref $ VT.mkIndexRef (VT.cphBindValue bind Seq.<| rest))
                                | otherwise -> return acc
                          )
                          Nothing
                          (reverse bindings)
                      maybe (return focus) return rM
                _ -> return focus
          )
          (Cursor.TreeCursor ripped [])
      return $ Cursor.tcFocus x
 where
  isComprehension emb = case VT.treeNode (VT.embValue emb) of
    VT.TNMutable (VT.Compreh _) -> True
    _ -> False

reduceInterpolation :: (RM.ReduceMonad s r m) => VT.Interpolation VT.Tree -> TCOps.TrCur -> m (Maybe VT.Tree)
reduceInterpolation l tc = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  r <-
    foldM
      ( \accRes seg -> case seg of
          VT.IplSegExpr j -> do
            argTC <- TCOps.goDownTCSegMust (Path.MutableArgTASeg j) tc
            r <- reduce argTC
            if
              | Just s <- VT.getStringFromTree r -> return $ (`T.append` s) <$> accRes
              | Just i <- VT.getIntFromTree r -> return $ (`T.append` (T.pack $ show i)) <$> accRes
              | Just b <- VT.getBoolFromTree r -> return $ (`T.append` (T.pack $ show b)) <$> accRes
              | Just f <- VT.getFloatFromTree r -> return $ (`T.append` (T.pack $ show f)) <$> accRes
              | Just _ <- VT.getStructFromTree r ->
                  return $
                    Left $
                      VT.mkBottomTree $
                        printf "can not use struct in interpolation: %s" (VT.showTreeSymbol r)
              | Just _ <- VT.getListFromTree r ->
                  return $
                    Left $
                      VT.mkBottomTree $
                        printf "can not use list in interpolation: %s" (VT.showTreeSymbol r)
              | otherwise -> return undefined
          VT.IplSegStr s -> return $ (`T.append` s) <$> accRes
      )
      (Right T.empty)
      (VT.itpSegs l)
  case r of
    Left err -> return $ Just err
    Right res -> return $ Just $ VT.mkAtomTree (VT.String res)
