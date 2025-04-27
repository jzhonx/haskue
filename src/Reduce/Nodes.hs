{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Nodes where

import qualified Common
import Control.Monad (foldM, unless, when)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (asks)
import qualified Cursor
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified Reduce.UnifyOp as UnifyOp
import qualified TCOps
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

-- ###
-- Reduce tree nodes
-- ###

{- | Reduce the struct.

Most of the heavy work is done in the propUpStructPost function.
-}
reduceStruct :: forall s r m. (RM.ReduceMonad s r m) => TCOps.TrCur -> m VT.Tree
reduceStruct _tc = RM.debugSpanRM "reduceStruct" _tc $ do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs

  -- Close the struct if the tree is closed.
  utc <-
    RM.mustStruct
      _tc
      ( \(s, tc) -> do
          let
            focus = Cursor.tcFocus tc
            isClosed = VT.treeRecurClosed focus
          return $
            if isClosed
              -- Use RM.modifyTMTN instead of VT.mkNewTree because tree attributes need to be preserved, such as
              -- VT.treeRecurClosed.
              then VT.setTN focus (VT.TNStruct $ s{VT.stcClosed = True}) `Cursor.setTCFocus` tc
              else tc
      )
      >>= whenStruct (\(s, tc) -> foldM (flip validateLetName) tc (Map.keys $ VT.stcLets s))
      -- reduce the labels of the dynamic fields first. If the dynfields become actual fields, later they will be
      -- reduced.
      >>= whenStruct
        ( \(s, tc) ->
            foldM
              ( \acc (i, _) ->
                  -- Inserting reduced dynamic field element into the struct is handled by propUpStructPost.
                  inStructSub (Path.DynFieldTASeg i 0) reduce acc
              )
              tc
              (IntMap.toList $ VT.stcDynFields s)
        )
      >>= whenStruct
        ( \(s, tc) ->
            foldM
              ( \acc (i, _) ->
                  -- pattern value should never be reduced because the references inside the pattern value should only
                  -- be resolved in the unification node of the static field.
                  -- See unify for more details.
                  -- reduced constraint will constrain fields, which is done in the propUpStructPost.
                  inStructSub (Path.PatternTASeg i 0) reduce acc
              )
              tc
              (IntMap.toList $ VT.stcCnstrs s)
        )
      >>= whenStruct
        ( \(s, tc) ->
            foldM
              ( \acc (i, _) ->
                  -- Unifying reduced embedding with the rest of the struct is handled by propUpStructPost.
                  inStructSub (Path.EmbedTASeg i) reduce acc
              )
              tc
              (IntMap.toList $ VT.stcEmbeds s)
        )
      -- Add the let bindings to the unreferred let bindings.
      >>= whenStruct
        ( \(s, tc) -> do
            mapM_
              ( \x ->
                  RM.addRMUnreferredLet (Path.appendSeg (Path.StructTASeg (Path.LetTASeg x)) (Cursor.tcTreeAddr tc))
              )
              (Map.keys $ VT.stcLets s)

            unrefLets <- RM.getRMUnreferredLets
            RM.debugInstantRM
              "reduceStruct"
              (printf "unrefLets: %s" (show unrefLets))
              tc

            return tc
        )
      -- Reduce all fields. New fields might have been created by the dynamic fields.
      >>= whenStruct
        ( \(s, tc) ->
            foldM (\acc (x, _) -> reduceStructField x acc) tc (Map.toList . VT.stcFields $ s)
        )

  return $ Cursor.tcFocus utc

whenStruct ::
  (RM.ReduceMonad s r m) =>
  ((VT.Struct VT.Tree, TCOps.TrCur) -> m TCOps.TrCur) ->
  TCOps.TrCur ->
  m TCOps.TrCur
whenStruct f tc = do
  let t = Cursor.tcFocus tc
  case VT.treeNode t of
    VT.TNStruct struct -> f (struct, tc)
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
      let addr = Cursor.tcTreeAddr subTC
      if Common.isTreeBottom sub && Path.isInDisj addr
        then do
          return (sub `Cursor.setTCFocus` tc)
        else TCOps.propUpTC (sub `Cursor.setTCFocus` subTC)
    >>= whenStruct
      ( \(s, utc) -> do
          newS <- propUpStructPost (sseg, s) utc
          return $ newS `Cursor.setTCFocus` utc
      )

validateLetName :: (RM.ReduceMonad s r m) => String -> TCOps.TrCur -> m TCOps.TrCur
validateLetName name =
  whenStruct
    ( \(_, tc) -> do
        -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make sure
        -- in the parent scope that there is no field with the same name.
        parResM <- RefSys.searchTCIdentInPar name tc
        -- RM.withAddrAndFocus $ \addr _ ->
        --   logDebugStr $
        --     printf "validateLetName: addr: %s, var %s in parent: %s" (show addr) name (show parResM)

        return $ case parResM of
          -- If the let binding with the name is found in the scope.
          Just (_, True) -> lbRedeclErr name `Cursor.setTCFocus` tc
          -- If the field with the same name is found in the scope.
          Just (_, False) -> aliasErr name `Cursor.setTCFocus` tc
          _ -> tc
    )

aliasErr :: String -> VT.Tree
aliasErr name = VT.mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name

lbRedeclErr :: String -> VT.Tree
lbRedeclErr name = VT.mkBottomTree $ printf "%s redeclared in same scope" name

reduceStructField :: (RM.ReduceMonad s r m) => String -> TCOps.TrCur -> m TCOps.TrCur
reduceStructField name stc = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  whenStruct
    ( \(_, tc) -> do
        -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make
        -- sure in the parent scope that there is no field with the same name.
        parResM <- RefSys.searchTCIdentInPar name tc

        case parResM of
          -- If the let binding with the name is found in the scope.
          Just (_, True) -> return $ aliasErr name `Cursor.setTCFocus` tc
          _ -> return tc
    )
    stc
    >>= whenStruct
      (\(_, tc) -> inStructSub (Path.StringTASeg name) reduce tc)

{- | Handle the post process of propagating value into struct.

The focus of the tree must be a struct.
-}
propUpStructPost :: (RM.ReduceMonad s r m) => (Path.StructTASeg, VT.Struct VT.Tree) -> TCOps.TrCur -> m VT.Tree
propUpStructPost (Path.DynFieldTASeg i _, _struct) stc = RM.debugSpanRM
  (printf "propUpStructPost_dynamic, idx: %s" (show i))
  stc
  $ do
    -- First we need to remove the dynamic field with the old label from the struct.
    (remAffStruct, _) <- removeAppliedObject i _struct stc

    let
      dsf = VT.stcDynFields _struct IntMap.! i
      rE = dynFieldToStatic remAffStruct dsf
      allCnstrs = IntMap.elems $ VT.stcCnstrs remAffStruct

    RM.debugInstantRM "propUpStructPost_dynamic" (printf "dsf: %s, rE: %s" (show dsf) (show rE)) stc

    either
      (\err -> return $ VT.setTN (Cursor.tcFocus stc) (VT.treeNode err))
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

          RM.debugInstantRM "propUpStructPost_dynamic" (printf "addAffFields: %s" (show addAffFields)) stc

          let newSTC = TCOps.setTCFocusTN (VT.TNStruct $ VT.updateStructWithFields addAffFields remAffStruct) stc

          -- -- Check the permission of the label of newly created field.
          -- whenStruct () $ \s -> checkPermForNewDyn s (Path.DynFieldTASeg i 0)

          -- Reduce the updated struct value, which is the new field, if it is matched with any constraints.
          final <- whenStruct (\(_, tc) -> foldM (flip reduceStructField) tc addAffLabels) newSTC
          return $ Cursor.tcFocus final
      )
      rE
propUpStructPost (Path.PatternTASeg i _, struct) stc =
  RM.debugSpanRM (printf "propUpStructPost_constraint, idx: %s" (show i)) stc $ do
    -- Constrain all fields with the new constraint if it exists.
    let cnstr = VT.stcCnstrs struct IntMap.! i
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

    (remAffStruct, remAffLabels) <- removeAppliedObject i struct stc
    -- RM.withAddrAndFocus $ \addr _ ->
    --   logDebugStr $
    --     printf
    --       "propUpStructPost_constraint: addr: %s, remAffLabels: %s, remAffStruct: %s"
    --       (show addr)
    --       (show remAffLabels)
    --       (show $ VT.mkStructTree remAffStruct)
    (newStruct, addAffLabels) <- applyMoreCnstr cnstr remAffStruct stc
    -- RM.modifyTMNodeWithTree (VT.mkStructTree newStruct)

    let
      affectedLabels = remAffLabels ++ addAffLabels
      nstc = VT.mkStructTree newStruct `Cursor.setTCFocus` stc
    unless (null affectedLabels) $
      RM.debugInstantRM
        "propUpStructPost_constraint"
        ( printf
            "-ns: %s, +ns: %s, new struct: %s"
            (show remAffLabels)
            (show addAffLabels)
            (show $ VT.mkStructTree newStruct)
        )
        nstc

    -- whenStruct () $ \s -> checkPermForNewPattern s (Path.PatternTASeg i 0)

    -- Reduce the updated struct values.
    Cursor.tcFocus <$> whenStruct (\_ -> foldM (flip reduceStructField) nstc affectedLabels) nstc
propUpStructPost (Path.EmbedTASeg i, struct) stc =
  RM.debugSpanRM (printf "propUpStructPost_embed, idx: %s" (show i)) stc $ do
    let embed = VT.stcEmbeds struct IntMap.! i
        embedVM = case VT.treeNode (VT.embValue embed) of
          -- TODO: make getMutVal deal with stub value
          VT.TNMutable mut -> do
            v <- VT.getMutVal mut
            if v == VT.stubTree
              then Nothing
              else Just v
          _ -> Just $ VT.embValue embed
    case embedVM of
      Nothing -> return $ Cursor.tcFocus stc
      Just ev -> do
        -- First remove the fields, constraints and dynamic fields from the embedding. Every field from the embedding
        -- has an object ID that is the same as the embedding ID.
        let rmIDs =
              i : case VT.treeNode ev of
                VT.TNStruct es -> IntMap.keys (VT.stcCnstrs es) ++ IntMap.keys (VT.stcDynFields es)
                _ -> []

        (allRmStruct, affectedLabels) <-
          foldM
            ( \(accStruct, accLabels) idx -> do
                (s, affLabels) <- removeAppliedObject idx accStruct stc
                return (s, affLabels ++ accLabels)
            )
            (struct, [])
            rmIDs

        -- RM.debugInstantRM "propUpStructPost_embed" $
        --   printf
        --     "rmIDS: %s, affectedLabels: %s, allRmStruct: %s"
        --     (show rmIDs)
        --     (show affectedLabels)
        --     (show allRmStruct)
        -- Restore the focus with the struct without the embedding unified.
        -- RM.modifyTMTN (VT.TNStruct allRmStruct)

        -- MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
        -- addr <- RM.getTMAbsAddr

        let
          saveEmbeds = VT.stcEmbeds allRmStruct
          -- We don't want any embeddings to be re-evaluated in a deeper env. Plus, it would make reducing infinite.
          t1 = VT.mkStructTree (allRmStruct{VT.stcEmbeds = IntMap.empty})
        embedTC <- TCOps.goDownTCSegMust (Path.StructTASeg (Path.EmbedTASeg i)) stc
        mergedM <-
          UnifyOp.unifyUTrees
            [ UnifyOp.UTree Path.L Nothing (t1 `Cursor.setTCFocus` stc)
            , UnifyOp.UTree Path.R (Just i) (ev `Cursor.setTCFocus` embedTC)
            ]
            (Cursor.tcTreeAddr stc)

        maybe
          (return $ Cursor.tcFocus stc)
          ( \merged -> do
              MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
              res <- reduce (merged `Cursor.setTCFocus` stc)
              let r = case VT.treeNode res of
                    VT.TNStruct s -> VT.mkStructTree $ s{VT.stcEmbeds = saveEmbeds}
                    _ -> res
              return $ VT.setTN (Cursor.tcFocus stc) (VT.treeNode r)
          )
          mergedM

-- RM.inTempSubTM
--   ( VT.mkMutableTree $
--       VT.mkBinaryOp
--         AST.Unify
--         ( \_ _ -> do
--             -- tmpAddr <- RM.getTMAbsAddr
--             -- let
--             --   funcAddr = fromJust $ Path.initTreeAddr tmpAddr
--             --   rAddr = Path.appendSeg Path.binOpRightTASeg funcAddr
--             --   ut1 = UnifyOp.UTree t1 Path.L Nothing addr
--             --   ut2 = UnifyOp.UTree t2 Path.R (Just i) rAddr
--             let ut1 = undefined
--                 ut2 = undefined
--             UnifyOp.mergeBinUTrees ut1 ut2
--             UnifyOp.reduceMerged
--         )
--         t1
--         t2
--   )
--   (reduce >> RM.getTMTree)

-- RM.debugInstantTM "propUpStructPost_embed" $ printf "r: %s" (VT.treeFullStr 0 r)

propUpStructPost (_, _) stc = return $ Cursor.tcFocus stc

getLabelFieldPairs :: VT.Struct VT.Tree -> [(String, VT.Field VT.Tree)]
getLabelFieldPairs struct = Map.toList $ VT.stcFields struct

{- | Convert a dynamic field to a static field.

It returns a pair which contains reduced string and the newly created/updated field.
-}
dynFieldToStatic ::
  VT.Struct VT.Tree ->
  VT.DynamicField VT.Tree ->
  Either VT.Tree (Maybe (String, VT.Field VT.Tree))
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
  (RM.ReduceMonad s r m) => String -> VT.Field VT.Tree -> [VT.StructCnstr VT.Tree] -> TCOps.TrCur -> m (VT.Field VT.Tree)
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
  String ->
  VT.Field VT.Tree ->
  VT.StructCnstr VT.Tree ->
  TCOps.TrCur ->
  m (VT.Field VT.Tree, Bool)
bindFieldWithCnstr name field cnstr tc = do
  let selPattern = VT.scsPattern cnstr

  matched <- UnifyOp.patMatchLabel selPattern name tc
  logDebugStr $ printf "bindFieldWithCnstr: %s with %s, matched: %s" name (show selPattern) (show matched)

  let
    fval = VT.ssfValue field
    -- TODO: comment on why mkCnstredValTree is used.
    op = VT.mkMutableTree $ VT.mkUnifyOp [fval, VT.mkCnstredValTree (VT.scsValue cnstr) Nothing]
    newField =
      if matched
        then field{VT.ssfValue = op, VT.ssfObjects = Set.insert (VT.scsID cnstr) (VT.ssfObjects field)}
        else field

  logDebugStr $
    printf "bindFieldWithCnstr: %s with %s, matched: %s, newField: %s" name (show selPattern) (show matched) (show newField)

  return (newField, matched)

{- | Update the struct with the constrained result.

If the constrained result introduce new fields that are not in the struct, then they are ignored.
-}
updateStructWithCnstredRes ::
  -- | The constrained result is a list of tuples that contains the name of the field, the field.
  [(String, VT.Field VT.Tree)] ->
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
filterMatchedNames :: (RM.ReduceMonad s r m) => VT.StructCnstr VT.Tree -> [String] -> TCOps.TrCur -> m [String]
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
  m (VT.Struct VT.Tree, [String])
removeAppliedObject objID struct tc = RM.debugSpanRM "removeAppliedObject" tc $ do
  logDebugStr $
    printf
      "removeAppliedObject: objID: %s, struct: %s"
      (show objID)
      (show $ VT.mkStructTree struct)

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
  fieldsUnifiedWithObject :: Int -> [(String, VT.Field VT.Tree)] -> [(String, VT.Field VT.Tree)]
  fieldsUnifiedWithObject j =
    foldr (\(k, field) acc -> if j `elem` VT.ssfObjects field then (k, field) : acc else acc) []

-- | Apply the additional constraint to the fields.
applyMoreCnstr ::
  (RM.ReduceMonad s r m) =>
  VT.StructCnstr VT.Tree ->
  VT.Struct VT.Tree ->
  TCOps.TrCur ->
  m (VT.Struct VT.Tree, [String])
applyMoreCnstr cnstr struct tc = RM.debugSpanRM "applyMoreCnstr" tc $ do
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
  logDebugStr $
    printf
      "applyMoreCnstr: addAffFields: %s, addAffLabels: %s, struct: %s, newStruct: %s"
      (show addAffFields)
      (show addAffLabels)
      (show $ VT.mkStructTree struct)
      (show $ VT.mkStructTree newStruct)
  return (newStruct, addAffLabels)

-- checkPermForNewDyn :: (RM.ReduceTCMonad s r m) => VT.Struct VT.Tree -> Path.StructTASeg -> m ()
-- checkPermForNewDyn struct (Path.DynFieldTASeg i 0) =
--   let perms = VT.getPermInfoForDyn struct i
--    in mapM_ (validatePermItem struct) perms
-- checkPermForNewDyn _ opLabel = throwErrSt $ printf "invalid opLabel %s" (show opLabel)

-- checkPermForNewPattern :: (RM.ReduceTCMonad s r m) => VT.Struct VT.Tree -> Path.StructTASeg -> m ()
-- checkPermForNewPattern struct (Path.PatternTASeg i 0) =
--   let perms = VT.getPermInfoForPattern struct i
--    in mapM_ (validatePermItem struct) perms
-- checkPermForNewPattern _ opLabel = throwErrSt $ printf "invalid opLabel %s" (show opLabel)

reduceCnstredVal :: (RM.ReduceMonad s r m) => VT.CnstredVal VT.Tree -> TCOps.TrCur -> m VT.Tree
reduceCnstredVal _ tc = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  Cursor.tcFocus <$> TCOps.inSubTC Path.SubValTASeg reduce tc

-- | Create a new identifier reference.
mkVarLinkTree :: (MonadError String m) => String -> m VT.Tree
mkVarLinkTree var = do
  let mut = VT.mkRefMutable var []
  return $ VT.mkMutableTree mut

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
  Cursor.tcFocus
    <$> foldM
      (\acc (i, _) -> TCOps.inSubTC (Path.IndexTASeg i) reduce acc)
      tc
      (zip [0 ..] (VT.lstSubs l))

-- built-in functions
builtinMutableTable :: [(String, VT.Tree)]
builtinMutableTable =
  [
    ( "close"
    , VT.mkMutableTree . VT.RegOp $
        -- built-in close does not recursively close the struct.
        VT.emptyRegularOp
          { VT.ropName = "close"
          , VT.ropArgs = [VT.mkNewTree VT.TNTop]
          , VT.ropOpType = VT.CloseFunc
          }
    )
  ]

-- | Closes a struct when the tree has struct.
close :: (RM.ReduceMonad s r m) => [VT.Tree] -> TCOps.TrCur -> m (Maybe VT.Tree)
close args tc
  | length args /= 1 = throwErrSt $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      r <- Mutate.reduceMutableArg Path.unaryOpTASeg tc
      case VT.treeNode r of
        -- If the argument is pending, wait for the result.
        VT.TNMutable _ -> return Nothing
        _ -> return $ Just $ closeTree r

-- | Close a struct when the tree has struct.
closeTree :: VT.Tree -> VT.Tree
closeTree a =
  case VT.treeNode a of
    VT.TNStruct s -> VT.setTN a $ VT.TNStruct s{VT.stcClosed = True}
    VT.TNDisj dj ->
      let
        dft = closeTree <$> VT.dsjDefault dj
        ds = map closeTree (VT.dsjDisjuncts dj)
       in
        VT.setTN a $ VT.TNDisj (dj{VT.dsjDefault = dft, VT.dsjDisjuncts = ds})
    -- TODO: VT.Mutable should be closed.
    -- VT.TNMutable _ -> throwErrSt "TODO"
    _ -> VT.mkBottomTree $ printf "cannot use %s as struct in argument 1 to close" (show a)
