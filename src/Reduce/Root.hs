{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Root where

import qualified AST
import Common (
  TreeOp (isTreeBottom),
 )
import Control.Monad (foldM, unless, when)
import Control.Monad.Except (MonadError)
import Cursor (
  Context (Context, ctxReduceStack),
  hasCtxNotifSender,
 )
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, isJust)
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.Notif as Notif
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified Reduce.RegOps as RegOps
import qualified Reduce.UnifyOp as UnifyOp
import Text.Printf (printf)
import Util (
  getTraceID,
  logDebugStr,
 )
import qualified Value.Tree as VT

fullReduce :: (RM.ReduceMonad s r m) => m ()
fullReduce = RM.debugSpanRM "fullReduce" $ do
  reduce
  Notif.drainRefSysQueue

-- | Reduce the tree to the lowest form.
reduce :: (RM.ReduceMonad s r m) => m ()
reduce = RM.withAddrAndFocus $ \addr _ -> RM.debugSpanRM "reduce" $ do
  RM.treeDepthCheck
  push addr

  -- tid <- getTraceID
  -- RM.dumpEntireTree $ printf "reduce id=%s start" (show tid)

  -- save the original tree before effects are applied to the focus of the tree.
  orig <- RM.getRMTree
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNMutable _ -> Mutate.mutate
    VT.TNStruct _ -> reduceStruct
    VT.TNList _ -> RM.traverseSub reduce
    VT.TNDisj _ -> RM.traverseSub reduce
    VT.TNCnstredVal cv -> reduceCnstredVal cv
    VT.TNStructuralCycle _ -> RM.putRMTree $ VT.mkBottomTree "structural cycle"
    VT.TNStub -> throwErrSt "stub node should not be reduced"
    _ -> return ()

  -- Overwrite the treenode of the raw with the reduced tree's VT.TreeNode to preserve tree attributes.
  RM.withTree $ \t -> RM.putRMTree $ VT.setTN orig (VT.treeNode t)

  notifyEnabled <- RM.getRMRefSysEnabled
  isSender <- hasCtxNotifSender addr <$> RM.getRMContext
  -- Only notify dependents when we are not in a temporary node.
  let refAddrM = Path.referableAddr addr
  if isSender && Path.isTreeAddrAccessible addr && notifyEnabled && isJust refAddrM
    then do
      let refAddr = fromJust refAddrM
      RM.debugInstantRM "enqueue" $ printf "addr: %s, enqueue new reduced Addr: %s" (show addr) (show refAddr)
      RM.addToRMRefSysQ refAddr
    else logDebugStr $ printf "reduce, addr: %s, not accessible or not enabled" (show addr)

  pop
 where
  -- RM.dumpEntireTree $ printf "reduce id=%s done" (show tid)

  push addr = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}

  pop = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}

-- ###
-- Reduce tree nodes
-- ###

{- | Reduce the struct.

Most of the heavy work is done in the propUpStructPost function.
-}
reduceStruct :: forall s r m. (RM.ReduceMonad s r m) => m ()
reduceStruct = RM.debugSpanRM "reduceStruct" $ do
  -- Close the struct if the tree is closed.
  RM.mustStruct $ \s -> do
    closed <- VT.treeRecurClosed <$> RM.getRMTree
    when closed $
      -- Use RM.modifyRMTN instead of VT.mkNewTree because tree attributes need to be preserved, such as VT.treeRecurClosed.
      RM.modifyRMTN (VT.TNStruct $ s{VT.stcClosed = True})

  whenStruct () $ \s -> mapM_ validateLetName (Map.keys $ VT.stcLets s)

  -- reduce the labels of the dynamic fields first. If the dynfields become actual fields, later they will be reduced.
  whenStruct () $ \s ->
    foldM
      ( \_ (i, df) ->
          -- Inserting reduced dynamic field element into the struct is handled by propUpStructPost.
          RM.inSubRM (Path.StructTASeg (Path.DynFieldTASeg i 0)) (VT.dsfLabel df) reduce
      )
      ()
      (IntMap.toList $ VT.stcDynFields s)

  whenStruct () $ \s ->
    foldM
      ( \_ (i, cnstr) ->
          -- pattern value should never be reduced because the references inside the pattern value should only be
          -- resolved in the unification node of the static field.
          -- See unify for more details.
          -- reduced constraint will constrain fields, which is done in the propUpStructPost.
          RM.inSubRM (Path.StructTASeg (Path.PatternTASeg i 0)) (VT.scsPattern cnstr) reduce
      )
      ()
      (IntMap.toList $ VT.stcCnstrs s)

  whenStruct () $ \s ->
    mapM_
      ( \(i, embed) ->
          -- Unifying reduced embedding with the rest of the struct is handled by propUpStructPost.
          RM.inSubRM (Path.StructTASeg (Path.EmbedTASeg i)) (VT.embValue embed) reduce
      )
      (IntMap.toList $ VT.stcEmbeds s)

  -- Reduce all fields. New fields might have been created by the dynamic fields.
  whenStruct () $ \s -> mapM_ (reduceStructField . fst) (Map.toList . VT.stcFields $ s)

whenStruct :: (RM.ReduceMonad s r m) => a -> (VT.Struct VT.Tree -> m a) -> m a
whenStruct a f = do
  t <- RM.getRMTree
  case VT.treeNode t of
    VT.TNStruct struct -> f struct
    -- The struct might have been turned to another type due to embedding.
    _ -> return a

validateLetName :: (RM.ReduceMonad s r m) => String -> m ()
validateLetName name = whenStruct () $ \_ -> do
  -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make sure
  -- in the parent scope that there is no field with the same name.
  parResM <- RefSys.searchRMVarInPar name
  RM.withAddrAndFocus $ \addr _ ->
    logDebugStr $
      printf "validateLetName: addr: %s, var %s in parent: %s" (show addr) name (show parResM)

  case parResM of
    -- If the let binding with the name is found in the scope.
    Just (_, True) -> RM.putRMTree $ lbRedeclErr name
    -- If the field with the same name is found in the scope.
    Just (_, False) -> RM.putRMTree $ aliasErr name
    _ -> return ()

aliasErr :: String -> VT.Tree
aliasErr name = VT.mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name

lbRedeclErr :: String -> VT.Tree
lbRedeclErr name = VT.mkBottomTree $ printf "%s redeclared in same scope" name

reduceStructField :: (RM.ReduceMonad s r m) => String -> m ()
reduceStructField name = whenStruct () $ \struct -> do
  -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make sure
  -- in the parent scope that there is no field with the same name.
  parResM <- RefSys.searchRMVarInPar name
  RM.withAddrAndFocus $ \addr _ ->
    logDebugStr $
      printf "reduceStructField: addr: %s, var %s in parent: %s" (show addr) name (show parResM)

  case parResM of
    -- If the let binding with the name is found in the scope.
    Just (_, True) -> RM.putRMTree $ aliasErr name
    _ -> return ()

  whenStruct () $ \_ -> do
    sub <-
      maybe
        (throwErrSt $ printf "%s is not found" (show name))
        return
        (VT.lookupStructField name struct)
    RM.inSubRM (Path.StructTASeg $ Path.StringTASeg name) (VT.ssfValue sub) reduce

{- | Handle the post process of propagating value into struct.

The focus of the tree must be a struct.
-}
propUpStructPost :: (RM.ReduceMonad s r m) => (Path.StructTASeg, VT.Struct VT.Tree) -> m ()
propUpStructPost (Path.DynFieldTASeg i _, _struct) = RM.debugSpanRM
  (printf "propUpStructPost_dynamic, idx: %s" (show i))
  $ do
    -- First we need to remove the dynamic field with the old label from the struct.
    (remAffStruct, _) <- removeAppliedObject i _struct

    let
      dsf = VT.stcDynFields _struct IntMap.! i
      rE = dynFieldToStatic remAffStruct dsf
      allCnstrs = IntMap.elems $ VT.stcCnstrs remAffStruct

    RM.debugInstantRM "propUpStructPost_dynamic" $ printf "dsf: %s, rE: %s" (show dsf) (show rE)

    either
      RM.modifyRMNodeWithTree
      ( \labelFieldM -> do
          -- Constrain the dynamic field with all existing constraints.
          (addAffFields, addAffLabels) <-
            maybe
              (return ([], []))
              ( \(name, field) -> do
                  newField <- constrainFieldWithCnstrs name field allCnstrs
                  return
                    ( [(name, newField)]
                    , if not (null $ VT.ssfObjects newField) then [name] else []
                    )
              )
              labelFieldM

          RM.debugInstantRM "propUpStructPost_dynamic" $ printf "addAffFields: %s" (show addAffFields)

          RM.modifyRMNodeWithTree (VT.mkStructTree $ VT.updateStructWithFields addAffFields remAffStruct)

          -- Check the permission of the label of newly created field.
          whenStruct () $ \s -> checkPermForNewPend s (Path.DynFieldTASeg i 0)

          -- Reduce the updated struct value, which is the new field, if it is matched with any constraints.
          whenStruct () $ \_ -> mapM_ reduceStructField addAffLabels
      )
      rE
propUpStructPost (Path.PatternTASeg i _, struct) =
  RM.debugSpanRM (printf "propUpStructPost_constraint, idx: %s" (show i)) $ do
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

    (remAffStruct, remAffLabels) <- removeAppliedObject i struct
    RM.withAddrAndFocus $ \addr _ ->
      logDebugStr $
        printf
          "propUpStructPost_constraint: addr: %s, remAffLabels: %s, remAffStruct: %s"
          (show addr)
          (show remAffLabels)
          (show $ VT.mkStructTree remAffStruct)
    (newStruct, addAffLabels) <- applyMoreCnstr cnstr remAffStruct
    RM.modifyRMNodeWithTree (VT.mkStructTree newStruct)

    let affectedLabels = remAffLabels ++ addAffLabels
    unless (null affectedLabels) $
      RM.debugInstantRM
        "propUpStructPost_constraint"
        ( printf
            "-ns: %s, +ns: %s, new struct: %s"
            (show remAffLabels)
            (show addAffLabels)
            (show $ VT.mkStructTree newStruct)
        )

    whenStruct () $ \s -> checkPermForNewPattern s (Path.PatternTASeg i 0)

    -- Reduce the updated struct values.
    whenStruct () $ \_ -> mapM_ reduceStructField affectedLabels
propUpStructPost (Path.EmbedTASeg i, struct) =
  RM.debugSpanRM (printf "propUpStructPost_embed, idx: %s" (show i)) $
    do
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
        Nothing -> return ()
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
                  (s, affLabels) <- removeAppliedObject idx accStruct
                  return (s, affLabels ++ accLabels)
              )
              (struct, [])
              rmIDs

          RM.debugInstantRM "propUpStructPost_embed" $
            printf
              "rmIDS: %s, affectedLabels: %s, allRmStruct: %s"
              (show rmIDs)
              (show affectedLabels)
              (show allRmStruct)
          -- Restore the focus with the struct without the embedding unified.
          RM.modifyRMTN (VT.TNStruct allRmStruct)

          addr <- RM.getRMAbsAddr

          let
            saveEmbeds = VT.stcEmbeds allRmStruct
            -- We don't want any embeddings to be re-evaluated. Plus, it would make reducing infinite.
            t1 = VT.mkStructTree (allRmStruct{VT.stcEmbeds = IntMap.empty})
            t2 = ev
          res <-
            RM.inTempSubRM
              ( VT.mkMutableTree $
                  VT.mkBinaryOp
                    AST.Unify
                    ( \_ _ -> do
                        tmpAddr <- RM.getRMAbsAddr
                        let
                          funcAddr = fromJust $ Path.initTreeAddr tmpAddr
                          rAddr = Path.appendSeg Path.binOpRightTASeg funcAddr
                          ut1 = UnifyOp.UTree t1 Path.L Nothing addr
                          ut2 = UnifyOp.UTree t2 Path.R (Just i) rAddr
                        UnifyOp.mergeUTrees ut1 ut2
                    )
                    t1
                    t2
              )
              (reduce >> RM.getRMTree)

          let r = case VT.treeNode res of
                VT.TNStruct s -> VT.mkStructTree $ s{VT.stcEmbeds = saveEmbeds}
                _ -> res

          RM.debugInstantRM "propUpStructPost_embed" $
            printf "r: %s" (VT.treeFullStr 0 r)

          RM.modifyRMNodeWithTree r
propUpStructPost (_, _) = return ()

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
      unifier l r = VT.mkMutableTree $ mkUnifyNode l r
      newSF = VT.dynToField df (VT.lookupStructField s struct) unifier
     in
      return (Just (s, newSF))

{- | Apply pattern constraints ([pattern]: constraint) to the static field.

Returns the new field. If the field is not matched with the pattern, it returns the original field.
-}
constrainFieldWithCnstrs ::
  (RM.ReduceMonad s r m) => String -> VT.Field VT.Tree -> [VT.StructCnstr VT.Tree] -> m (VT.Field VT.Tree)
constrainFieldWithCnstrs name =
  foldM
    ( \accField cnstr -> do
        (newField, _) <- bindFieldWithCnstr name accField cnstr
        return newField
    )

{- | Bind the pattern constraint ([pattern]: constraint) to the static field if the field name matches the pattern.

If the field name matches the pattern, it returns the new unify function node, which is constraint & field.
Otherwise, return the original field.

The field should not have been applied with the constraint before.

It can run in any kind of node.
-}
bindFieldWithCnstr ::
  (RM.ReduceMonad s r m) => String -> VT.Field VT.Tree -> VT.StructCnstr VT.Tree -> m (VT.Field VT.Tree, Bool)
bindFieldWithCnstr name field cnstr = do
  let selPattern = VT.scsPattern cnstr

  matched <- UnifyOp.patMatchLabel selPattern name
  logDebugStr $ printf "bindFieldWithCnstr: %s with %s, matched: %s" name (show selPattern) (show matched)

  let
    fval = VT.ssfValue field
    -- TODO: comment on why mkCnstredValTree is used.
    op = VT.mkMutableTree $ mkUnifyNode fval (VT.mkCnstredValTree (VT.scsValue cnstr) Nothing)
    newField =
      if matched
        then field{VT.ssfValue = op, VT.ssfObjects = Set.insert (VT.scsID cnstr) (VT.ssfObjects field)}
        else field

  logDebugStr $
    printf "bindFieldWithCnstr: %s with %s, matched: %s, newField: %s" name (show selPattern) (show matched) (show newField)

  return (newField, matched)

mkUnifyNode :: VT.Tree -> VT.Tree -> VT.Mutable VT.Tree
mkUnifyNode = VT.mkBinaryOp AST.Unify UnifyOp.unify

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
filterMatchedNames :: (RM.ReduceMonad s r m) => VT.StructCnstr VT.Tree -> [String] -> m [String]
filterMatchedNames cnstr =
  foldM
    ( \acc name -> do
        matched <- UnifyOp.patMatchLabel (VT.scsPattern cnstr) name
        return $ if matched then name : acc else acc
    )
    []

{- | Remove the applied object from the fields.

Returns the updated struct and the list of labels whose fields are affected.

This is done by re-applying existing objects except the one that is removed because unification is a lossy operation.
-}
removeAppliedObject ::
  (RM.ReduceMonad s r m) =>
  Int ->
  VT.Struct VT.Tree ->
  m (VT.Struct VT.Tree, [String])
removeAppliedObject objID struct = RM.debugSpanRM "removeAppliedObject" $ do
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
          RM.debugInstantRM "removeAppliedObject" $
            printf
              "field: %s, objID: %s, newObjectIDs: %s, raw: %s"
              name
              (show objID)
              (show $ Set.toList newObjectIDs)
              (show baseRawM)
          case baseRawM of
            Just raw -> do
              let
                rawField = field{VT.ssfValue = raw, VT.ssfObjects = Set.empty}
                fieldWithDyns =
                  foldr
                    (\dyn acc -> VT.dynToField dyn (Just acc) unifier)
                    rawField
                    (IntMap.elems newDyns)
              newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems newCnstrs)
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
                  newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems newCnstrs)
                  return ((name, newField) : accUpdated, accRemoved)
      )
      ([], [])
      (fieldsUnifiedWithObject objID $ Map.toList $ VT.stcFields struct)
  let res = VT.removeStructFields removedLabels $ VT.updateStructWithFields remAffFields struct
  return (res, map fst remAffFields)
 where
  allCnstrs = VT.stcCnstrs struct
  allDyns = VT.stcDynFields struct
  unifier l r = VT.mkMutableTree $ mkUnifyNode l r

  -- Find the fields that are unified with the object
  fieldsUnifiedWithObject :: Int -> [(String, VT.Field VT.Tree)] -> [(String, VT.Field VT.Tree)]
  fieldsUnifiedWithObject j =
    foldr (\(k, field) acc -> if j `elem` VT.ssfObjects field then (k, field) : acc else acc) []

-- | Apply the additional constraint to the fields.
applyMoreCnstr ::
  (RM.ReduceMonad s r m) =>
  VT.StructCnstr VT.Tree ->
  VT.Struct VT.Tree ->
  m (VT.Struct VT.Tree, [String])
applyMoreCnstr cnstr struct = RM.debugSpanRM "applyMoreCnstr" $ do
  (addAffFields, addAffLabels) <-
    foldM
      ( \(accFields, accLabels) (name, field) -> do
          (nf, isMatched) <- bindFieldWithCnstr name field cnstr
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

checkPermForNewPend :: (RM.ReduceMonad s r m) => VT.Struct VT.Tree -> Path.StructTASeg -> m ()
checkPermForNewPend struct (Path.DynFieldTASeg i 0) =
  let perms = VT.getPermInfoForDyn struct i
   in mapM_ (validatePermItem struct) perms
checkPermForNewPend _ opLabel = throwErrSt $ printf "invalid opLabel %s" (show opLabel)

checkPermForNewPattern :: (RM.ReduceMonad s r m) => VT.Struct VT.Tree -> Path.StructTASeg -> m ()
checkPermForNewPattern struct (Path.PatternTASeg i 0) =
  let perms = VT.getPermInfoForPattern struct i
   in mapM_ (validatePermItem struct) perms
checkPermForNewPattern _ opLabel = throwErrSt $ printf "invalid opLabel %s" (show opLabel)

{- | Validate the permission item.

A struct must be provided so that dynamic fields and constraints can be found.

It constructs the allowing labels and constraints and checks if the joining labels are allowed.
-}
validatePermItem :: (RM.ReduceMonad s r m) => VT.Struct VT.Tree -> VT.PermItem -> m ()
validatePermItem struct p =
  let
    labels = VT.piLabels p `Set.union` dynIdxesToLabels (VT.piDyns p)
    cnstrs = IntMap.fromList $ map (\i -> (i, VT.stcCnstrs struct IntMap.! i)) (Set.toList $ VT.piCnstrs p)
    opLabels = Set.toList $ VT.piOpLabels p `Set.union` dynIdxesToLabels (VT.piOpDyns p)
   in
    UnifyOp.checkLabelsPerm labels cnstrs True False opLabels
 where
  dynIdxesToLabels :: Set.Set Int -> Set.Set String
  dynIdxesToLabels idxes =
    Set.fromList
      ( catMaybes $
          map
            ( \i ->
                VT.getStringFromTree (VT.dsfLabel $ VT.stcDynFields struct IntMap.! i)
            )
            (Set.toList idxes)
      )

reduceCnstredVal :: (RM.ReduceMonad s r m) => VT.CnstredVal VT.Tree -> m ()
reduceCnstredVal cv = RM.inSubRM Path.SubValTASeg (VT.cnsedVal cv) reduce

-- | Create a new identifier reference.
mkVarLinkTree :: (MonadError String m) => String -> m VT.Tree
mkVarLinkTree var = do
  let mut = VT.mkRefMutable var []
  return $ VT.mkMutableTree mut

dispBinMutable :: (RM.ReduceMonad s r m) => AST.BinaryOp -> VT.Tree -> VT.Tree -> m ()
dispBinMutable op = case op of
  AST.Unify -> UnifyOp.unify
  _ -> RegOps.regBin op

data DisjItem = DisjDefault VT.Tree | DisjRegular VT.Tree

instance Show DisjItem where
  show (DisjDefault t) = show t
  show (DisjRegular t) = show t

-- reduceDisjPair is used to evaluate a disjunction whose both sides are evaluated.
reduceDisjPair :: (RM.ReduceMonad s r m) => DisjItem -> DisjItem -> m VT.Tree
reduceDisjPair i1 i2 = case (i1, i2) of
  (DisjDefault v1, _) -> do
    logDebugStr $ printf "reduceDisjPair: *: %s, r: %s" (show v1) (show i2)
    t <- reduceLeftDefault (\(df1, ds1, df2, ds2) -> newDisj df1 ds1 df2 ds2) v1 i2
    logDebugStr $ printf "reduceDisjPair: *: %s, r: %s, resulting to:\n%s" (show v1) (show i2) (show t)
    return t
  -- reverse v2 r1 and also the order to the disjCons.
  (DisjRegular _, DisjDefault v2) -> do
    reduceLeftDefault (\(df2, ds2, df1, ds1) -> newDisj df1 ds1 df2 ds2) v2 i1
  (DisjRegular v1, DisjRegular v2) -> do
    logDebugStr $ printf "reduceDisjPair: both regulars v1: %s, v2: %s" (show v1) (show v2)
    r <- reduceRegularDisj v1 v2
    logDebugStr $ printf "reduceDisjPair: both regulars results: %s" (show r)
    return r

-- reduceLeftDefault is used to evaluate a disjunction whose left side is a default.
-- the first argument is a function that takes the four lists of values and returns a disjunction.
reduceLeftDefault ::
  (MonadError String m) =>
  ((Maybe VT.Tree, [VT.Tree], Maybe VT.Tree, [VT.Tree]) -> m VT.Tree) ->
  VT.Tree ->
  DisjItem ->
  m VT.Tree
-- Below is rule M2 and M3. We eliminate the defaults from the right side.
reduceLeftDefault disjCons (VT.Tree{VT.treeNode = VT.TNDisj dj1}) (DisjRegular (VT.Tree{VT.treeNode = VT.TNDisj dj2})) =
  disjCons (VT.dsjDefault dj1, VT.dsjDisjuncts dj1, Nothing, VT.dsjDisjuncts dj2)
-- Below is rule M1.
reduceLeftDefault disjCons v1 (DisjRegular (VT.Tree{VT.treeNode = VT.TNDisj dj2})) =
  disjCons (Just v1, [v1], VT.dsjDefault dj2, VT.dsjDisjuncts dj2)
reduceLeftDefault disjCons v1 (DisjRegular v2) =
  disjCons (Just v1, [v1], Nothing, [v2])
reduceLeftDefault disjCons v1 (DisjDefault v2) =
  disjCons (Nothing, [v1], Nothing, [v2])

-- evalFullDisj is used to evaluate a disjunction whose both sides are regular.
-- Rule: D1, D2
reduceRegularDisj :: (RM.ReduceMonad s r m) => VT.Tree -> VT.Tree -> m VT.Tree
reduceRegularDisj (VT.Tree{VT.treeNode = VT.TNDisj dj1}) (VT.Tree{VT.treeNode = VT.TNDisj dj2}) =
  newDisj (VT.dsjDefault dj1) (VT.dsjDisjuncts dj1) (VT.dsjDefault dj2) (VT.dsjDisjuncts dj2)
reduceRegularDisj (VT.Tree{VT.treeNode = VT.TNDisj dj}) y = newDisj (VT.dsjDefault dj) (VT.dsjDisjuncts dj) Nothing [y]
reduceRegularDisj x (VT.Tree{VT.treeNode = VT.TNDisj dj}) = newDisj Nothing [x] (VT.dsjDefault dj) (VT.dsjDisjuncts dj)
-- Rule D0
reduceRegularDisj x y = newDisj Nothing [x] Nothing [y]

newDisj :: (RM.ReduceMonad s r m) => Maybe VT.Tree -> [VT.Tree] -> Maybe VT.Tree -> [VT.Tree] -> m VT.Tree
newDisj df1 ds1 df2 ds2 =
  if
    | null allTerms -> throwErrSt "both sides of disjunction are empty"
    -- No non-bottoms exist
    | null filteredTerms -> return $ head allTerms
    -- the disjunction of a value a with bottom is always a.
    | length filteredTerms == 1 -> return $ head filteredTerms
    -- two or more non-bottom terms exist.
    | otherwise -> return $ VT.mkDisjTree (defaultFrom $ filterBtms defaults) (filterBtms disjuncts)
 where
  defaults :: [VT.Tree]
  defaults = catMaybes [df1, df2]

  defaultFrom :: [VT.Tree] -> Maybe VT.Tree
  defaultFrom xs = case xs of
    [x] -> Just x
    -- If there are more than one defaults, then defaults become disjuncts.
    [x, y] -> Just $ VT.mkDisjTree Nothing [x, y]
    _ -> Nothing

  -- The first element is non-bottom.
  -- The second element is a bottom.
  disjuncts :: [VT.Tree]
  disjuncts = dedupAppend ds1 ds2

  filterBtms :: [VT.Tree] -> [VT.Tree]
  filterBtms = filter (not . isTreeBottom)

  allTerms :: [VT.Tree]
  allTerms = defaults ++ disjuncts

  filteredTerms :: [VT.Tree]
  filteredTerms = filterBtms allTerms

  -- dedupAppend appends unique elements in ys to the xs list, but only if they are not already in xs.
  -- xs and ys are guaranteed to be unique.
  dedupAppend :: [VT.Tree] -> [VT.Tree] -> [VT.Tree]
  dedupAppend xs ys = xs ++ foldr (\y acc -> if y `elem` xs then acc else y : acc) [] ys

-- built-in functions
builtinMutableTable :: [(String, VT.Tree)]
builtinMutableTable =
  [
    ( "close"
    , VT.mkMutableTree . VT.SFunc $
        -- built-in close does not recursively close the struct.
        VT.emptySFunc
          { VT.sfnName = "close"
          , VT.sfnArgs = [VT.mkNewTree VT.TNTop]
          , VT.sfnMethod = close
          }
    )
  ]

-- | Closes a struct when the tree has struct.
close :: (RM.ReduceMonad s r m) => [VT.Tree] -> m ()
close args
  | length args /= 1 = throwErrSt $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      let a = head args
      r <- Mutate.reduceMutableArg Path.unaryOpTASeg a
      case VT.treeNode r of
        -- If the argument is pending, wait for the result.
        VT.TNMutable _ -> return ()
        _ -> RM.putRMTree $ closeTree r

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
    _ -> a
