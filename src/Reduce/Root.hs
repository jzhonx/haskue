{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Root where

import qualified AST
import Common (
  BuildASTExpr (buildASTExpr),
  TreeOp (isTreeBottom),
 )
import Control.Monad (foldM, unless, when)
import Control.Monad.Except (MonadError)
import Control.Monad.State.Strict (gets)
import Cursor (
  Context (Context, ctxReduceStack),
 )
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified Reduce.RegOps as RegOps
import qualified Reduce.UnifyOp as UnifyOp
import Text.Printf (printf)
import Util (
  HasTrace (getTrace),
  Trace (traceID),
  debugSpan,
  logDebugStr,
 )
import qualified Value.Tree as VT

fullReduce :: (RM.ReduceMonad s r m) => m ()
fullReduce = RM.withAddrAndFocus $ \addr _ -> debugSpan (printf "fullReduce, addr: %s" (show addr)) $ do
  reduce
  RefSys.drainRefSysQueue

-- | Reduce the tree to the lowest form.
reduce :: (RM.ReduceMonad s r m) => m ()
reduce = RM.withAddrAndFocus $ \addr _ -> debugSpan (printf "reduce, addr: %s" (show addr)) $ do
  RM.treeDepthCheck
  push addr

  tr <- gets getTrace
  let trID = traceID tr
  RM.dumpEntireTree $ printf "reduce id=%s start" (show trID)

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
  -- Only notify dependents when we are not in a temporary node.
  if (Path.isTreeAddrAccessible addr && notifyEnabled)
    then (RM.addToRMRefSysQ $ Path.referableAddr addr)
    else logDebugStr $ printf "reduce, addr: %s, not accessible or not enabled" (show addr)

  pop
  RM.dumpEntireTree $ printf "reduce id=%s done" (show trID)
 where
  push addr = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}

  pop = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}

-- ###
-- Reduce tree nodes
-- ###

reduceStruct :: forall s r m. (RM.ReduceMonad s r m) => m ()
reduceStruct = do
  -- Close the struct if the tree is closed.
  RM.mustStruct $ \s -> do
    closed <- VT.treeRecurClosed <$> RM.getRMTree
    when closed $
      -- Use RM.modifyRMTN instead of VT.mkNewTree because tree attributes need to be preserved, such as VT.treeRecurClosed.
      RM.modifyRMTN (VT.TNStruct $ s{VT.stcClosed = True})

  whenStruct () $ \s -> mapM_ validateLetName (Map.keys $ VT.stcLets s)

  -- reduce the dynamic fields first. If the dynfields become actual fields, later they will be reduced.
  whenStruct () $ \s ->
    foldM
      ( \_ (i, pend) ->
          -- Inserting reduced pending element into the struct is handled by propUpStructPost.
          RM.inSubRM (Path.StructTASeg (Path.PendingTASeg i 0)) (VT.dsfLabel pend) reduce
      )
      ()
      (IntMap.toList $ VT.stcPendSubs s)

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

  -- Reduce all fields
  whenStruct () $ \s -> do
    mapM_ (reduceStructField . fst) (Map.toList . VT.stcFields $ s)
    RM.withAddrAndFocus $ \addr t ->
      logDebugStr $ printf "reduceStruct: addr: %s, new struct: %s" (show addr) (show t)

whenStruct :: (RM.ReduceMonad s r m) => a -> (VT.Struct VT.Tree -> m a) -> m a
whenStruct a f = do
  t <- RM.getRMTree
  case VT.treeNode t of
    VT.TNBottom _ -> return a
    VT.TNStruct struct -> f struct
    _ -> do
      RM.putRMTree . VT.mkBottomTree $ printf "%s is not a struct" (show t)
      return a

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
propUpStructPost (Path.PendingTASeg i _, _struct) = RM.withAddrAndFocus $ \p _ ->
  debugSpan (printf "propUpStructPost_dynamic, addr: %s" (show p)) $ do
    let dsf = VT.stcPendSubs _struct IntMap.! i
    either
      RM.modifyRMNodeWithTree
      ( \(struct, fieldM) -> do
          -- Constrain the new field with all existing constraints.
          (newStruct, matchedSegs) <-
            maybe
              (return (struct, []))
              ( \(name, field) -> do
                  (items, matchedSegs) <- do
                    let allCnstrsWithIdx = IntMap.toList $ VT.stcCnstrs struct
                    (newSub, matchedCnstrs) <- constrainField name (VT.ssfValue field) allCnstrsWithIdx
                    return
                      ( [(name, newSub, matchedCnstrs)]
                      , if not (null matchedCnstrs) then [name] else []
                      )
                  return (updateFieldsWithAppliedCnstrs struct items, matchedSegs)
              )
              fieldM
          RM.withAddrAndFocus $ \addr _ ->
            logDebugStr $
              printf
                "propUpStructPost_dynamic: addr: %s, new struct: %s, matchedSegs: %s"
                (show addr)
                (show $ VT.mkStructTree newStruct)
                (show matchedSegs)
          RM.modifyRMNodeWithTree (VT.mkStructTree newStruct)

          -- Check the permission of the label of newly created field.
          whenStruct () $ \s -> checkNewLabelPerm s (Path.PendingTASeg i 0)

          -- Reduce the updated struct value, which is the new field, if it is matched with any constraints.
          whenStruct () $ \_ -> mapM_ reduceStructField matchedSegs
      )
      (updateStructPend _struct dsf)
propUpStructPost (Path.PatternTASeg i _, struct) = RM.withAddrAndFocus $ \p _ ->
  debugSpan (printf "propUpStructPost_constraint, addr: %s, idx: %s" (show p) (show i)) $ do
    -- Constrain all fields with the new constraint if it exists.
    let
      prevMatchedNames = matchedByCnstr i (getSFieldPairs struct)
      cnstr = VT.stcCnstrs struct IntMap.! i
    newMatchedNames <- filterMatchedNames cnstr (map fst $ getSFieldPairs struct)
    -- New constraint might have the following effect:
    -- A. It matches fewer fields than the previous constraint with narrower constraints.
    -- -----
    -- abcde
    --   +++
    -- In the above example, we need to do
    -- 1. Remove the constraint for a,b
    -- 2. Do nothing for c,d,e
    --
    -- B. It could also match more fields when the constraint just got reduced to a pattern.
    let
      removedNames = Set.fromList prevMatchedNames `Set.difference` Set.fromList newMatchedNames
      addedNames = Set.fromList newMatchedNames `Set.difference` Set.fromList prevMatchedNames

    removedItems <-
      removeAppliedCnstr
        i
        (IntMap.toList $ VT.stcCnstrs struct)
        (filter (\(seg, _) -> seg `Set.member` removedNames) (getSFieldPairs struct))

    addedItems <-
      applyMoreCnstr
        (i, cnstr)
        (filter (\(seg, _) -> seg `Set.member` addedNames) (getSFieldPairs struct))
    let newStruct = updateFieldsWithAppliedCnstrs struct (removedItems ++ addedItems)
    RM.modifyRMNodeWithTree (VT.mkStructTree newStruct)

    let affectedLabels = Set.toList removedNames ++ Set.toList addedNames

    unless (null affectedLabels) $
      RM.withAddrAndFocus $ \addr _ ->
        logDebugStr $
          printf
            ( "propUpPendStructPost_constraint: addr: %s, diff_items, -ns: %s, +ns: %s, "
                ++ "-items: %s, +items: %s, new struct: %s"
            )
            (show addr)
            (show $ Set.toList removedNames)
            (show $ Set.toList addedNames)
            (show removedItems)
            (show addedItems)
            (show $ VT.mkStructTree newStruct)

    whenStruct () $ \s -> checkNewPatternPerm s (Path.PatternTASeg i 0)

    -- Reduce the updated struct values.
    whenStruct () $ \_ -> mapM_ reduceStructField affectedLabels

    RM.withTree $ \t ->
      logDebugStr $ printf "propUpPendStructPost_constraint: new value: %s" (show t)
 where
  --
  matchedByCnstr :: Int -> [(String, VT.Field VT.Tree)] -> [String]
  matchedByCnstr j = foldr (\(k, field) acc -> if j `elem` VT.ssfCnstrs field then k : acc else acc) []
propUpStructPost (_, _) = return ()

getSFieldPairs :: VT.Struct VT.Tree -> [(String, VT.Field VT.Tree)]
getSFieldPairs struct = Map.toList $ VT.stcFields struct

{- | Update the struct with the reduced pending element.

It returns the new struct and a pair, containing reduced string and the newly created/updated field.
-}
updateStructPend ::
  VT.Struct VT.Tree ->
  VT.DynamicField VT.Tree ->
  Either VT.Tree (VT.Struct VT.Tree, Maybe (String, VT.Field VT.Tree))
updateStructPend struct df = case VT.treeNode label of
  VT.TNBottom _ -> Left label
  VT.TNMutable mut
    -- TODO: atom can become bottom or not found.
    | Just (VT.TNAtom (VT.AtomV (VT.String s))) <- VT.treeNode <$> VT.getMutVal mut -> updateLabel s
    -- Incomplete field label, no change is made. If the mutable was a reference with string value, then it would
    -- have been reduced to a string.
    | otherwise -> return (struct, Nothing)
  VT.TNAtom (VT.AtomV (VT.String s)) -> updateLabel s
  _ -> Left (VT.mkBottomTree "label can only be a string")
 where
  label = VT.dsfLabel df
  updateLabel s =
    let
      unifier l r = VT.mkMutableTree $ mkUnifyNode l r
      newSF = VT.dynToField df (VT.lookupStructField s struct) unifier
     in
      return (VT.convertPendDyn struct s newSF, Just (s, newSF))

{- | Apply pattern constraints ([pattern]: constraint) to the static field.

Returns the new field and the indexes of the constraints that are matched with the field.
-}
constrainField :: (RM.ReduceMonad s r m) => String -> VT.Tree -> [(Int, VT.StructCnstr VT.Tree)] -> m (VT.Tree, [Int])
constrainField name field =
  foldM
    ( \(accField, accMatchedIdxes) (i, cnstr) -> do
        (newField, isMatched) <- bindFieldWithCnstr name accField cnstr
        return (newField, if isMatched then i : accMatchedIdxes else accMatchedIdxes)
    )
    (field, [])

{- | Bind the pattern constraint ([pattern]: constraint) to the static field if the field name matches the pattern.

Return the new unify node, which is constraint & field, if the field name matches the pattern. Otherwise, return the
field. The boolean indicates if the field is matched with the pattern.

It can run in any kind of node.
-}
bindFieldWithCnstr :: (RM.ReduceMonad s r m) => String -> VT.Tree -> VT.StructCnstr VT.Tree -> m (VT.Tree, Bool)
bindFieldWithCnstr name fval psf = do
  let selPattern = VT.scsPattern psf

  matched <- UnifyOp.patMatchLabel selPattern name
  logDebugStr $ printf "bindFieldWithCnstr: %s with %s, matched: %s" name (show selPattern) (show matched)

  let op = VT.mkMutableTree $ mkUnifyNode fval (VT.mkCnstredValTree (VT.scsValue psf) Nothing)
  return
    ( if matched
        then op
        else fval
    , matched
    )

mkUnifyNode :: VT.Tree -> VT.Tree -> VT.Mutable VT.Tree
mkUnifyNode = VT.mkBinaryOp AST.Unify UnifyOp.unify

{- | Update the struct field with the cnstr items.

If the cnstr items introduce new fields that are not in the struct, then they are ignored.
-}
updateFieldsWithAppliedCnstrs :: VT.Struct VT.Tree -> [(String, VT.Tree, [Int])] -> VT.Struct VT.Tree
updateFieldsWithAppliedCnstrs struct =
  foldr
    ( \(name, val, matchedCnstrs) acc ->
        maybe
          acc
          ( \field -> VT.updateStructField name (field{VT.ssfValue = val, VT.ssfCnstrs = matchedCnstrs}) acc
          )
          (VT.lookupStructField name struct)
    )
    struct

-- | Filter the names that are matched with the constraint's pattern.
filterMatchedNames :: (RM.ReduceMonad s r m) => VT.StructCnstr VT.Tree -> [String] -> m [String]
filterMatchedNames cnstr =
  foldM
    ( \acc name -> do
        matched <- UnifyOp.patMatchLabel (VT.scsPattern cnstr) name
        return $ if matched then name : acc else acc
    )
    []

{- | Remove the applied constraint from the fields.

The constraint must have been applied to the fields.

This is done by re-applying existing constraints except the one that is removed.
-}
removeAppliedCnstr ::
  (RM.ReduceMonad s r m) =>
  Int ->
  [(Int, VT.StructCnstr VT.Tree)] ->
  [(String, VT.Field VT.Tree)] ->
  m [(String, VT.Tree, [Int])]
removeAppliedCnstr delIdx allCnstrs subs = do
  foldM
    ( \accSubs (name, field) -> do
        let
          updatedIdxes = filter (/= delIdx) (VT.ssfCnstrs field)
          updatedCnstrs = filter (\(i, _) -> i `elem` updatedIdxes) allCnstrs
          fval = VT.ssfValue field
        raw <-
          maybe (buildASTExpr False fval) return (VT.treeExpr fval)
            >>= RefSys.evalExprRM
        logDebugStr $ printf "removeAppliedCnstr: %s, updatedIdxes: %s, raw: %s" name (show updatedIdxes) (show raw)
        (newSub, matchedCnstrs) <- constrainField name raw updatedCnstrs
        return $ (name, newSub, matchedCnstrs) : accSubs
    )
    []
    subs

-- | Apply the additional constraint to the fields.
applyMoreCnstr ::
  (RM.ReduceMonad s r m) =>
  (Int, VT.StructCnstr VT.Tree) ->
  [(String, VT.Field VT.Tree)] ->
  m [(String, VT.Tree, [Int])]
applyMoreCnstr (i, cnstr) =
  mapM
    ( \(name, field) -> do
        (nv, _) <- bindFieldWithCnstr name (VT.ssfValue field) cnstr
        return (name, nv, VT.ssfCnstrs field ++ [i])
    )

checkNewLabelPerm :: (RM.ReduceMonad s r m) => VT.Struct VT.Tree -> Path.StructTASeg -> m ()
checkNewLabelPerm struct (Path.PendingTASeg i 0) =
  let perms = VT.getPermInfoForDyn struct i
   in mapM_ (validatePermItem struct) perms
checkNewLabelPerm _ opLabel = throwErrSt $ printf "invalid opLabel %s" (show opLabel)

checkNewPatternPerm :: (RM.ReduceMonad s r m) => VT.Struct VT.Tree -> Path.StructTASeg -> m ()
checkNewPatternPerm struct (Path.PatternTASeg i 0) =
  let perms = VT.getPermInfoForPattern struct i
   in mapM_ (validatePermItem struct) perms
checkNewPatternPerm _ opLabel = throwErrSt $ printf "invalid opLabel %s" (show opLabel)

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
                VT.getStringFromTree (VT.dsfLabel $ VT.stcPendSubs struct IntMap.! i)
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
