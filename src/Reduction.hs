{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Reduction where

import qualified AST
import Class
import Config
import Control.Monad (foldM, forM, unless, when)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (asks, local)
import Control.Monad.State.Strict (gets)
import Cursor
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust)
import qualified Data.Set as Set
import Error
import Mutate
import Path
import Ref
import TMonad
import Text.Printf (printf)
import Util
import Value.Tree

fullReduce :: (TreeMonad s m) => m ()
fullReduce = withAddrAndFocus $ \addr _ -> debugSpan (printf "fullReduce, addr: %s" (show addr)) $ do
  reduce
  drainNotifQueue

-- | Reduce the tree to the lowest form.
reduce :: (TreeMonad s m) => m ()
reduce = withAddrAndFocus $ \addr _ -> debugSpan (printf "reduce, addr: %s" (show addr)) $ do
  treeDepthCheck
  push addr

  tr <- gets getTrace
  let trID = traceID tr
  dumpEntireTree $ printf "reduce id=%s start" (show trID)

  -- save the original tree before effects are applied to the focus of the tree.
  orig <- getTMTree
  withTree $ \t -> case treeNode t of
    TNMutable _ -> mutate
    TNStruct _ -> reduceStruct
    TNList _ -> traverseSub reduce
    TNDisj _ -> traverseSub reduce
    TNStructuralCycle _ -> putTMTree $ mkBottomTree "structural cycle"
    _ -> return ()

  -- Overwrite the treenode of the raw with the reduced tree's TreeNode to preserve tree attributes.
  withTree $ \t -> putTMTree $ setTN orig (treeNode t)

  notifyEnabled <- getTMNotifEnabled
  -- Only notify dependents when we are not in a temporary node.
  when (isTreeAddrAccessible addr && notifyEnabled) (addToTMNotifQ $ referableAddr addr)

  pop
  dumpEntireTree $ printf "reduce id=%s done" (show trID)
 where
  push addr = modifyTMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}

  pop = modifyTMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}

-- | Only reduce the tree to the first level.
shallowReduce :: (TreeMonad s m) => m ()
shallowReduce = withAddrAndFocus $ \addr _ -> debugSpan (printf "shallowReduce, addr: %s" (show addr)) $ do
  -- save the original tree before effects are applied to the focus of the tree.
  orig <- getTMTree
  withTree $ \t -> case treeNode t of
    TNMutable _ -> local (\r -> r{cfFunctions = (cfFunctions r){fnReduce = shallowReduce}}) mutate
    _ -> return ()

  -- Overwrite the treenode of the raw with the reduced tree's TreeNode to preserve tree attributes.
  withTree $ \t -> putTMTree $ setTN orig (treeNode t)

-- ###
-- Reduce tree nodes
-- ###

reduceAtomOpArg :: (TreeMonad s m) => TASeg -> Tree -> m (Maybe Tree)
reduceAtomOpArg seg sub =
  reduceMutableArgMaybe
    seg
    sub
    ( \rM -> case rM of
        Nothing -> Nothing
        Just r ->
          if isMutableTreeReducible sub r
            then rM
            else Nothing
    )

reduceMutableArg :: (TreeMonad s m) => TASeg -> Tree -> m Tree
reduceMutableArg seg sub = withTree $ \t -> do
  ret <- reduceMutableArgMaybe seg sub (Just . fromMaybe t)
  return $ fromJust ret

{- | Evaluate the argument of the given mutable.

Notice that if the argument is a mutable and the mutval, such as struct or disjunction, is not
reducible, the value is still returned because the parent mutable needs the value.
-}
reduceMutableArgMaybe ::
  (TreeMonad s m) =>
  TASeg ->
  Tree ->
  (Maybe Tree -> Maybe Tree) ->
  m (Maybe Tree)
reduceMutableArgMaybe seg sub csHandler = withAddrAndFocus $ \addr _ ->
  debugSpan (printf "reduceMutableArgMaybe, addr: %s, seg: %s" (show addr) (show seg)) $
    -- We are currently in the Mutable's val field. We need to go up to the Mutable.
    mutValToArgsTM
      seg
      sub
      ( do
          Functions{fnReduce = _reduce} <- asks cfFunctions
          _reduce
          withTree $ \x -> return $ case treeNode x of
            TNMutable mut -> csHandler (getMutVal mut)
            _ -> Just x
      )

{- | Go to the parent mutable and run the action in an argument environment, then come back to the mutval environment.

The mutable must see changes propagated from the argument environment.
-}
mutValToArgsTM :: (TreeMonad s m) => TASeg -> Tree -> m a -> m a
mutValToArgsTM subSeg sub f = doInMutTM $ mustMutable $ \_ -> inSubTM subSeg sub f
 where
  -- Run the action in the parent tree. All changes will be propagated to the parent tree and back to the current
  -- tree. After evaluating the argument environment, the focus of the tree should still be the mutable.
  doInMutTM :: (TreeMonad s m) => m a -> m a
  doInMutTM action = do
    seg <- getTMTASeg
    propUpTM
    r <- action
    ok <- descendTMSeg seg
    unless ok $ throwErrSt $ printf "failed to go down with seg %s" (show seg)
    return r

-- | Reduce the struct.
reduceStruct :: forall s m. (TreeMonad s m) => m ()
reduceStruct = do
  -- Close the struct if the tree is closed.
  mustStruct $ \s -> do
    closed <- treeRecurClosed <$> getTMTree
    when closed $
      putTMTree (mkStructTree $ s{stcClosed = True})

  -- reduce the dynamic fields first. If the dynfields become actual fields, later they will be reduced.
  whenStruct () $ \s ->
    foldM
      ( \acc (i, pendM) ->
          maybe
            (return acc)
            ( \pend ->
                -- Inserting reduced pending element into the struct is handled by propUpStructPost.
                inSubTM (StructTASeg (PendingTASeg i)) (dsfLabel pend) reduce
            )
            pendM
      )
      ()
      (zip [0 ..] (stcPendSubs s))

  whenStruct () $ \s ->
    foldM
      ( \_ (i, cnstr) ->
          -- pattern value should never be reduced because the references inside the pattern value should only be
          -- resolved in the unification node of the static field.
          -- See unify for more details.
          -- reduced constraint will constrain fields, which is done in the propUpStructPost.
          inSubTM (StructTASeg (PatternTASeg i)) (scsPattern cnstr) reduce
      )
      ()
      (zip [0 ..] (stcCnstrs s))

  -- Reduce all subs
  whenStruct () $ \s ->
    if allCnstrsReady s
      then do
        mapM_ (reduceStructVal . fst) (Map.toList . stcSubs $ s)
        withAddrAndFocus $ \addr t ->
          logDebugStr $ printf "reduceStruct: addr: %s, new struct: %s" (show addr) (show t)
      else withAddrAndFocus $ \addr _ ->
        logDebugStr $ printf "reduceStruct: addr: %s, not all constraints are ready" (show addr)

allCnstrsReady :: Struct Tree -> Bool
allCnstrsReady Struct{stcCnstrs = cnstrs} = all isPatternReady cnstrs
 where
  isPatternReady (StructCnstr{scsPattern = pat}) = case treeNode pat of
    TNMutable mut
      | Nothing <- getMutVal mut -> False
      -- If the mutable is a reference and it currently has stub value.
      | Just (TNMutable MutStub) <- treeNode <$> getMutVal mut -> False
    _ -> True

whenStruct :: (TreeMonad s m) => a -> (Struct Tree -> m a) -> m a
whenStruct a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    TNStruct struct -> f struct
    _ -> do
      putTMTree . mkBottomTree $ printf "%s is not a struct" (show t)
      return a

reduceStructVal :: (TreeMonad s m) => StructTASeg -> m ()
reduceStructVal seg@(getStrFromSeg -> Just name) = whenStruct () $ \struct -> do
  (sub, foundLet) <-
    maybe
      (throwErrSt $ printf "%s is not found" (show seg))
      return
      (lookupStructVal name struct >>= getSubFromSV)

  -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make sure
  -- in the parent scope that there is no field with the same name.
  parResM <- searchTMVarInPar name
  structAddr <- getTMAbsAddr
  let letAddr = appendSeg (StructTASeg seg) structAddr
  logDebugStr $
    printf
      "reduceStructVal: addr: %s, lbaddr: %s, var %s in parent: %s"
      (show structAddr)
      (show letAddr)
      name
      (show parResM)
  case parResM of
    -- If the let binding with the name is found in the scope.
    Just (targetAddr, True)
      -- The case of the same let bindings or same let binding and field identifier has already checked in the evalExpr
      -- phase. If both addrs are equal, it just means it is the current let binding.
      | letAddr /= targetAddr -> putTMTree $ if foundLet then lbRedeclErr else aliasErr
    -- If the field with the name is found in the scope.
    Just (_, False)
      | foundLet -> putTMTree aliasErr
    -- If there is no conflict, then reduce the sub.
    _ -> reduceInStructSub seg sub
 where
  aliasErr = mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name
  lbRedeclErr = mkBottomTree $ printf "%s redeclared in same scope" name
reduceStructVal seg = throwErrSt $ printf "invalid segment %s" (show seg)

reduceInStructSub :: (TreeMonad s m) => StructTASeg -> Tree -> m ()
reduceInStructSub seg sub = do
  -- The segment should be a struct segment.
  whenStruct () $ \_ -> do
    inSubTM (StructTASeg seg) sub reduce

-- | Handle the post process of propagating value into struct.
propUpStructPost :: (TreeMonad s m) => (StructTASeg, Struct Tree) -> m ()
propUpStructPost (PendingTASeg i, _struct) = withAddrAndFocus $ \p _ ->
  debugSpan (printf "propUpStructPost_dynamic, addr: %s" (show p)) $ do
    dsf <- maybe (throwErrSt "pending element has been deleted") return (stcPendSubs _struct !! i)
    either
      putTMTree
      ( \(struct, fieldM) -> do
          -- Constrain the new field with all existing constraints.
          (newStruct, matchedSegs) <-
            maybe
              (return (struct, []))
              ( \(name, field) -> do
                  (items, matchedSegs) <- do
                    let allCnstrsWithIdx = zip [0 ..] (stcCnstrs struct)
                    (newSub, matchedCnstrs) <- constrainField name (ssfValue field) allCnstrsWithIdx
                    return
                      ( [(name, newSub, matchedCnstrs)]
                      , if not (null matchedCnstrs) then [StringTASeg name] else []
                      )
                  return (updateStructWithCnstrItems struct items, matchedSegs)
              )
              fieldM
          withAddrAndFocus $ \addr _ ->
            logDebugStr $
              printf
                "propUpPendStructPost_dynamic: addr: %s, new struct: %s, matchedSegs: %s"
                (show addr)
                (show $ mkStructTree newStruct)
                (show matchedSegs)
          putTMTree (mkStructTree newStruct)

          -- Reduce the updated struct values.
          whenStruct () $ \_ -> mapM_ reduceStructVal matchedSegs
      )
      (updateStructDynamicPend _struct i dsf)
propUpStructPost (PatternTASeg i, struct) = withAddrAndFocus $ \p _ ->
  debugSpan (printf "propUpStructPost_constraint, addr: %s, idx: %s" (show p) (show i)) $ do
    -- Constrain all fields with the new constraint if it exists.
    let
      prevMatchedNames = matchedByCnstr i (getSFieldPairs struct)
      cnstr = stcCnstrs struct !! i
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
        (stcCnstrs struct)
        (filter (\(seg, _) -> seg `Set.member` removedNames) (getSFieldPairs struct))

    addedItems <-
      applyMoreCnstr
        (i, cnstr)
        (filter (\(seg, _) -> seg `Set.member` addedNames) (getSFieldPairs struct))
    let newStruct = updateStructWithCnstrItems struct (removedItems ++ addedItems)
    putTMTree (mkStructTree newStruct)

    let affectedSegs = map StringTASeg $ Set.toList removedNames ++ Set.toList addedNames

    unless (null affectedSegs) $
      withAddrAndFocus $ \addr _ ->
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
            (show $ mkStructTree newStruct)

    -- Reduce the updated struct values.
    whenStruct () $ \_ -> mapM_ reduceStructVal affectedSegs
    withTree $ \t ->
      logDebugStr $ printf "propUpPendStructPost_constraint: new value: %s" (show t)
 where
  --
  matchedByCnstr :: Int -> [(String, Field Tree)] -> [String]
  matchedByCnstr j = foldr (\(k, field) acc -> if j `elem` ssfCnstrs field then k : acc else acc) []
propUpStructPost (_, _) = return ()

getSFieldPairs :: Struct Tree -> [(String, Field Tree)]
getSFieldPairs struct =
  foldr
    ( \(k, sv) acc -> case ( do
                              name <- getStrFromSeg k
                              f <- getFieldFromSV sv
                              return (name, f)
                           ) of
        Just p -> p : acc
        _ -> acc
    )
    []
    (Map.toList $ stcSubs struct)

mustStruct :: (TreeMonad s m) => (Struct Tree -> m a) -> m a
mustStruct f = withTree $ \t -> case treeNode t of
  TNStruct struct -> f struct
  _ -> throwErrSt $ printf "%s is not a struct" (show t)

{- | Update the struct with the reduced pending element.

It returns the new struct and a boolean indicating if the label is reduced to a string.
-}
updateStructDynamicPend ::
  Struct Tree ->
  Int ->
  DynamicField Tree ->
  Either Tree (Struct Tree, Maybe (String, Field Tree))
updateStructDynamicPend struct i dsf =
  let sub = dsfLabel dsf
   in case treeNode sub of
        TNBottom _ -> Left sub
        -- Incomplete field label, no change is made. If the mutable was a reference with string value, then it would
        -- have been reduced to a string.
        TNMutable _ -> return (struct, Nothing)
        TNAtom (AtomV (String s)) ->
          let
            unifier l r = mkMutableTree $ mkUnifyNode l r
            newSF = dynToField dsf (lookupStructVal s struct) unifier
           in
            return (markPendDeleted i $ addStructField struct s newSF, Just (s, newSF))
        _ -> Left (mkBottomTree "label can only be a string")

{- | Apply pattern constraints ([pattern]: constraint) to the static field.

Returns the new field and the indexes of the constraints that are matched with the field.
-}
constrainField :: (TreeMonad s m) => String -> Tree -> [(Int, StructCnstr Tree)] -> m (Tree, [Int])
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
bindFieldWithCnstr :: (TreeMonad s m) => String -> Tree -> StructCnstr Tree -> m (Tree, Bool)
bindFieldWithCnstr name fval psf = do
  let selPattern = scsPattern psf

  matched <- patMatchLabel selPattern name
  logDebugStr $ printf "bindFieldWithCnstr: %s with %s, matched: %s" name (show selPattern) (show matched)

  let op = mkMutableTree $ mkUnifyNode fval (scsValue psf)
  fieldExpr <- maybe (buildASTExpr False fval) return (treeExpr fval)
  return
    ( if matched
        then op{treeNonCnstrExpr = Just fieldExpr}
        else fval
    , matched
    )

-- | Returns whether the pattern matches the label.
patMatchLabel :: (TreeMonad s m) => Tree -> String -> m Bool
patMatchLabel pat name = case treeNode pat of
  TNMutable mut ->
    maybe
      (return False)
      ( -- The lable mutable might be a reference. The pending element should not be marked as deleted.
        \val -> case treeNode val of
          -- If the mutable is a reference and it currently has no value.
          TNMutable MutStub -> return False
          _ -> match val
      )
      (getMutVal mut)
  _ -> match pat
 where
  match v = do
    let
      segOp = mkMutableTree $ mkUnifyNode (mkAtomTree $ String name) v
    -- Since segOps a list of unify nodes that unify the string with the bounds, we can use inDiscardSubTM to
    -- evaluate the unify nodes and get the strings.
    r <- inDiscardSubTM TempTASeg segOp (reduce >> getTMTree)
    -- Filter the strings from the results. Non-string results are ignored meaning the fields do not match the
    -- pattern.
    case treeNode r of
      TNAtom (AtomV (String _)) -> return True
      _ -> return False

{- | Update the struct with the cnstr items.

If the cnstr items introduce new fields that are not in the struct, then the new fields are ignored.
-}
updateStructWithCnstrItems :: Struct Tree -> [(String, Tree, [Int])] -> Struct Tree
updateStructWithCnstrItems struct =
  foldr
    ( \(name, v, matchedCnstrs) acc ->
        let seg = StringTASeg name
         in maybe
              acc
              (\field -> updateStructSub seg (SField field{ssfValue = v, ssfCnstrs = matchedCnstrs}) acc)
              (lookupStructVal name struct >>= getFieldFromSV)
    )
    struct

-- | Filter the names that are matched with the constraint's pattern.
filterMatchedNames :: (TreeMonad s m) => StructCnstr Tree -> [String] -> m [String]
filterMatchedNames cnstr =
  foldM
    ( \acc name -> do
        matched <- patMatchLabel (scsPattern cnstr) name
        return $ if matched then name : acc else acc
    )
    []

{- | Remove the applied constraint from the fields.

The constraint must have been applied to the fields.

This is done by re-applying existing constraints except the one that is removed.
-}
removeAppliedCnstr ::
  (TreeMonad s m) =>
  Int ->
  [StructCnstr Tree] ->
  [(String, Field Tree)] ->
  m [(String, Tree, [Int])]
removeAppliedCnstr delIdx allCnstrs subs = do
  foldM
    ( \accSubs (name, field) -> do
        let
          updatedIdxes = filter (/= delIdx) (ssfCnstrs field)
          updatedCnstrs = filter (\(i, _) -> i `elem` updatedIdxes) (zip [0 ..] allCnstrs)
          fval = ssfValue field
        raw <-
          maybe (throwErrSt "non-constrained expression is not found") return (treeNonCnstrExpr fval)
            >>= evalExprTM
        logDebugStr $ printf "removeAppliedCnstr: %s, updatedIdxes: %s, raw: %s" name (show updatedIdxes) (show raw)
        (newSub, matchedCnstrs) <- constrainField name raw updatedCnstrs
        return $ (name, newSub, matchedCnstrs) : accSubs
    )
    []
    subs

-- | Apply the additional constraint to the fields.
applyMoreCnstr ::
  (TreeMonad s m) =>
  (Int, StructCnstr Tree) ->
  [(String, Field Tree)] ->
  m [(String, Tree, [Int])]
applyMoreCnstr (i, cnstr) =
  mapM
    ( \(name, field) -> do
        (nv, _) <- bindFieldWithCnstr name (ssfValue field) cnstr
        return (name, nv, ssfCnstrs field ++ [i])
    )

-- | Create a new identifier reference.
mkVarLinkTree :: (MonadError String m) => String -> m Tree
mkVarLinkTree var = do
  let mut = mkRefMutable (Path.Reference [StringSel var])
  return $ mkMutableTree mut

{- | Index the tree with the segments.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
index :: (TreeMonad s m) => Maybe (TreeAddr, TreeAddr) -> [Tree] -> m ()
index origAddrsM ts@(t : _)
  | length ts > 1 = do
      idxRefM <- treesToRef <$> mapM evalIndexArg [1 .. length ts - 1]
      logDebugStr $ printf "index: idxRefM is reduced to %s" (show idxRefM)
      whenJustE idxRefM $ \idxRef -> case treeNode t of
        TNMutable mut
          -- If the function is a ref, then we should append the addr to the ref. For example, if the ref is a.b, and
          -- the addr is c, then the new ref should be a.b.c.
          | (Ref ref) <- mut -> do
              let
                newRef = appendRefs (refPath ref) idxRef
                -- Use the index's original addrs since it is the referable node
                refMutable = Ref $ ref{refPath = newRef, refOrigAddrs = origAddrsM}
              putTMTree (mkMutableTree refMutable)
        -- in-place expression, like ({}).a, or regular functions.
        _ -> do
          res <- reduceMutableArg (MutableTASeg $ MutableArgTASeg 0) t
          putTMTree res
          logDebugStr $ printf "index: tree is reduced to %s" (show res)

          unlessFocusBottom () $ do
            -- descendTM can not be used here because it would change the tree cursor.
            tc <- getTMCursor
            maybe
              (throwErrSt $ printf "%s is not found" (show idxRef))
              (putTMTree . vcFocus)
              (goDownTCAddr (refToAddr idxRef) tc)

            withAddrAndFocus $ \_ r -> logDebugStr $ printf "index: the indexed is %s" (show r)
 where
  evalIndexArg :: (TreeMonad s m) => Int -> m Tree
  evalIndexArg i = mutValToArgsTM (MutableTASeg $ MutableArgTASeg i) (ts !! i) (reduce >> getTMTree)

  whenJustE :: (Monad m) => Maybe a -> (a -> m ()) -> m ()
  whenJustE m f = maybe (return ()) f m
index _ _ = throwErrSt "invalid index arguments"

dispUnaryOp :: (TreeMonad s m) => AST.UnaryOp -> Tree -> m ()
dispUnaryOp op _t = do
  tM <- reduceAtomOpArg unaryOpTASeg _t
  case tM of
    Just t -> case treeNode t of
      TNAtom ta -> case (op, amvAtom ta) of
        (AST.Plus, Int i) -> ia i id
        (AST.Plus, Float i) -> fa i id
        (AST.Minus, Int i) -> ia i negate
        (AST.Minus, Float i) -> fa i negate
        (AST.Not, Bool b) -> putTMTree (mkAtomTree (Bool (not b)))
        (AST.UnaRelOp uop, _) -> case (uop, amvAtom ta) of
          (AST.NE, a) -> mkb (BdNE a)
          (AST.LT, Int i) -> mkib BdLT i
          (AST.LT, Float f) -> mkfb BdLT f
          (AST.LE, Int i) -> mkib BdLE i
          (AST.LE, Float f) -> mkfb BdLE f
          (AST.GT, Int i) -> mkib BdGT i
          (AST.GT, Float f) -> mkfb BdGT f
          (AST.GE, Int i) -> mkib BdGE i
          (AST.GE, Float f) -> mkfb BdGE f
          (AST.ReMatch, String p) -> putTMTree (mkBoundsTree [BdStrMatch $ BdReMatch p])
          (AST.ReNotMatch, String p) -> putTMTree (mkBoundsTree [BdStrMatch $ BdReNotMatch p])
          _ -> putConflict
        _ -> putConflict
      TNRefCycle (RefCycleVertMerger _) -> putTMTree t
      _ -> putConflict
    Nothing -> return ()
 where
  conflict :: Tree
  conflict = mkBottomTree $ printf "%s cannot be used for %s" (show _t) (show op)

  putConflict :: (TreeMonad s m) => m ()
  putConflict = putTMTree conflict

  ia :: (TreeMonad s m) => Integer -> (Integer -> Integer) -> m ()
  ia a f = putTMTree (mkAtomTree (Int $ f a))

  fa :: (TreeMonad s m) => Double -> (Double -> Double) -> m ()
  fa a f = putTMTree (mkAtomTree (Float $ f a))

  mkb :: (TreeMonad s m) => Bound -> m ()
  mkb b = putTMTree (mkBoundsTree [b])

  mkib :: (TreeMonad s m) => BdNumCmpOp -> Integer -> m ()
  mkib uop i = putTMTree (mkBoundsTree [BdNumCmp $ BdNumCmpCons uop (NumInt i)])

  mkfb :: (TreeMonad s m) => BdNumCmpOp -> Double -> m ()
  mkfb uop f = putTMTree (mkBoundsTree [BdNumCmp $ BdNumCmpCons uop (NumFloat f)])

dispBinMutable :: (TreeMonad s m) => AST.BinaryOp -> Tree -> Tree -> m ()
dispBinMutable op = case op of
  AST.Unify -> unify
  _ -> regBin op

regBin :: (TreeMonad s m) => AST.BinaryOp -> Tree -> Tree -> m ()
regBin op t1 t2 = regBinDir op (L, t1) (R, t2)

regBinDir :: (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> m ()
regBinDir op (d1, _t1) (d2, _t2) = do
  withAddrAndFocus $ \addr _ ->
    logDebugStr $
      printf "regBinDir: addr: %s, %s: %s with %s: %s" (show addr) (show d1) (show _t1) (show d2) (show _t2)

  t1M <- reduceAtomOpArg (toBinOpTASeg d1) _t1
  t2M <- reduceAtomOpArg (toBinOpTASeg d2) _t2

  withAddrAndFocus $ \addr _ ->
    logDebugStr $
      printf "regBinDir: addr: %s, reduced args, %s: %s with %s: %s" (show addr) (show d1) (show t1M) (show d2) (show t2M)

  case (t1M, t2M) of
    (Just t1, Just t2) -> case (treeNode t1, treeNode t2) of
      (TNBottom _, _) -> putTMTree t1
      (_, TNBottom _) -> putTMTree t2
      (TNRefCycle (RefCycleVertMerger _), _) -> putTMTree t1
      (_, TNRefCycle (RefCycleVertMerger _)) -> putTMTree t2
      (TNAtom l1, _) -> regBinLeftAtom op (d1, l1, t1) (d2, t2)
      (_, TNAtom l2) -> regBinLeftAtom op (d2, l2, t2) (d1, t1)
      (TNStruct s1, _) -> regBinLeftStruct op (d1, s1, t1) (d2, t2)
      (_, TNStruct s2) -> regBinLeftStruct op (d2, s2, t2) (d1, t1)
      (TNDisj dj1, _) -> regBinLeftDisj op (d1, dj1, t1) (d2, t2)
      (_, TNDisj dj2) -> regBinLeftDisj op (d2, dj2, t2) (d1, t1)
      _ -> regBinLeftOther op (d1, t1) (d2, t2)
    (Just t1, _)
      | TNBottom _ <- treeNode t1 -> putTMTree t1
      | TNRefCycle (RefCycleVertMerger _) <- treeNode t1 -> putTMTree t1
    (_, Just t2)
      | TNBottom _ <- treeNode t2 -> putTMTree t2
      | TNRefCycle (RefCycleVertMerger _) <- treeNode t2 -> putTMTree t2
    _ -> return ()

regBinLeftAtom :: (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, AtomV, Tree) -> (BinOpDirect, Tree) -> m ()
regBinLeftAtom op (d1, ta1, t1) (d2, t2) = do
  logDebugStr $ printf "regBinLeftAtom: %s (%s: %s) (%s: %s)" (show op) (show d1) (show ta1) (show d2) (show t2)
  if
    -- comparison operators
    | isJust (lookup op cmpOps) -> case treeNode t2 of
        TNAtom ta2 ->
          let
            a2 = amvAtom ta2
            f :: (Atom -> Atom -> Bool)
            f = fromJust (lookup op cmpOps)
            r = case (a1, a2) of
              (String _, String _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Int _, Int _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Int _, Float _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Float _, Int _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Float _, Float _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Bool _, Bool _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Null, _) -> Right . Bool $ dirApply f (d1, a1) a2
              (_, Null) -> Right . Bool $ dirApply f (d2, a2) a1
              _ -> Left $ uncmpAtoms a1 a2
           in
            case r of
              Right b -> putTMTree $ mkAtomTree b
              Left err -> putTMTree err
        TNDisj dj2 -> regBinLeftDisj op (d2, dj2, t2) (d1, t1)
        TNStruct _ -> putTMTree $ cmpNull a1 t2
        TNList _ -> putTMTree $ cmpNull a1 t2
        _ -> regBinLeftOther op (d2, t2) (d1, t1)
    -- arithmetic operators
    | op `elem` arithOps -> case treeNode t2 of
        TNAtom ta2 ->
          let
            r = case op of
              AST.Add -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (+) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (+) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (+) (d1, i1) (fromIntegral i2)
                (String s1, String s2) -> Right . String $ dirApply (++) (d1, s1) s2
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              AST.Sub -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (-) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (-) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (-) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              AST.Mul -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (*) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (*) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (*) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              AST.Div -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Float $ dirApply (/) (d1, fromIntegral i1) (fromIntegral i2)
                (Int i1, Float i2) -> Right . Float $ dirApply (/) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (/) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              _ -> Left $ mismatch op a1 (amvAtom ta2)
           in
            case r of
              Right b -> putTMTree $ mkAtomTree b
              Left err -> putTMTree err
        TNDisj dj2 -> regBinLeftDisj op (d2, dj2, t2) (d1, t1)
        TNStruct _ -> putTMTree $ mismatchArith a1 t2
        TNList _ -> putTMTree $ mismatchArith a1 t2
        _ -> regBinLeftOther op (d2, t2) (d1, t1)
    | otherwise -> putTMTree (mkBottomTree $ printf "operator %s is not supported" (show op))
 where
  a1 = amvAtom ta1
  cmpOps = [(AST.Equ, (==)), (AST.BinRelOp AST.NE, (/=))]
  arithOps = [AST.Add, AST.Sub, AST.Mul, AST.Div]

  uncmpAtoms :: Atom -> Atom -> Tree
  uncmpAtoms x y = mkBottomTree $ printf "%s and %s are not comparable" (show x) (show y)

  cmpNull :: Atom -> Tree -> Tree
  cmpNull a t =
    if
      -- There is no way for a non-atom to be compared with a non-null atom.
      | a /= Null -> mismatch op a t
      | op == AST.Equ -> mkAtomTree (Bool False)
      | op == AST.BinRelOp AST.NE -> mkAtomTree (Bool True)
      | otherwise -> mkBottomTree $ printf "operator %s is not supported" (show op)

  mismatchArith :: (Show a, Show b) => a -> b -> Tree
  mismatchArith = mismatch op

dirApply :: (a -> a -> b) -> (BinOpDirect, a) -> a -> b
dirApply f (di1, i1) i2 = if di1 == L then f i1 i2 else f i2 i1

mismatch :: (Show a, Show b) => AST.BinaryOp -> a -> b -> Tree
mismatch op x y = mkBottomTree $ printf "%s can not be used for %s and %s" (show op) (show x) (show y)

regBinLeftStruct ::
  (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, Struct Tree, Tree) -> (BinOpDirect, Tree) -> m ()
regBinLeftStruct op (d1, _, t1) (d2, t2) = case treeNode t2 of
  TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1)
  _ -> putTMTree (mismatch op t1 t2)

regBinLeftDisj ::
  (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, Disj Tree, Tree) -> (BinOpDirect, Tree) -> m ()
regBinLeftDisj op (d1, dj1, t1) (d2, t2) = case dj1 of
  Disj{dsjDefault = Just d} -> regBinDir op (d1, d) (d2, t2)
  _ -> case treeNode t2 of
    TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1)
    _ -> putTMTree (mismatch op t1 t2)

regBinLeftOther :: (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> m ()
regBinLeftOther op (d1, t1) (d2, t2) = do
  withAddrAndFocus $ \addr _ ->
    logDebugStr $ printf "regBinLeftOther: addr: %s, %s: %s, %s: %s" (show addr) (show d1) (show t1) (show d2) (show t2)
  case (treeNode t1, t2) of
    (TNRefCycle _, _) -> return ()
    (TNConstraint c, _) -> do
      na <- regBinDir op (d1, mkNewTree (TNAtom $ cnsAtom c)) (d2, t2) >> getTMTree
      case treeNode na of
        TNAtom atom -> putTMTree (mkNewTree (TNConstraint $ updateCnstrAtom atom c))
        _ -> undefined
    _ -> putTMTree (mkBottomTree mismatchErr)
 where
  mismatchErr :: String
  mismatchErr = printf "values %s and %s cannot be used for %s" (show t1) (show t2) (show op)

data DisjItem = DisjDefault Tree | DisjRegular Tree

instance Show DisjItem where
  show (DisjDefault t) = show t
  show (DisjRegular t) = show t

-- reduceDisjPair is used to evaluate a disjunction whose both sides are evaluated.
reduceDisjPair :: (TreeMonad s m) => DisjItem -> DisjItem -> m Tree
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
  (MonadError String m) => ((Maybe Tree, [Tree], Maybe Tree, [Tree]) -> m Tree) -> Tree -> DisjItem -> m Tree
-- Below is rule M2 and M3. We eliminate the defaults from the right side.
reduceLeftDefault disjCons (Tree{treeNode = TNDisj dj1}) (DisjRegular (Tree{treeNode = TNDisj dj2})) =
  disjCons (dsjDefault dj1, dsjDisjuncts dj1, Nothing, dsjDisjuncts dj2)
-- Below is rule M1.
reduceLeftDefault disjCons v1 (DisjRegular (Tree{treeNode = TNDisj dj2})) =
  disjCons (Just v1, [v1], dsjDefault dj2, dsjDisjuncts dj2)
reduceLeftDefault disjCons v1 (DisjRegular v2) =
  disjCons (Just v1, [v1], Nothing, [v2])
reduceLeftDefault disjCons v1 (DisjDefault v2) =
  disjCons (Nothing, [v1], Nothing, [v2])

-- evalFullDisj is used to evaluate a disjunction whose both sides are regular.
-- Rule: D1, D2
reduceRegularDisj :: (TreeMonad s m) => Tree -> Tree -> m Tree
reduceRegularDisj (Tree{treeNode = TNDisj dj1}) (Tree{treeNode = TNDisj dj2}) =
  newDisj (dsjDefault dj1) (dsjDisjuncts dj1) (dsjDefault dj2) (dsjDisjuncts dj2)
reduceRegularDisj (Tree{treeNode = TNDisj dj}) y = newDisj (dsjDefault dj) (dsjDisjuncts dj) Nothing [y]
reduceRegularDisj x (Tree{treeNode = TNDisj dj}) = newDisj Nothing [x] (dsjDefault dj) (dsjDisjuncts dj)
-- Rule D0
reduceRegularDisj x y = newDisj Nothing [x] Nothing [y]

newDisj :: (TreeMonad s m) => Maybe Tree -> [Tree] -> Maybe Tree -> [Tree] -> m Tree
newDisj df1 ds1 df2 ds2 =
  if
    | null allTerms -> throwErrSt "both sides of disjunction are empty"
    -- No non-bottoms exist
    | null filteredTerms -> return $ head allTerms
    -- the disjunction of a value a with bottom is always a.
    | length filteredTerms == 1 -> return $ head filteredTerms
    -- two or more non-bottom terms exist.
    | otherwise -> return $ mkDisjTree (defaultFrom $ filterBtms defaults) (filterBtms disjuncts)
 where
  defaults :: [Tree]
  defaults = catMaybes [df1, df2]

  defaultFrom :: [Tree] -> Maybe Tree
  defaultFrom xs = case xs of
    [x] -> Just x
    -- If there are more than one defaults, then defaults become disjuncts.
    [x, y] -> Just $ mkDisjTree Nothing [x, y]
    _ -> Nothing

  -- The first element is non-bottom.
  -- The second element is a bottom.
  disjuncts :: [Tree]
  disjuncts = dedupAppend ds1 ds2

  filterBtms :: [Tree] -> [Tree]
  filterBtms = filter (not . isTreeBottom)

  allTerms :: [Tree]
  allTerms = defaults ++ disjuncts

  filteredTerms :: [Tree]
  filteredTerms = filterBtms allTerms

  -- dedupAppend appends unique elements in ys to the xs list, but only if they are not already in xs.
  -- xs and ys are guaranteed to be unique.
  dedupAppend :: [Tree] -> [Tree] -> [Tree]
  dedupAppend xs ys = xs ++ foldr (\y acc -> if y `elem` xs then acc else y : acc) [] ys

mkUnifyNode :: Tree -> Tree -> Mutable Tree
mkUnifyNode = mkBinaryOp AST.Unify unify

-- | Create a unify node from two UTrees.
mkUnifyUTreesNode :: UTree -> UTree -> Mutable Tree
mkUnifyUTreesNode ut1 ut2 =
  -- Values of UTrees are created to receive the updated values.
  mkBinaryOp AST.Unify (\a b -> unifyUTrees (ut1{utVal = a}) (ut2{utVal = b})) (utVal ut1) (utVal ut2)

-- | UTree is a tree with a direction and an embedded flag.
data UTree = UTree
  { utVal :: Tree
  , utDir :: Path.BinOpDirect
  , utEmbedded :: Bool
  -- ^ Whether the tree is embedded in a struct.
  }

instance Show UTree where
  show (UTree t d e) = printf "(%s,e:%s,\n%s)" (show d) (show e) (show t)

unify :: (TreeMonad s m) => Tree -> Tree -> m ()
unify t1 t2 = unifyUTrees (UTree t1 Path.L False) (UTree t2 Path.R False)

-- | Unify the right embedded tree with the left tree.
unifyREmbedded :: (TreeMonad s m) => Tree -> Tree -> m ()
unifyREmbedded t1 t2 = unifyUTrees (UTree t1 Path.L False) (UTree t2 Path.R True)

{- | Unify UTrees.

The special case is the struct. If two operands are structs, we must not immediately reduce the operands. Instead, we
should combine both fields and reduce sub-fields. The reason is stated in the spec,

> The successful unification of structs a and b is a new struct c which has all fields of both a and b, where the value
of a field f in c is a.f & b.f if f is defined in both a and b, or just a.f or b.f if f is in just a or b, respectively.
Any references to a or b in their respective field values need to be replaced with references to c. The result of a
unification is bottom (_|_) if any of its defined fields evaluates to bottom, recursively.

Suppose one of the structs contains a reference to a field in the other struct, and reducing the struct operand will
register a notifier that watches the field in the unified struct. The notifier will be triggered when the field is
updated. But the direction is from parent to the child. Once the operand is updated, the reference system will search
for the lowest ancestor mutable to re-run reduction since one of the LAM's dependencies is updated. This will cause the
unified struct to be reduced again, and the notifier will be triggered again. This will cause an infinite loop.

Consider the example:
x: { a: c } & { c: {} }

After reducing the left struct, the notifier, (/x/c, /x/fa0/a) will be registered to watch the field "c". When the field
"c" is updated, the notifier will be triggered. Then the struct labeled with "x" will be reduced again. An infinite loop
will occur.

Another example:
{
  a: b + 100
  b: a - 100
} &
{ b: 50 }

The "b" in the first struct will have to see the atom 50.

For operands that are references, we do not need reduce them. We only evaluate the expression when the reference is
dereferenced. If the reference is evaluated to a struct, the struct will be a raw struct.
-}
unifyUTrees :: (TreeMonad s m) => UTree -> UTree -> m ()
unifyUTrees ut1@(UTree{utVal = t1}) ut2@(UTree{utVal = t2}) = withAddrAndFocus $ \addr _ ->
  debugSpan (printf ("unifying, addr: %s:, %s" ++ "\n" ++ "with %s") (show addr) (show ut1) (show ut2)) $ do
    -- Each case should handle embedded case when the left value is embedded.
    case (treeNode t1, treeNode t2) of
      (TNBottom _, _) -> putTMTree t1
      (_, TNBottom _) -> putTMTree t2
      (TNTop, _) -> unifyLeftTop ut1 ut2
      (_, TNTop) -> unifyLeftTop ut2 ut1
      (TNAtom a1, _) -> unifyLeftAtom (a1, ut1) ut2
      -- Below is the earliest time to create a constraint
      (_, TNAtom a2) -> unifyLeftAtom (a2, ut2) ut1
      (TNDisj dj1, _) -> unifyLeftDisj (dj1, ut1) ut2
      (_, TNDisj dj2) -> unifyLeftDisj (dj2, ut2) ut1
      (TNStruct s1, _) -> unifyLeftStruct (s1, ut1) ut2
      (_, TNStruct s2) -> unifyLeftStruct (s2, ut2) ut1
      (TNBounds b1, _) -> unifyLeftBound (b1, ut1) ut2
      (_, TNBounds b2) -> unifyLeftBound (b2, ut2) ut1
      _ -> unifyLeftOther ut1 ut2

    -- reduce the merged tree
    withTree $ \t -> case getMutableFromTree t of
      -- If the unify result is incomplete, skip the reduction.
      Just MutStub -> return ()
      _ -> reduce

unifyLeftTop :: (TreeMonad s m) => UTree -> UTree -> m ()
unifyLeftTop ut1 ut2 = do
  case treeNode . utVal $ ut2 of
    -- If the left top is embedded in the right struct, we can immediately put the top into the tree without worrying
    -- any future existing/new fields. Because for example {_, a: 1} is equivalent to _ & {a: 1}. This follows the
    -- behavior of the spec:
    -- The result of { A } is A for any A (including definitions).
    -- Notice that this is different from the behavior of the latest CUE. The latest CUE would do the following:
    -- {_, _h: int} & {_h: "hidden"} -> _|_.
    TNStruct _ | utEmbedded ut1 -> putTMTree (utVal ut1)
    _ -> putTMTree (utVal ut2)

unifyLeftAtom :: (TreeMonad s m) => (AtomV, UTree) -> UTree -> m ()
unifyLeftAtom (v1, ut1@(UTree{utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = do
  case (amvAtom v1, treeNode t2) of
    (String x, TNAtom s)
      | String y <- amvAtom s -> putTree $ if x == y then TNAtom v1 else amismatch x y
    (Int x, TNAtom s)
      | Int y <- amvAtom s -> putTree $ if x == y then TNAtom v1 else amismatch x y
    (Float x, TNAtom s)
      | Float y <- amvAtom s -> putTree $ if x == y then TNAtom v1 else amismatch x y
    (Bool x, TNAtom s)
      | Bool y <- amvAtom s -> putTree $ if x == y then TNAtom v1 else amismatch x y
    (Null, TNAtom s) | Null <- amvAtom s -> putTree $ TNAtom v1
    (_, TNBounds b) -> do
      logDebugStr $ printf "unifyLeftAtom, %s with Bounds: %s" (show v1) (show t2)
      putTMTree $ unifyAtomBounds (d1, amvAtom v1) (d2, bdsList b)
    (_, TNConstraint c) ->
      if v1 == cnsAtom c
        then putCnstr (cnsAtom c)
        else putTMTree . mkBottomTree $ printf "values mismatch: %s != %s" (show v1) (show $ cnsAtom c)
    (_, TNDisj dj2) -> do
      logDebugStr $ printf "unifyLeftAtom: TNDisj %s, %s" (show t2) (show v1)
      unifyLeftDisj (dj2, ut2) ut1
    (_, TNMutable mut2)
      | (SFunc m2) <- mut2 -> case sfnType m2 of
          -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
          -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
          -- marked disjunction.
          DisjMutable -> unifyLeftOther ut2 ut1
          _ -> procOther
      | otherwise -> procOther
    (_, TNRefCycle _) -> procOther
    -- If the left atom is embedded in the right struct and there is no fields and no pending dynamic fields, we can
    -- immediately put the atom into the tree without worrying any future new fields. This is what CUE currently
    -- does.
    (_, TNStruct s2) | utEmbedded ut1 && hasEmptyFields s2 -> putTree (TNAtom v1)
    _ -> unifyLeftOther ut1 ut2
 where
  putTree :: (TreeMonad s m) => TreeNode Tree -> m ()
  putTree n = putTMTree $ mkNewTree n

  amismatch :: (Show a) => a -> a -> TreeNode Tree
  amismatch x y = TNBottom . Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

  procOther :: (TreeMonad s m) => m ()
  procOther = do
    RuntimeParams{rpCreateCnstr = cc} <- asks cfRuntimeParams
    logDebugStr $ printf "unifyLeftAtom: cc: %s, procOther: %s, %s" (show cc) (show ut1) (show ut2)
    if cc
      then do
        c <- putCnstr v1 >> getTMTree
        logDebugStr $ printf "unifyLeftAtom: constraint created, %s" (show c)
      else unifyLeftOther ut2 ut1

  putCnstr :: (TreeMonad s m) => AtomV -> m ()
  putCnstr a1 = do
    unifyOp <- getTMParent
    logDebugStr $ printf "unifyLeftAtom: creating constraint, t: %s" (show unifyOp)
    -- TODO: this is hack now. The unifyOp has a mutStub, which makes the buildASTExpr unhappy.
    let emptyUnifyOp = case getMutableFromTree unifyOp of
          Just mut -> mkMutableTree $ setMutVal Nothing mut
          _ -> unifyOp
    e <- maybe (buildASTExpr False emptyUnifyOp) return (treeExpr unifyOp)
    logDebugStr $ printf "unifyLeftAtom: creating constraint, e: %s, t: %s" (show e) (show unifyOp)
    putTMTree $ mkCnstrTree a1 e

unifyLeftBound :: (TreeMonad s m) => (Bounds, UTree) -> UTree -> m ()
unifyLeftBound (b1, ut1@(UTree{utVal = t1, utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = case treeNode t2 of
  TNAtom ta2 -> do
    logDebugStr $ printf "unifyAtomBounds: %s, %s" (show t1) (show t2)
    putTMTree $ unifyAtomBounds (d2, amvAtom ta2) (d1, bdsList b1)
  TNBounds b2 -> do
    logDebugStr $ printf "unifyBoundList: %s, %s" (show t1) (show t2)
    let res = unifyBoundList (d1, bdsList b1) (d2, bdsList b2)
    case res of
      Left err -> putTMTree (mkBottomTree err)
      Right bs ->
        let
          r =
            foldl
              ( \acc x -> case x of
                  BdIsAtom a -> (fst acc, Just a)
                  _ -> (x : fst acc, snd acc)
              )
              ([], Nothing)
              bs
         in
          case snd r of
            Just a -> putTMTree (mkAtomTree a)
            Nothing -> putTMTree (mkBoundsTree (fst r))
  -- If the left bounds are embedded in the right struct and there is no fields and no pending dynamic fields, we can
  -- immediately put the bounds into the tree without worrying any future new fields. This is what CUE currently
  -- does.
  TNStruct s2 | utEmbedded ut1 && hasEmptyFields s2 -> putTMTree t1
  _ -> unifyLeftOther ut2 ut1

unifyAtomBounds :: (Path.BinOpDirect, Atom) -> (Path.BinOpDirect, [Bound]) -> Tree
unifyAtomBounds (d1, a1) (d2, bs) =
  -- try to find the atom in the bounds list.
  foldl1 findAtom (map withBound bs)
 where
  ta1 = mkAtomTree a1

  findAtom acc x = if acc == ta1 || x == ta1 then acc else x

  withBound :: Bound -> Tree
  withBound b =
    let
      r = unifyBounds (d1, BdIsAtom a1) (d2, b)
     in
      case r of
        Left s -> mkBottomTree s
        Right v -> case v of
          [x] -> case x of
            BdIsAtom a -> mkAtomTree a
            _ -> mkBottomTree $ printf "unexpected bounds unification result: %s" (show x)
          _ -> mkBottomTree $ printf "unexpected bounds unification result: %s" (show v)

-- TODO: regex implementation
-- Second argument is the pattern.
reMatch :: String -> String -> Bool
reMatch = (==)

-- TODO: regex implementation
-- Second argument is the pattern.
reNotMatch :: String -> String -> Bool
reNotMatch = (/=)

unifyBoundList :: (Path.BinOpDirect, [Bound]) -> (Path.BinOpDirect, [Bound]) -> Either String [Bound]
unifyBoundList (d1, bs1) (d2, bs2) = case (bs1, bs2) of
  ([], _) -> return bs2
  (_, []) -> return bs1
  _ -> do
    bss <- manyToMany (d1, bs1) (d2, bs2)
    let bsMap = Map.fromListWith (++) (map (\b -> (bdRep b, [b])) (concat bss))
    norm <- forM bsMap narrowBounds
    let m = Map.toList norm
    return $ concat $ map snd m
 where
  oneToMany :: (Path.BinOpDirect, Bound) -> (Path.BinOpDirect, [Bound]) -> Either String [Bound]
  oneToMany (ld1, b) (ld2, ts) =
    let f x y = unifyBounds (ld1, x) (ld2, y)
     in do
          r <- mapM (`f` b) ts
          return $ concat r

  manyToMany :: (Path.BinOpDirect, [Bound]) -> (Path.BinOpDirect, [Bound]) -> Either String [[Bound]]
  manyToMany (ld1, ts1) (ld2, ts2) =
    if ld1 == Path.R
      then mapM (\y -> oneToMany (ld2, y) (ld1, ts1)) ts2
      else mapM (\x -> oneToMany (ld1, x) (ld2, ts2)) ts1

-- | Narrow the bounds to the smallest set of bounds for the same bound type.
narrowBounds :: [Bound] -> Either String [Bound]
narrowBounds xs = case xs of
  [] -> return []
  (BdNE _) : _ -> return xs
  x : rs ->
    let
      f acc y =
        if length acc == 1
          then unifyBounds (Path.L, acc !! 0) (Path.R, y)
          else Left "bounds mismatch"
     in
      foldM f [x] rs

unifyBounds :: (Path.BinOpDirect, Bound) -> (Path.BinOpDirect, Bound) -> Either String [Bound]
unifyBounds db1@(d1, b1) db2@(_, b2) = case b1 of
  BdNE a1 -> case b2 of
    BdNE a2 -> return $ if a1 == a2 then [b1] else newOrdBounds
    BdNumCmp c2 -> uNENumCmp a1 c2
    BdStrMatch m2 -> uNEStrMatch a1 m2
    BdType t2 -> uNEType a1 t2
    BdIsAtom a2 -> if a1 == a2 then Left conflict else return [b2]
  BdNumCmp c1 -> case b2 of
    BdNumCmp c2 -> uNumCmpNumCmp c1 c2
    BdStrMatch _ -> Left conflict
    BdType t2 ->
      if t2 `elem` [BdInt, BdFloat, BdNumber]
        then return [b1]
        else Left conflict
    BdIsAtom a2 -> uNumCmpAtom c1 a2
    _ -> unifyBounds db2 db1
  BdStrMatch m1 -> case b2 of
    BdStrMatch m2 -> case (m1, m2) of
      (BdReMatch _, BdReMatch _) -> return $ if m1 == m2 then [b1] else newOrdBounds
      (BdReNotMatch _, BdReNotMatch _) -> return $ if m1 == m2 then [b1] else newOrdBounds
      _ -> return [b1, b2]
    BdType t2 ->
      if t2 `elem` [BdString]
        then return [b1]
        else Left conflict
    BdIsAtom a2 -> uStrMatchAtom m1 a2
    _ -> unifyBounds db2 db1
  BdType t1 -> case b2 of
    BdType t2 -> if t1 == t2 then return [b1] else Left conflict
    BdIsAtom a2 -> uTypeAtom t1 a2
    _ -> unifyBounds db2 db1
  BdIsAtom a1 -> case b2 of
    BdIsAtom a2 -> if a1 == a2 then return [b1] else Left conflict
    _ -> unifyBounds db2 db1
 where
  uNENumCmp :: Atom -> BdNumCmp -> Either String [Bound]
  uNENumCmp a1 (BdNumCmpCons o2 y) = do
    x <- case a1 of
      Int x -> return $ NumInt x
      Float x -> return $ NumFloat x
      _ -> Left conflict
    case o2 of
      BdLT -> if x < y then Left conflict else return newOrdBounds
      BdLE -> if x <= y then Left conflict else return newOrdBounds
      BdGT -> if x > y then Left conflict else return newOrdBounds
      BdGE -> if x >= y then Left conflict else return newOrdBounds

  uNEStrMatch :: Atom -> BdStrMatch -> Either String [Bound]
  uNEStrMatch a1 m2 = do
    _ <- case a1 of
      String x -> return x
      _ -> Left conflict
    case m2 of
      -- delay verification
      BdReMatch _ -> return [b1, b2]
      BdReNotMatch _ -> return [b1, b2]

  uNEType :: Atom -> BdType -> Either String [Bound]
  uNEType a1 t2 = case a1 of
    Bool _ -> if BdBool == t2 then Left conflict else return newOrdBounds
    Int _ -> if BdInt == t2 then Left conflict else return newOrdBounds
    Float _ -> if BdFloat == t2 then Left conflict else return newOrdBounds
    String _ -> if BdString == t2 then Left conflict else return newOrdBounds
    -- TODO: null?
    _ -> Left conflict

  ncncGroup :: [([BdNumCmpOp], [(Number -> Number -> Bool)])]
  ncncGroup =
    [ ([BdLT, BdLE], [(<=), (>)])
    , ([BdGT, BdGE], [(>=), (<)])
    ]

  uNumCmpNumCmp :: BdNumCmp -> BdNumCmp -> Either String [Bound]
  uNumCmpNumCmp (BdNumCmpCons o1 n1) (BdNumCmpCons o2 n2) =
    let
      c1g = if o1 `elem` fst (ncncGroup !! 0) then ncncGroup !! 0 else ncncGroup !! 1
      c1SameGCmp = snd c1g !! 0
      c1OppGCmp = snd c1g !! 1
      isSameGroup = o2 `elem` (fst c1g)
      oppClosedEnds = sort [o1, o2] == [BdLE, BdGE]
     in
      if isSameGroup
        then return $ if c1SameGCmp n1 n2 then [b1] else [b2]
        else
          if
            | oppClosedEnds && n1 == n2 -> case n1 of
                NumInt i -> return [BdIsAtom $ Int i]
                NumFloat f -> return [BdIsAtom $ Float f]
            | c1OppGCmp n1 n2 -> return newOrdBounds
            | otherwise -> Left conflict

  uNumCmpAtom :: BdNumCmp -> Atom -> Either String [Bound]
  uNumCmpAtom (BdNumCmpCons o1 n1) a2 = do
    x <- case a2 of
      Int x -> return $ NumInt x
      Float x -> return $ NumFloat x
      _ -> Left conflict
    let r = case o1 of
          BdLT -> x < n1
          BdLE -> x <= n1
          BdGT -> x > n1
          BdGE -> x >= n1
    if r then return [b2] else Left conflict

  uStrMatchAtom :: BdStrMatch -> Atom -> Either String [Bound]
  uStrMatchAtom m1 a2 = case a2 of
    String s2 ->
      let r = case m1 of
            BdReMatch p1 -> reMatch s2 p1
            BdReNotMatch p1 -> reNotMatch s2 p1
       in if r then return [b2] else Left conflict
    _ -> Left conflict

  uTypeAtom :: BdType -> Atom -> Either String [Bound]
  uTypeAtom t1 a2 =
    let r = case a2 of
          Bool _ -> t1 == BdBool
          Int _ -> t1 `elem` [BdInt, BdNumber]
          Float _ -> t1 `elem` [BdFloat, BdNumber]
          String _ -> t1 == BdString
          _ -> False
     in if r then return [b2] else Left conflict

  conflict :: String
  conflict = printf "bounds %s and %s conflict" (show b1) (show b2)

  newOrdBounds :: [Bound]
  newOrdBounds = if d1 == Path.L then [b1, b2] else [b2, b1]

-- | unifyLeftOther is the sink of the unification process.
unifyLeftOther :: (TreeMonad s m) => UTree -> UTree -> m ()
unifyLeftOther ut1@(UTree{utVal = t1, utDir = d1}) ut2@(UTree{utVal = t2}) =
  case treeNode t1 of
    (TNMutable _) -> do
      withAddrAndFocus $ \addr _ ->
        logDebugStr $ printf "unifyLeftOther starts, addr: %s, %s, %s" (show addr) (show ut1) (show ut2)
      -- If the left value is mutable, we should shallow reduce the left value first.
      r1 <-
        local (\r -> r{cfFunctions = (cfFunctions r){fnReduce = shallowReduce}}) $
          reduceMutableArg (Path.toBinOpTASeg d1) t1
      case treeNode r1 of
        TNMutable _ -> return () -- No concrete value exists.
        _ -> unifyUTrees (ut1{utVal = r1}) ut2

    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    (TNConstraint c1) -> do
      r <- unifyUTrees (ut1{utVal = mkNewTree (TNAtom $ cnsAtom c1)}) ut2
      na <- getTMTree
      putTMTree $ case treeNode na of
        TNBottom _ -> na
        _ -> t1
      return r
    -- According to the spec,
    -- A field value of the form r & v, where r evaluates to a reference cycle and v is a concrete value, evaluates to v.
    -- Unification is idempotent and unifying a value with itself ad infinitum, which is what the cycle represents,
    -- results in this value. Implementations should detect cycles of this kind, ignore r, and take v as the result of
    -- unification.
    -- We can just return the second value.
    (TNRefCycle _) -> putTMTree t2
    -- TODO: comment
    TNStructuralCycle (StructuralCycle infAddr) -> do
      curPath <- getTMAbsAddr
      logDebugStr $
        printf
          "unifyLeftOther: unifying with structural cycle, inf path: %s, current path: %s"
          (show infAddr)
          (show curPath)
      if isPrefix infAddr curPath
        then putTMTree $ mkBottomTree "structural cycle"
        else do
          raw <-
            maybe (throwErrSt "original expression is not found") return (treeExpr t1)
              >>= evalExprTM
          r1 <-
            local (\r -> r{cfFunctions = (cfFunctions r){fnReduce = shallowReduce}}) $
              reduceMutableArg (Path.toBinOpTASeg d1) raw
          logDebugStr $
            printf
              "unifyLeftOther: found structural cycle, trying original deref'd %s with %s"
              (show r1)
              (show t2)
          unifyUTrees ut1{utVal = r1} ut2
    _ -> putNotUnifiable
 where
  putNotUnifiable :: (TreeMonad s m) => m ()
  putNotUnifiable = mkNodeWithDir ut1 ut2 f
   where
    f :: (TreeMonad s m) => Tree -> Tree -> m ()
    f x y = putTMTree $ mkBottomTree $ printf "values not unifiable: L:\n%s, R:\n%s" (show x) (show y)

unifyLeftStruct :: (TreeMonad s m) => (Struct Tree, UTree) -> UTree -> m ()
unifyLeftStruct (s1, ut1@(UTree{utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = case treeNode t2 of
  -- If either of the structs is embedded, closed struct restrictions are ignored.
  TNStruct s2 -> unifyStructs (utEmbedded ut1 || utEmbedded ut2) (d1, s1) (d2, s2)
  _ -> unifyLeftOther ut2 ut1

{- | unify two structs.

The s1 is made the left struct, and s2 is made the right struct.

For closedness, unification only generates a closed struct but not a recursively closed struct since to close a struct
recursively, the only way is to reference the struct via a #ident.
-}
unifyStructs ::
  (TreeMonad s m) => Bool -> (Path.BinOpDirect, Struct Tree) -> (Path.BinOpDirect, Struct Tree) -> m ()
unifyStructs isEitherEmbeded (Path.L, _s1) (_, _s2) = do
  let
    s1 = _s1
    s2 = _s2

  lBtm1 <- checkPermittedLabels s1 isEitherEmbeded s2
  lBtm2 <- checkPermittedLabels s2 isEitherEmbeded s1
  case (lBtm1, lBtm2) of
    (Just b1, _) -> putTMTree b1
    (_, Just b2) -> putTMTree b2
    _ -> do
      sid <- allocTMScopeID
      let merged = nodesToStruct sid (unionFields s1 s2) s1 s2
      withAddrAndFocus $ \addr _ ->
        logDebugStr $ printf "unifyStructs: %s gets updated to tree:\n%s" (show addr) (show merged)
      -- in reduce, the new combined fields will be checked by the combined patterns.
      putTMTree merged
 where
  -- merge two fields by creating a unify node with merged attributes.
  mergeField :: Field Tree -> Field Tree -> Field Tree
  mergeField sf1 sf2 =
    let
      ua = mergeAttrs (ssfAttr sf1) (ssfAttr sf2)
      -- No original node exists yet
      f = mkUnifyNode (ssfValue sf1) (ssfValue sf2)
     in
      Field
        { ssfValue = mkMutableTree f
        , ssfAttr = ua
        , -- TODO
          ssfCnstrs = []
        }

  -- merge two fields that are not let-bindings.
  unionFields :: Struct Tree -> Struct Tree -> [(Path.StructTASeg, Field Tree)]
  unionFields st1 st2 =
    foldr
      ( \seg acc ->
          let
            f1M = getFieldFromSV (fields1 Map.! seg)
            f2M = getFieldFromSV (fields2 Map.! seg)
           in
            if
              | seg `Set.member` l1Set && seg `Set.member` l2Set
              , Just sf1 <- f1M
              , Just sf2 <- f2M ->
                  (seg, mergeField sf1 sf2) : acc
              | seg `Set.member` l1Set, Just sf1 <- f1M -> (seg, sf1) : acc
              | seg `Set.member` l2Set, Just sf2 <- f2M -> (seg, sf2) : acc
              | otherwise -> acc
      )
      []
      unionLabels
   where
    fields1 = stcSubs st1
    fields2 = stcSubs st2
    l1Set = Map.keysSet fields1
    l2Set = Map.keysSet fields2

    -- Put the labels in the order of the first struct and append the labels that are not in the first struct.
    unionLabels =
      stcOrdLabels st1
        ++ foldr (\l acc -> if l `Set.member` l1Set then acc else l : acc) [] (stcOrdLabels st2)

  nodesToStruct ::
    Int -> [(Path.StructTASeg, Field Tree)] -> Struct Tree -> Struct Tree -> Tree
  nodesToStruct sid nodes st1 st2 =
    mkStructTree $
      emptyStruct
        { stcID = sid
        , stcOrdLabels = map fst nodes
        , stcSubs = Map.fromList $ map (\(seg, f) -> (seg, SField f)) nodes
        , stcPendSubs = combinedPendSubs
        , stcCnstrs = combinedPatterns
        , stcClosed = stcClosed st1 || stcClosed st2
        }
   where
    combinedPendSubs = stcPendSubs st1 ++ stcPendSubs st2
    combinedPatterns = stcCnstrs st1 ++ stcCnstrs st2
unifyStructs isEitherEmbeded dt1@(Path.R, _) dt2 = unifyStructs isEitherEmbeded dt2 dt1

{- | Check if the new labels from the new struct are permitted based on the base struct.

The isNewEmbedded flag indicates whether the new struct is embedded in the base struct.
-}
checkPermittedLabels :: (TreeMonad s m) => Struct Tree -> Bool -> Struct Tree -> m (Maybe Tree)
checkPermittedLabels base isNewEmbedded new =
  -- According to the spec, An embedded value of type struct is unified with the struct in which it is embedded, but
  -- disregarding the restrictions imposed by closed structs.
  if not (stcClosed base) || isNewEmbedded
    then return Nothing
    else do
      let
        baseLabels = Set.fromList $ stcOrdLabels base
        basePatterns = map scsPattern (stcCnstrs base)
        newLabels = Set.fromList $ stcOrdLabels new
        -- diff is the new labels that are not in the base struct.
        diff = Set.difference newLabels baseLabels

      -- If the new struct has new labels, we need to check if they are allowed by the field patterns of the base
      -- struct.
      -- A "new" field is allowed if there is at least one pattern that matches the field.
      res <-
        mapM
          ( \seg -> case seg of
              StringTASeg s -> do
                -- foldM only returns whether the new label is allowed by the patterns.
                r <-
                  foldM
                    ( \iacc pat ->
                        if iacc
                          then return iacc
                          else do
                            r <- patMatchLabel pat s
                            logDebugStr $ printf "checkPermittedLabels: pat: %s, s: %s, r: %s" (show pat) s (show r)
                            return r
                    )
                    -- By default, "new" label is not allowed.
                    False
                    basePatterns

                return (seg, r)
              _ -> throwErrSt $ printf "unexpected segment: %s" (show seg)
          )
          (Set.toList diff)

      -- A field is disallowed if no pattern exists or no pattern matches the label.
      let disallowed = map fst $ filter (not . snd) res

      withAddrAndFocus $ \addr _ ->
        logDebugStr $
          printf
            "checkPermittedLabels: addr: %s, isNewEmbedde: %s, basePatterns: %s, diff: %s, r: %s, disallowed: %s"
            (show addr)
            (show isNewEmbedded)
            (show basePatterns)
            (show $ Set.toList diff)
            (show res)
            (show disallowed)

      -- When no new labels or all new labels are in the patterns, we return the new labels.
      if null disallowed
        then return Nothing
        else return . Just $ mkBottomTree $ printf "fields: %s are not allowed" (show disallowed)

mkNodeWithDir ::
  (TreeMonad s m) => UTree -> UTree -> (Tree -> Tree -> m ()) -> m ()
mkNodeWithDir (UTree{utVal = t1, utDir = d1}) (UTree{utVal = t2}) f = case d1 of
  Path.L -> f t1 t2
  Path.R -> f t2 t1

unifyLeftDisj :: (TreeMonad s m) => (Disj Tree, UTree) -> UTree -> m ()
unifyLeftDisj
  (dj1, ut1@(UTree{utDir = d1, utEmbedded = isEmbedded1}))
  ut2@( UTree
          { utVal = t2
          , utDir = d2
          , utEmbedded = isEmbedded2
          }
        ) = do
    withAddrAndFocus $ \addr _ ->
      logDebugStr $ printf "unifyLeftDisj: addr: %s, dj: %s, right: %s" (show addr) (show ut1) (show ut2)
    case treeNode t2 of
      TNMutable _ -> unifyLeftOther ut2 ut1
      TNConstraint _ -> unifyLeftOther ut2 ut1
      TNRefCycle _ -> unifyLeftOther ut2 ut1
      -- If the left disj is embedded in the right struct and there is no fields and no pending dynamic fields, we can
      -- immediately put the disj into the tree without worrying any future new fields. This is what CUE currently
      -- does.
      TNStruct s2
        | utEmbedded ut1 && hasEmptyFields s2 -> putTMTree (utVal ut1)
      TNDisj dj2 -> case (dj1, dj2) of
        -- this is U0 rule, <v1> & <v2> => <v1&v2>
        (Disj{dsjDefault = Nothing, dsjDisjuncts = ds1}, Disj{dsjDefault = Nothing, dsjDisjuncts = ds2}) -> do
          logDebugStr $ printf "unifyLeftDisj: U0, ds1: %s, ds2: %s" (show ds1) (show ds2)
          ds <- mapM (`oneToMany` (d2, isEmbedded2, ds2)) (map (\x -> (d1, isEmbedded1, x)) ds1)
          treeFromNodes Nothing ds >>= putTMTree
        -- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
        (Disj{dsjDefault = Just df1, dsjDisjuncts = ds1}, Disj{dsjDefault = Nothing, dsjDisjuncts = ds2}) -> do
          logDebugStr $ printf "unifyLeftDisj: U1, df1: %s, ds1: %s, df2: N, ds2: %s" (show df1) (show ds1) (show ds2)
          dfs <- oneToMany (d1, isEmbedded1, df1) (d2, isEmbedded2, ds2)
          df <- treeFromNodes Nothing [dfs]
          dss <- manyToMany (d1, isEmbedded1, ds1) (d2, isEmbedded2, ds2)
          treeFromNodes (Just df) dss >>= putTMTree
        -- this is also the U1 rule.
        (Disj{dsjDefault = Nothing}, Disj{}) -> unifyLeftDisj (dj2, ut2) ut1
        -- this is U2 rule, <v1,d1> & <v2,d2> => <v1&v2,d1&d2>
        (Disj{dsjDefault = Just df1, dsjDisjuncts = ds1}, Disj{dsjDefault = Just df2, dsjDisjuncts = ds2}) -> do
          withAddrAndFocus $ \addr _ ->
            logDebugStr $
              printf
                "unifyLeftDisj: addr: %s, U2, d1:%s, df1: %s, ds1: %s, df2: %s, ds2: %s"
                (show addr)
                (show d1)
                (show df1)
                (show ds1)
                (show df2)
                (show ds2)
          df <- unifyUTreesInTemp (ut1{utVal = df1}) (ut2{utVal = df2})
          dss <- manyToMany (d1, isEmbedded1, ds1) (d2, isEmbedded2, ds2)
          withAddrAndFocus $ \addr _ ->
            logDebugStr $ printf "unifyLeftDisj: addr: %s, U2, df: %s, dss: %s" (show addr) (show df) (show dss)
          treeFromNodes (Just df) dss >>= putTMTree
      -- this is the case for a disjunction unified with a value.
      _ -> case dj1 of
        Disj{dsjDefault = Nothing, dsjDisjuncts = ds1} -> do
          logDebugStr $
            printf "unifyLeftDisj: unify with %s, disj: (ds: %s)" (show t2) (show ds1)
          ds2 <- oneToMany (d2, isEmbedded2, t2) (d1, isEmbedded1, ds1)
          treeFromNodes Nothing [ds2] >>= putTMTree
        Disj{dsjDefault = Just df1, dsjDisjuncts = ds1} -> do
          logDebugStr $
            printf "unifyLeftDisj: U1, unify with %s, disj: (df: %s, ds: %s)" (show t2) (show df1) (show ds1)
          df2 <- unifyUTreesInTemp (ut1{utVal = df1}) ut2
          ds2 <- oneToMany (d2, isEmbedded2, t2) (d1, isEmbedded1, ds1)
          logDebugStr $ printf "unifyLeftDisj: U1, df2: %s, ds2: %s" (show df2) (show ds2)
          r <- treeFromNodes (Just df2) [ds2]
          logDebugStr $ printf "unifyLeftDisj: U1, result: %s" (show r)
          putTMTree r
   where
    -- Note: isEmbedded is still required. Think about the following values,
    -- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
    -- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
    oneToMany :: (TreeMonad s m) => (Path.BinOpDirect, Bool, Tree) -> (Path.BinOpDirect, Bool, [Tree]) -> m [Tree]
    oneToMany (ld1, em1, node) (ld2, em2, ts) =
      let f x y = unifyUTreesInTemp (UTree x ld1 em1) (UTree y ld2 em2)
       in mapM (`f` node) ts

    manyToMany :: (TreeMonad s m) => (Path.BinOpDirect, Bool, [Tree]) -> (Path.BinOpDirect, Bool, [Tree]) -> m [[Tree]]
    manyToMany (ld1, em1, ts1) (ld2, em2, ts2) =
      if ld1 == Path.R
        then mapM (\y -> oneToMany (ld2, em2, y) (ld1, em1, ts1)) ts2
        else mapM (\x -> oneToMany (ld1, em1, x) (ld2, em2, ts2)) ts1

unifyUTreesInTemp :: (TreeMonad s m) => UTree -> UTree -> m Tree
unifyUTreesInTemp ut1 ut2 =
  inTempSubTM
    (mkMutableTree $ mkUnifyUTreesNode ut1 ut2)
    $ reduce >> getTMTree

treeFromNodes :: (MonadError String m) => Maybe Tree -> [[Tree]] -> m Tree
treeFromNodes dfM ds = case (excludeBottomM dfM, concatDedupNonBottoms ds) of
  -- if there is no non-bottom disjuncts, we return the first bottom.
  (_, []) -> maybe (throwErrSt $ printf "no disjuncts") return (firstBottom ds)
  (Nothing, [_d]) -> return $ mkNewTree (treeNode _d)
  (Nothing, _ds) ->
    let
      node = TNDisj $ Disj{dsjDefault = Nothing, dsjDisjuncts = _ds}
     in
      return $ mkNewTree node
  (_df, _ds) ->
    let
      node = TNDisj $ Disj{dsjDefault = _df, dsjDisjuncts = _ds}
     in
      return $ mkNewTree node
 where
  -- concat and dedup the non-bottom disjuncts
  concatDedupNonBottoms :: [[Tree]] -> [Tree]
  concatDedupNonBottoms xs =
    dedup $ concatMap (filter (not . isTreeBottom)) xs

  firstBottom :: [[Tree]] -> Maybe Tree
  firstBottom xs = let ys = concatMap (filter isTreeBottom) xs in if null ys then Nothing else Just $ head ys

  excludeBottomM :: Maybe Tree -> Maybe Tree
  excludeBottomM = maybe Nothing (\x -> if isTreeBottom x then Nothing else Just x)

  dedup :: [Tree] -> [Tree]
  dedup = foldr (\y acc -> if y `elem` acc then acc else y : acc) []

-- built-in functions
builtinMutableTable :: [(String, Tree)]
builtinMutableTable =
  [
    ( "close"
    , mkMutableTree . SFunc $
        -- built-in close does not recursively close the struct.
        emptySFunc
          { sfnName = "close"
          , sfnArgs = [mkNewTree TNTop]
          , sfnMethod = close
          }
    )
  ]

-- | Closes a struct when the tree has struct.
close :: (TreeMonad s m) => [Tree] -> m ()
close args
  | length args /= 1 = throwErrSt $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      let a = head args
      r <- reduceMutableArg unaryOpTASeg a
      case treeNode r of
        -- If the argument is pending, wait for the result.
        TNMutable _ -> return ()
        _ -> putTMTree $ closeTree r

-- | Close a struct when the tree has struct.
closeTree :: Tree -> Tree
closeTree a =
  case treeNode a of
    TNStruct s -> setTN a $ TNStruct s{stcClosed = True}
    TNDisj dj ->
      let
        dft = closeTree <$> dsjDefault dj
        ds = map closeTree (dsjDisjuncts dj)
       in
        setTN a $ TNDisj (dj{dsjDefault = dft, dsjDisjuncts = ds})
    -- TODO: Mutable should be closed.
    -- TNMutable _ -> throwErrSt "TODO"
    _ -> a
