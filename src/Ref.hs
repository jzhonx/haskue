{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Ref (
  deref,
  drainNotifQueue,
  evalExprTM,
  notify,
  finalizedAddr,
  searchTMVarInPar,
)
where

import qualified AST
import Class
import Config
import Control.Monad (foldM, unless, when)
import Control.Monad.Reader (ask)
import Control.Monad.State.Strict (runStateT)
import Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe)
import qualified Data.Set as Set
import Env
import Error
import Mutate
import Path
import TMonad
import Text.Printf (printf)
import Util
import Value.Tree

{- | Notify dependents of the change of the value.

It will try all parent nodes to notify the dependents.
-}
notify :: (TreeMonad s m) => m ()
notify = withAddrAndFocus $ \addr t -> debugSpan
  (printf "notify: addr: %s, new value: %s" (show addr) (show t))
  $ do
    cs <- getTMCrumbs
    e <- do
      focus <- getTMTree
      -- First try to get the expression from the tree. If the expression is not found, then build the expression.
      -- The reason for not found could be the tree is unified by a dynamic field.
      maybe
        (buildASTExpr False focus)
        return
        (treeOrig focus)

    -- We should not use root value to notify.
    when (length cs > 1) $ do
      notifyG <- ctxNotifGraph <$> getTMContext
      let
        -- We need to use the finalized addr to find the notifiers so that some dependents that reference on the
        -- finalized address can be notified.
        -- For example, { a: r, r: {y:{}}, p: a.y}. p's a.y references the finalized address while a's value might always
        -- have address of /a/fv/y.
        srcFinalizedAddr = finalizedAddr addr
        recvs = fromMaybe [] (Map.lookup srcFinalizedAddr notifyG)
      logDebugStr $ printf "notify: srcRefAddr: %s, recvs %s" (show addr) (show recvs)
      unless (null recvs) $ do
        notifyWithTree e recvs
        -- The current focus notifying its dependents means it is referred.
        markReferred
      inParentTM $ do
        ptc <- getTMCursor
        -- We must check if the parent is reducing. If the parent is reducing, we should not go up and keep
        -- notifying the dependents.
        -- Because once parent is done with reducing, it will notify its dependents.
        inReducing <- parentIsReducing $ tcTreeAddr ptc
        unless inReducing $ do
          parAddr <- getTMAbsAddr
          addToTMNotifQ (finalizedAddr parAddr)
 where
  parentIsReducing parTreeAddr = do
    stack <- ctxReduceStack <$> getTMContext
    return $ length stack > 1 && stack !! 1 == parTreeAddr

  markReferred :: (TreeMonad s m) => m ()
  markReferred = do
    tc <- getTMCursor
    putTMCursor $ markTCFocusReferred tc

drainNotifQueue :: (TreeMonad s m) => m ()
drainNotifQueue = do
  headM <- popTMNotifQ
  q <- getTMNotifQ
  logDebugStr $ printf "drainNotifQueue: q: %s" (show q)
  case headM of
    Nothing -> return ()
    Just addr -> do
      logDebugStr $ printf "drainNotifQueue: addr: %s" (show addr)
      maybe
        (logDebugStr $ printf "drainNotifQueue: addr: %s, not found" (show addr))
        return
        =<< inAbsRemoteTMMaybe addr notify

      drainNotifQueue

{- | Run the action in the parent tree. All changes will be propagated to the parent tree and back to the current tree.

The focus of the tree must not change the type of the parent.
-}
inParentTM :: (TreeMonad s m) => m () -> m ()
inParentTM f = do
  seg <- getTMTASeg
  t <- getTMTree
  unless (isTreeBottom t || isTreeRefCycleTail t) $ do
    propUpTM
    f
    ok <- descendTMSeg seg
    unless ok $ throwErrSt $ printf "failed to go down with seg %s" (show seg)

notifyWithTree :: (TreeMonad s m) => AST.Expression -> [TreeAddr] -> m ()
notifyWithTree e recvs = do
  mapM_
    ( \dep ->
        inAbsRemoteTMMaybe
          dep
          ( do
              addr <- getTMAbsAddr
              hasDiff <- checkRefHasDiff e
              if hasDiff
                then do
                  logDebugStr $ printf "notifyWithTree: addr: %s, difference found" (show addr)
                  reduceLAMut
                else logDebugStr $ printf "notifyWithTree: addr: %s, no difference found" (show addr)
          )
          -- Remove the notification if the receiver is not found. The receiver might be relocated. For example,
          -- the receiver could first be reduced in a unifying function reducing arguments phase with addr a/fa0.
          -- Then the receiver is relocated to a due to unifying fields.
          >>= maybe (delNotifRecvPrefix dep) return
    )
    recvs

{- | Go to the absolute addr in the tree and execute the action.
If the addr does not exist, return Nothing.
-}
inAbsRemoteTMMaybe :: (TMonad s m t, Show t) => TreeAddr -> m a -> m (Maybe a)
inAbsRemoteTMMaybe p f = do
  origAbsAddr <- getTMAbsAddr

  tarM <- whenM (goTMAbsAddr p) f
  backOk <- goTMAbsAddr origAbsAddr
  unless backOk $ do
    tc <- getTMCursor
    logDebugStr $ printf "tc: %s" (show tc)
    throwErrSt $
      printf
        "failed to go back to the original addr %s, dest: %s"
        (show origAbsAddr)
        (show p)
  return tarM
 where
  whenM :: (TMonad s m t) => m Bool -> m a -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then Just <$> g else return Nothing

{- | Populate the ref's mutval with the new value and trigger the re-evaluation of the lowest ancestor Mutable.

The tree focus is set to the ref mutable.
-}
checkRefHasDiff :: (TreeMonad s m) => AST.Expression -> m Bool
checkRefHasDiff e = withTree $ \t -> do
  case getMutableFromTree t of
    Just (Ref rf) -> do
      let r = refExpr rf /= Just e
      addr <- getTMAbsAddr
      logDebugStr $
        printf
          "checkRefHasDiff: addr: %s, is different: %s, old:\n%s\nnew:\n%s"
          (show addr)
          (show r)
          (show $ refExpr rf)
          (show e)
      return r
    _ -> return False

reduceLAMut :: (TreeMonad s m) => m ()
reduceLAMut = do
  from <- getTMAbsAddr
  -- Locate the lowest ancestor mutable to trigger the re-evaluation of the ancestor mutable.
  -- Notice the tree focus now changes to the LA mutable.
  locateLAMutable
  addr <- getTMAbsAddr
  Config{cfReduce = reduce} <- ask
  withTree $ \t -> case treeNode t of
    TNMutable mut
      | Just _ <- getRefFromMutable mut -> do
          when (from /= addr) $
            throwErrSt $
              printf "the LAMut %s is not the same as the ref addr: %s" (show addr) (show from)
          -- If it is a reference, the re-evaluation can be skipped because
          -- 1. The la mutable is actually itself.
          -- 2. Re-evaluating the reference would get the same value.
          logDebugStr $
            printf
              "reduceLAMut: LAMut is a reference, addr: %s, node: %s, trigger notify"
              (show addr)
              (show t)
          reduce
      -- re-evaluate the highest mutable when it is not a reference.
      | otherwise -> do
          logDebugStr $
            printf "reduceLAMut: re-evaluating the LAMut, addr: %s, node: %s" (show addr) (show t)
          reduce
    _ -> logDebugStr "reduceLAMut: LAMut is not found"

-- Locate the lowest ancestor mutable.
-- TODO: consider the mutable does not have arguments.
locateLAMutable :: (TreeMonad s m) => m ()
locateLAMutable = do
  addr <- getTMAbsAddr
  if hasEmptyTreeAddr addr || not (hasMutableArgSeg addr)
    then return ()
    -- If the addr has mutable argument segments, that means we are in a mutable node.
    else propUpTM >> locateLAMutable
 where
  hasEmptyTreeAddr (Path.TreeAddr sels) = null sels
  -- Check if the addr has mutable argument segments.
  hasMutableArgSeg (Path.TreeAddr sels) =
    any
      ( \case
          (MutableTASeg (MutableArgTASeg _)) -> True
          _ -> False
      )
      sels

{- | Dereference the reference.

It keeps dereferencing until the target node is not a reference node or a cycle is
detected. If the target is found, a copy of the target value is put to the tree.
-}
deref ::
  (TreeMonad s m) =>
  -- | the reference addr
  Path.Reference ->
  m ()
deref ref = withAddrAndFocus $ \addr _ ->
  debugSpan (printf "deref: addr: %s, ref: %s" (show addr) (show ref)) $ do
    isInfEval <- checkInfinite ref
    if isInfEval
      then do
        logDebugStr $ printf "deref: addr: %s, ref: %s, ref is reducing in ancestor" (show addr) (show ref)
        putTMTree $ mkBottomTree "structural cycle detected. infinite evaluation."
      else do
        let refAddr = refNodeAddr addr
        rE <- getDstVal ref (Set.fromList [refAddr])
        addNotifier ref
        case rE of
          Left err -> putTMTree err
          Right Nothing -> return ()
          Right (Just (_, tar)) -> do
            logDebugStr $ printf "deref: addr: %s, ref: %s, target is found: %s" (show addr) (show ref) (show tar)
            putTMTree tar

{- | Check if the ref is already being reduced in the ancestor nodes.

The function is supposed to be run in the mutval env.
-}
checkInfinite :: (TreeMonad s m) => Path.Reference -> m Bool
checkInfinite ref = do
  -- exclude the current mut node.
  mutCrumbs <- tail <$> getTMCrumbs
  let match = foldl (\acc (_, t) -> acc || getRef t == Just ref) False mutCrumbs
  withAddrAndFocus $ \addr t ->
    logDebugStr $
      printf
        "checkInfinite: addr: %s, ref: %s, match: %s, focus: %s"
        (show addr)
        (show ref)
        (show match)
        (show t)
  return match
 where
  getRef :: Tree -> Maybe Path.Reference
  getRef t = case treeNode t of
    TNMutable (Ref rf) -> Just $ refPath rf
    _ -> Nothing

{- | Add a notifier to the context.

If the referenced value changes, then the reference should be updated. Duplicate cases are handled by the
addCtxNotifier.
-}
addNotifier :: (TreeMonad s m) => Path.Reference -> m ()
addNotifier ref = do
  srcAddr <- mustRefToAbsAddr ref
  -- Since we are in the /fv environment, we need to get the refNode addr.
  recvAddr <- refNodeAddr <$> getTMAbsAddr

  logDebugStr $ printf "addNotifier: (%s -> %s)" (show srcAddr) (show recvAddr)
  ctx <- getTMContext
  putTMContext $ addCtxNotifier ctx (srcAddr, recvAddr)

{- | Get the value pointed by the reference.

If the reference addr is self or visited, then return the tuple of the absolute addr of the start of the cycle and
the cycle tail relative addr.
-}
getDstVal ::
  (TreeMonad s m) =>
  Path.Reference ->
  -- | keeps track of the followed *referable* addresses.
  Set.Set TreeAddr ->
  m (Either Tree (Maybe (TreeAddr, Tree)))
getDstVal ref trail = withAddrAndFocus $ \srcAddr _ ->
  debugSpan
    ( printf
        "deref_getDstVal: addr: %s, ref: %s, trail: %s"
        (show srcAddr)
        (show ref)
        (show $ Set.toList trail)
    )
    $ do
      rE <- locateRefAndRun ref $ do
        dstAddr <- getTMAbsAddr
        logDebugStr $ printf "deref_getDstVal ref: %s, ref is found, dstAddr: %s" (show ref) (show dstAddr)
        let
          canSrcAddr = canonicalizeAddr srcAddr
          canDstAddr = canonicalizeAddr dstAddr
        t <- getTMTree
        (val, noError) <-
          if
            -- The bottom must return early so that the var not found error would not be replaced with the cycle error.
            | isTreeBottom t -> return (t, False)
            -- This handles the case when following the chain of references leads to a cycle.
            -- For example, { a: b, b: a, d: a } and we are at d.
            -- The values of d would be: 1. a -> b, 2. b -> a, 3. a (seen) -> RC.
            -- The returned RC would be a self-reference cycle, which has empty addr because the cycle is formed by all
            -- references.
            -- dstAddr is already in the referable form.
            | Set.member dstAddr trail -> do
                logDebugStr $
                  printf
                    "deref_getDstVal: horizontal reference cycle detected: %s, dst: %s, trail: %s"
                    (show ref)
                    (show dstAddr)
                    (show $ Set.toList trail)
                return (setTN t $ TNRefCycle (RefCycleHori (dstAddr, srcAddr)), False)
            -- This handles the case when the reference refers to itself that is the ancestor.
            -- For example, { a: a + 1 } or { a: !a }.
            -- The tree representation of the latter is,
            -- { }
            --  | - a
            -- (!)
            --  | - unary_op
            -- ref_a
            -- Notice that for self-cycle, the srcTreeAddr could be /addr/fv, and the dstTreeAddr could be /addr. They
            -- are the same in the refNode form.
            | canDstAddr == refNodeAddr canSrcAddr && srcAddr /= dstAddr -> withTree $ \tar ->
                case treeNode tar of
                  -- In the validation phase, the subnode of the Constraint node might find the parent Constraint node.
                  TNConstraint c -> return (mkAtomVTree $ cnsOrigAtom c, False)
                  _ -> do
                    logDebugStr $
                      printf
                        "deref_getDstVal: vertical reference cycle tail detected: %s == %s."
                        (show dstAddr)
                        (show srcAddr)
                    return (setTN t $ TNRefCycle (RefCycleVertMerger (dstAddr, srcAddr)), False)
            | isPrefix canDstAddr canSrcAddr && canSrcAddr /= canDstAddr ->
                return
                  ( mkBottomTree $
                      printf "structural cycle detected. %s is a prefix of %s" (show dstAddr) (show srcAddr)
                  , False
                  )
            | otherwise -> return (t, True)
        if noError
          then do
            r <- copyRefVal srcAddr dstAddr trail val
            return . Right $ Just (dstAddr, r)
          else
            return . Right $ Just (dstAddr, val)

      case rE of
        Left _ -> return rE
        Right Nothing -> return rE
        Right (Just (dstAddr, r)) -> follow rE dstAddr r
 where
  follow rE dstAddr t = case getMutableFromTree t of
    -- follow the reference.
    Just (Ref rf) -> do
      withAddrAndFocus $ \addr _ ->
        logDebugStr $
          printf
            "deref_getDstVal: addr: %s, dstAddr: %s, follow the new reference: %s"
            (show addr)
            (show dstAddr)
            (show $ refPath rf)
      getDstVal (refPath rf) (Set.insert dstAddr trail)
    Just (Index _) -> do
      nt <- indexerToRef t
      logDebugStr $ printf "deref_getDstVal: addr: %s, follow the index, index reduced to: %s" (show dstAddr) (show nt)
      case getMutableFromTree nt of
        Just (Ref _) -> follow rE dstAddr nt
        _ -> return rE
    _ -> return rE

{- | Convert the indexer to a ref. If the result is not a ref, then return the original tree.

When evaluating the index arguments, the index arguments are evaluated in the temp scope.
-}
indexerToRef :: (TreeMonad s m) => Tree -> m Tree
indexerToRef t = case getMutableFromTree t of
  Just (Index idx) -> go (idxSels idx)
  _ -> return t
 where
  evalIndexArg :: (TreeMonad s m) => [Tree] -> Int -> m Tree
  evalIndexArg ts i = inTempSubTM (ts !! i) $ do
    Config{cfReduce = reduce} <- ask
    reduce >> getTMTree

  go :: (TreeMonad s m) => [Tree] -> m Tree
  go ts@(h : _)
    | length ts > 1 = do
        idxRefM <- treesToRef <$> mapM (evalIndexArg ts) [1 .. length ts - 1]
        logDebugStr $ printf "indexerToRef: idxRefM is %s" (show idxRefM)
        maybe
          (return t)
          ( \idxRef -> case treeNode h of
              TNMutable mut
                -- If the function is a ref, then we should append the addr to the ref. For example, if the ref is a.b, and
                -- the addr is c, then the new ref should be a.b.c.
                | (Ref ref) <- mut -> do
                    let
                      newRef = appendRefs (refPath ref) idxRef
                      refMutable = mkRefMutable newRef
                    return (mkMutableTree refMutable)
              _ -> return t
          )
          idxRefM
  go _ = throwErrSt "invalid index arguments"

{- | Copy the value of the reference.

dstAddr and trail are used to decide whether to close the deref'd value.

From the spec:
The value of a reference is a copy of the expression associated with the field that it is bound to, with
any references within that expression bound to the respective copies of the fields they were originally
bound to.
-}
copyRefVal :: (TreeMonad s m) => TreeAddr -> TreeAddr -> Set.Set TreeAddr -> Tree -> m Tree
copyRefVal srcAddr dstAddr trail tar = do
  case treeNode tar of
    -- The atom value is final, so we can just return it.
    TNAtom _ -> return tar
    TNBottom _ -> return tar
    TNConstraint c -> return (mkAtomVTree $ cnsAtom c)
    _ -> do
      -- evaluate the original expression.
      _orig <- do
        e <- maybe (buildASTExpr False tar) return $ treeOrig tar
        evalExprTM e

      tc <- getTMCursor
      orig <- rewriteRefIdents _orig srcAddr tc

      Config{cfClose = close} <- ask
      let visited = Set.insert dstAddr trail
      addr <- getTMAbsAddr
      val <-
        if any addrHasDef visited
          then do
            logDebugStr $
              printf
                "deref: addr: %s, visitedRefs: %s, has definition, recursively close the value."
                (show addr)
                (show $ Set.toList visited)
            return . mkMutableTree . SFunc $
              emptySFunc
                { sfnArgs = [orig]
                , sfnName = "deref_close"
                , sfnMethod = close True
                }
          else return orig
      logDebugStr $
        printf
          "deref: addr: %s, deref'd val is: %s, visited: %s, tar: %s"
          (show addr)
          (show val)
          (show $ Set.toList visited)
          (show tar)
      return val

-- | Rewrite all the reference identifiers in the value to new reference paths.
rewriteRefIdents ::
  (Env m) =>
  -- | The new evaluated value.
  Tree ->
  -- | source address
  TreeAddr ->
  -- | The current tree cursor.
  TreeCursor Tree ->
  m Tree
rewriteRefIdents val srcAddr ptc = do
  let valScopeAddr = finalizedAddr $ tcTreeAddr ptc
  utc <- traverseTC (rewriteRefPath valScopeAddr) (val <$ ptc)
  logDebugStr $
    printf "rewriteRefIdents: scope: %s, val: %s, rewrites to: %s" (show valScopeAddr) (show val) (show $ vcFocus utc)
  return $ vcFocus utc
 where
  rewriteRefPath :: (Env m) => TreeAddr -> TreeCursor Tree -> m Tree
  rewriteRefPath valAddr tc =
    let focus = vcFocus tc
     in case getMutableFromTree focus of
          Just (Ref rf) -> newRef valAddr tc rf
          _ -> return focus

  newRef :: (Env m) => TreeAddr -> TreeCursor Tree -> Value.Tree.Reference Tree -> m Tree
  newRef valAddr tc rf = do
    let focus = vcFocus tc
    tarIdentAddrM <- searchIdent (refPath rf) tc
    maybe
      (return focus)
      ( \tarIdentAddr -> do
          let tarIdentInVarScope = isPrefix valAddr tarIdentAddr && tarIdentAddr /= valAddr
          logDebugStr $
            printf
              "rewriteRefIdents: valAddr: %s, tarIdentAddr: %s, refPath: %s, inScope: %s"
              (show valAddr)
              (show tarIdentAddr)
              (show $ refPath rf)
              (show tarIdentInVarScope)
          if tarIdentInVarScope
            -- If the target identifier is in the scope, we should not rewrite because in this way in
            -- unification the identifier can be resolved correctly within the newly unified scope.
            then return focus
            else do
              newPath <- shortestRelPath srcAddr tarIdentAddr (refPath rf)
              return $ setTN focus $ TNMutable . Ref $ rf{refPath = newPath}
      )
      tarIdentAddrM

  -- \| Convert the first identifier of the reference to absolute tree addr if it exists.
  searchIdent :: (Env m) => Path.Reference -> TreeCursor Tree -> m (Maybe TreeAddr)
  searchIdent ref tc = do
    let fstSel = fromJust $ headSel ref
    resM <- searchTCVar fstSel tc
    return $ tcTreeAddr . fst <$> resM

{- | Get the shortest relative path from the srcAddr to the target identifier so that later identifiers can be found.
 -
This assumes that the refAddr is not a full prefix of tarIdentAddr. But from the refAddr, the
tarIdentAddr can be found with shorter address because the refAddr is a prefix of any reference.

Consider:
a: {
  b: c
  c: 1
}
The srcAddr is /a/b, and the tarIdentAddr is /a/c. The shortest relative path is c.
-}
shortestRelPath :: (Env m) => TreeAddr -> TreeAddr -> Path.Reference -> m Path.Reference
shortestRelPath srcAddr tarIdentAddr ref = do
  -- The common prefix should exist, at least the root. The "shortest" path means we should get rid of the common
  -- prefix. The prefix denotes the lowest ancestor scope that both addresses can find. The srcAddr should go to the
  -- lowest ancestor and then go down.
  laAddr <-
    maybe
      (throwErrSt "no common prefix found")
      return
      (prefixTreeAddr srcAddr tarIdentAddr)
  let shortestIdentAddr = trimPrefixTreeAddr tarIdentAddr laAddr
  res <-
    if isTreeAddrEmpty (finalizedAddr shortestIdentAddr)
      -- If the shortestIdentAddr is empty, that means the srcAddr is the same as the tarIdentAddr.
      then addrToRef tarIdentAddr
      else do
        identRef <- addrToRef shortestIdentAddr
        let res = maybe identRef (appendRefs identRef) (tailRef ref)
        return res
  logDebugStr $
    printf
      "shortestRelPath: srcAddr: %s, tarIdentAddr: %s, laAddr: %s, shorterIdentAddr: %s, res: %s"
      (show srcAddr)
      (show tarIdentAddr)
      (show laAddr)
      (show shortestIdentAddr)
      (show res)
  return res
 where
  addrToRef :: (Env m) => TreeAddr -> m Path.Reference
  addrToRef addr =
    let
      segs = addrToList addr
      segToSel :: (Env m) => TASeg -> m (Maybe Selector)
      segToSel (StructTASeg sseg) = return $ StringSel <$> getStrFromSeg sseg
      segToSel (MutableTASeg MutableValTASeg) = return Nothing
      -- The mutable arg seg is valid in the ident address as we might be in the argument environment of a function. For
      -- example, we are reducing a struct field that refers to another in-struct field.
      segToSel (MutableTASeg (MutableArgTASeg _)) = return Nothing
      segToSel RootTASeg = return Nothing
      segToSel seg = throwErrSt $ printf "convert invalid segment %s of addr %s to reference" (show seg) (show addr)
     in
      do
        selMs <- mapM segToSel segs
        return $ Path.Reference $ catMaybes selMs

{- | Trim the address by removing the ending non-string segments. If the address is the root address, return the
address.
-}
trimToStrAddr :: (Env m) => TreeAddr -> m TreeAddr
trimToStrAddr addr
  | isTreeAddrEmpty addr = throwErrSt "already empty address"
  | otherwise =
      let seg = fromJust $ lastSeg addr
       in if
            | seg == RootTASeg -> return addr
            | StructTASeg sseg <- seg, Just _ <- getStrFromSeg sseg -> return addr
            | otherwise -> do
                let newAddr = fromJust $ initTreeAddr addr
                trimToStrAddr newAddr

-- where
--  go _ (ValCursor _ []) = throwErrSt "already at the top"
--  go inited tc@(ValCursor _ ((seg, _) : _))
--    | seg == RootTASeg = return $ tcTreeAddr tc
--    | (StructTASeg sseg) <- seg, Just _ <- getStrFromSeg sseg, not inited = return $ tcTreeAddr tc
--    | otherwise = go False $ fromJust $ parentTC tc

traverseTC :: (Env m) => (TreeCursor Tree -> m Tree) -> TreeCursor Tree -> m (TreeCursor Tree)
traverseTC f tc = do
  newFocus <- f tc
  let
    subs = subNodes newFocus
    utc = newFocus <$ tc
  foldM
    ( \acc (seg, sub) ->
        traverseTC f (mkSubTC seg sub acc) >>= propValUp
    )
    utc
    subs

-- rewriteLetNames :: (TreeMonad s m) => TreeCursor Tree -> m (TreeCursor Tree)
-- rewriteLetNames tc =
--   let t = vcFocus tc
--    in case treeNode t of
--         TNStruct struct -> undefined
--         _ -> undefined

{- | Convert the reference target to absolute tree addr.

The target might not exist at the time, but the first identifier must be found, which means this function should be
called when the first identifier is already found.
-}
mustRefToAbsAddr :: (TreeMonad s m) => Path.Reference -> m TreeAddr
mustRefToAbsAddr ref = do
  let fstSel = fromJust $ headSel ref
  resM <- searchTMVar fstSel
  fstSegAbsAddr <-
    maybe
      (throwErrSt $ printf "reference %s is not found" (show fstSel))
      (return . fst)
      resM
  return $
    maybe
      fstSegAbsAddr
      (\rest -> refToAddr rest `appendTreeAddr` fstSegAbsAddr)
      (tailRef ref)

locateRefAndRun :: (TreeMonad s m) => Path.Reference -> m (Either Tree (Maybe a)) -> m (Either Tree (Maybe a))
locateRefAndRun ref f = do
  origAbsAddr <- getTMAbsAddr
  tarE <- goLAAddrTM ref
  res <- case tarE of
    -- modify the tree focus if it is an error.
    Left err -> return $ Left err
    Right False -> return $ Right Nothing
    Right True -> f
  backM <- goTMAbsAddr origAbsAddr
  unless backM $ throwErrSt $ printf "failed to go back to the original addr %s" (show origAbsAddr)
  return res

-- | Locate the node in the lowest ancestor tree by specified addr. The addr must start with a locatable var.
goLAAddrTM :: (TreeMonad s m) => Path.Reference -> m (Either Tree Bool)
goLAAddrTM ref = do
  when (isRefEmpty ref) $ throwErrSt "empty reference"
  let fstSel = fromJust $ headSel ref
  tc <- getTMCursor
  searchTCVar fstSel tc >>= \case
    Nothing -> return . Left $ mkBottomTree $ printf "identifier %s is not found" (show fstSel)
    Just (varTC, _) -> do
      -- var must be found. Mark the var as referred if it is a let binding.
      putTMCursor $ markTCFocusReferred varTC
      -- The ref is non-empty, so the rest must be a valid addr.
      let rest = fromJust $ tailRef ref
      r <- descendTM (refToAddr rest)
      return $ Right r

addrHasDef :: TreeAddr -> Bool
addrHasDef p =
  any
    ( \case
        StructTASeg (StringTASeg s) -> fromMaybe False $ do
          typ <- getFieldType s
          return $ typ == SFTDefinition
        _ -> False
    )
    $ addrToList p

-- | Mark the let binding specified by the its name selector as referred if the focus of the cursor is a let binding.
markTCFocusReferred :: TreeCursor Tree -> TreeCursor Tree
markTCFocusReferred tc@(ValCursor sub ((seg@(StructTASeg (LetTASeg name)), par) : cs)) =
  maybe
    tc
    ( \struct ->
        let newPar = setTN par (TNStruct $ markLocalReferred name struct)
         in -- sub is not changed.
            ValCursor sub ((seg, newPar) : cs)
    )
    (getStructFromTree par)
markTCFocusReferred tc = tc

{- | Search in the tree for the first variable that can match the segment. Also return if the variable is a let
binding.
-}
searchTMVar :: (TreeMonad s m) => Selector -> m (Maybe (TreeAddr, Bool))
searchTMVar sel = do
  tc <- getTMCursor
  resM <- searchTCVar sel tc
  return $ (\(rtc, isLB) -> Just (tcTreeAddr rtc, isLB)) =<< resM

{- | Search in the parent scope for the first variable that can match the segment. Also return if the variable is a
 - let binding.
-}
searchTMVarInPar :: (TreeMonad s m) => Selector -> m (Maybe (TreeAddr, Bool))
searchTMVarInPar sel = do
  ptc <- getTMCursor >>= propValUp
  resM <- searchTCVar sel ptc
  return $ (\(rtc, isLB) -> Just (tcTreeAddr rtc, isLB)) =<< resM

{- | Search the tree cursor up to the root and return the tree cursor that points to the variable and a boolean
 - indicating if the variable is a let binding.

The cursor will also be propagated to the parent block.
-}
searchTCVar :: (Env m) => Selector -> TreeCursor Tree -> m (Maybe (TreeCursor Tree, Bool))
searchTCVar sel@(StringSel name) tc = do
  -- logDebugStr $ printf "searchTCVar: %s, tc: %s" name (show tc)
  maybe
    (goUp tc)
    (\(field, isLB) -> return $ Just (mkSubTC (mkSeg isLB) field tc, isLB))
    (getStructField name $ vcFocus tc)
 where
  mkSeg isLB = StructTASeg $ if isLB then LetTASeg name else StringTASeg name

  goUp :: (Env m) => TreeCursor Tree -> m (Maybe (TreeCursor Tree, Bool))
  goUp (ValCursor _ [(RootTASeg, _)]) = return Nothing
  goUp utc = propValUp utc >>= searchTCVar sel
searchTCVar _ _ = return Nothing

-- | Go to the absolute addr in the tree.
goTMAbsAddr :: (TMonad s m t, Show t) => TreeAddr -> m Bool
goTMAbsAddr dst = do
  when (headSeg dst /= Just RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  propUpTMUntilSeg RootTASeg
  let dstNoRoot = fromJust $ tailTreeAddr dst
  descendTM dstNoRoot

{- | Return the ref node addr by removing the last mutable value env segment.

For example, /.../p/fv should return /.../p.

It should only be used get the referable part of the source address because deref is called in the /fv environment.
-}
refNodeAddr :: TreeAddr -> TreeAddr
refNodeAddr p =
  fromMaybe
    p
    ( do
        lseg <- lastSeg p
        if isMutValSeg lseg
          then initTreeAddr p
          else return p
    )
 where
  isMutValSeg :: TASeg -> Bool
  isMutValSeg (MutableTASeg MutableValTASeg) = True
  isMutValSeg _ = False

{- | Convert the address to finalized address. Finalized address is the address for finalized value, meaning all the
mutval segments are removed.
-}
finalizedAddr :: TreeAddr -> TreeAddr
finalizedAddr p = TreeAddr $ filter (not . isMutValSeg) $ getTreeSegs p
 where
  isMutValSeg :: TASeg -> Bool
  isMutValSeg (MutableTASeg MutableValTASeg) = True
  isMutValSeg _ = False

evalExprTM :: (TreeMonad s m) => AST.Expression -> m Tree
evalExprTM e = do
  Config{cfEvalExpr = evalExpr} <- ask
  curSID <- getTMScopeID
  (rawT, newSID) <- runStateT (evalExpr e) curSID
  setTMScopeID newSID
  return rawT
