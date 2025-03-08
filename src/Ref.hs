{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Ref (
  deref,
  drainNotifQueue,
  evalExprTM,
  notify,
  searchTMVarInPar,
  traverseTC,
)
where

import qualified AST
import Class (BuildASTExpr (buildASTExpr), TreeOp (isTreeBottom))
import Config (
  Config (cfFunctions),
  Functions (Functions, fnEvalExpr, fnReduce),
 )
import Control.Monad (foldM, unless, void, when)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (StateT, evalStateT, get, modify, put, runStateT)
import Control.Monad.Trans (lift)
import Cursor (
  Context (ctxNotifGraph, ctxReduceStack),
  TreeCursor,
  ValCursor (ValCursor, vcFocus),
  addCtxNotifier,
  isTCTop,
  mkSubTC,
  parentTC,
  propUpTC,
  tcTreeAddr,
 )
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Set as Set
import Env (Env)
import Exception (throwErrSt)
import Mutate (delNotifRecvPrefix)
import Path (
  MutableTASeg (MutableArgTASeg),
  Reference,
  Selector (StringSel),
  StructTASeg (LetTASeg, StringTASeg),
  TASeg (MutableTASeg, RootTASeg, StructTASeg),
  TreeAddr (TreeAddr),
  addrToNormOrdList,
  appendRefs,
  appendTreeAddr,
  canonicalizeAddr,
  headSeg,
  headSel,
  isPrefix,
  isRefEmpty,
  refToAddr,
  referableAddr,
  tailRef,
  tailTreeAddr,
 )
import TMonad (
  TreeMonad,
  descendTM,
  getTMAbsAddr,
  getTMContext,
  getTMCrumbs,
  getTMCursor,
  getTMNotifEnabled,
  getTMNotifQ,
  getTMObjID,
  getTMTree,
  inTempSubTM,
  popTMNotifQ,
  propUpTM,
  propUpTMUntilSeg,
  putTMContext,
  putTMCursor,
  putTMTree,
  setTMNotifEnabled,
  setTMObjID,
  withAddrAndFocus,
  withTree,
 )
import Text.Printf (printf)
import Util (debugSpan, logDebugStr)
import Value.Tree (
  AtomCnstr (cnsAtom, cnsOrigAtom),
  Mutable (Ref),
  RefCycle (RefCycleHori, RefCycleVertMerger),
  Reference (refOrigAddrs, refPath),
  Struct (stcClosed),
  StructFieldType (SFTDefinition),
  StructuralCycle (StructuralCycle),
  Tree (treeExpr, treeNode, treeRecurClosed),
  TreeNode (
    TNAtom,
    TNAtomCnstr,
    TNBottom,
    TNMutable,
    TNRefCycle,
    TNStruct,
    TNStructuralCycle
  ),
  getFieldType,
  getMutableFromTree,
  getRefFromMutable,
  getStructField,
  getStructFromTree,
  markLetBindReferred,
  mkAtomVTree,
  mkBottomTree,
  mkMutableTree,
  mkRefMutable,
  setTN,
  subNodes,
  treesToRef,
 )

{- | Notify dependents of the change of the value.

It will try all parent nodes to notify the dependents.
-}
notify :: (TreeMonad s m) => m ()
notify = withAddrAndFocus $ \addr _ -> debugSpan (printf "notify: addr: %s" (show addr)) $ do
  origNotifEnabled <- getTMNotifEnabled
  setTMNotifEnabled False
  let
    visiting = [addr]
    -- The initial node has already been reduced.
    q = [(addr, False)]

  evalStateT bfsLoopQ (BFSState visiting q)
  setTMNotifEnabled origNotifEnabled

data BFSState = BFSState
  { _bfsVisiting :: [TreeAddr]
  , bfsQueue :: [(TreeAddr, Bool)]
  }

type BFSMonad m a = StateT BFSState m a

bfsLoopQ :: (TreeMonad s m) => BFSMonad m ()
bfsLoopQ = do
  state@(BFSState{bfsQueue = q}) <- get
  case q of
    [] -> return ()
    ((addr, toReduce) : xs) -> do
      put state{bfsQueue = xs}
      addrFound <-
        lift $ do
          logDebugStr $ printf "bfsLoopQ: visiting addr: %s" (show addr)
          addrFound <-
            inAbsAddrTM addr (when toReduce reduceLAMut)
              >>= maybe
                ( do
                    -- Remove the notification if the receiver is not found. The receiver might be relocated. For
                    -- example, the receiver could first be reduced in a unifying function reducing arguments phase with
                    -- addr a/fa0. Then the receiver is relocated to a due to unifying fields.
                    delNotifRecvPrefix addr
                    return False
                )
                (const $ return True)
          logDebugStr $ printf "bfsLoopQ: visiting addr: %s, found: %s" (show addr) (show addrFound)
          return addrFound

      when
        addrFound
        ( do
            upUntilRoot
            void . lift $ goTMAbsAddr addr
        )
      bfsLoopQ
 where
  -- Check all the ancestors to notify the dependents.
  -- Notice that it changes the tree focus. After calling the function, the caller should restore the focus.
  upUntilRoot :: (TreeMonad s m) => BFSMonad m ()
  upUntilRoot = do
    cs <- lift getTMCrumbs
    -- We should not use root value to notify.
    when (length cs > 1) $ do
      recvs <- lift $ do
        notifyG <- ctxNotifGraph <$> getTMContext
        addr <- getTMAbsAddr
        let
          -- We need to use the finalized addr to find the notifiers so that some dependents that reference on the
          -- finalized address can be notified.
          -- For example, { a: r, r: y:{}, p: a.y}. p's a.y references the finalized address while a's value might
          -- always have address of /a/fv/y.
          srcFinalizedAddr = referableAddr addr
        return $ fromMaybe [] (Map.lookup srcFinalizedAddr notifyG)

      -- The current focus notifying its dependents means it is referred.
      unless (null recvs) $ lift markReferred

      -- Add the receivers to the visited list and the queue.
      modify $ \state ->
        foldr
          ( \recv s@(BFSState v q) ->
              if recv `notElem` v
                then
                  BFSState (recv : v) (q ++ [(recv, True)])
                else s
          )
          state
          recvs

      inReducing <- lift $ do
        ptc <- getTMCursor
        -- We must check if the parent is reducing. If the parent is reducing, we should not go up and keep
        -- notifying the dependents.
        -- Because once parent is done with reducing, it will notify its dependents.
        parentIsReducing $ tcTreeAddr ptc

      unless inReducing $ do
        lift propUpTM
        upUntilRoot

  markReferred :: (TreeMonad s m) => m ()
  markReferred = do
    tc <- getTMCursor
    putTMCursor $ markTCFocusReferred tc

  parentIsReducing parTreeAddr = do
    stack <- ctxReduceStack <$> getTMContext
    return $ length stack > 1 && stack !! 1 == parTreeAddr

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
        =<< inAbsAddrTM addr notify

      drainNotifQueue

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrTM :: (TreeMonad s m) => TreeAddr -> m a -> m (Maybe a)
inAbsAddrTM p f = do
  origAbsAddr <- getTMAbsAddr

  tarM <- whenM (goTMAbsAddr p) f
  backOk <- goTMAbsAddr origAbsAddr
  unless backOk $ do
    throwErrSt $
      printf
        "failed to go back to the original addr %s, dest: %s"
        (show origAbsAddr)
        (show p)
  return tarM
 where
  whenM :: (TreeMonad s m) => m Bool -> m a -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then Just <$> g else return Nothing

inAbsAddrTMMust :: (TreeMonad s m) => TreeAddr -> m a -> m a
inAbsAddrTMMust p f = do
  r <- inAbsAddrTM p f
  maybe (throwErrSt $ printf "addr %s not found" (show p)) return r

reduceLAMut :: (TreeMonad s m) => m ()
reduceLAMut = do
  from <- getTMAbsAddr
  -- Locate the lowest ancestor mutable to trigger the re-evaluation of the ancestor mutable.
  -- Notice the tree focus now changes to the LA mutable.
  locateLAMutable
  addr <- getTMAbsAddr
  Functions{fnReduce = reduce} <- asks cfFunctions
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
detected.

If the target is found, a copy of the target value is put to the tree.

The target address is also returned.
-}
deref ::
  (TreeMonad s m) =>
  -- | the reference addr
  Path.Reference ->
  Maybe (TreeAddr, TreeAddr) ->
  m (Maybe TreeAddr)
deref ref origAddrsM = withAddrAndFocus $ \addr _ ->
  debugSpan (printf "deref: addr: %s, origValAddr: %s, ref: %s" (show addr) (show origAddrsM) (show ref)) $ do
    -- Add the notifier anyway.
    addNotifier ref origAddrsM

    let refAddr = referableAddr addr
    rE <- getDstVal ref origAddrsM (Set.fromList [refAddr])
    case rE of
      Left err -> putTMTree err >> return Nothing
      Right Nothing -> return Nothing
      Right (Just (tarAddr, tar)) -> do
        logDebugStr $ printf "deref: addr: %s, ref: %s, target is found: %s" (show addr) (show ref) (show tar)
        putTMTree tar
        return $ Just tarAddr

{- | Add a notifier to the context.

If the referenced value changes, then the reference should be updated. Duplicate cases are handled by the
addCtxNotifier.
-}
addNotifier :: (TreeMonad s m) => Path.Reference -> Maybe (TreeAddr, TreeAddr) -> m ()
addNotifier ref origAddrsM = do
  srcAddrM <- refToPotentialAddr ref origAddrsM >>= \x -> return $ referableAddr <$> x
  -- Since we are in the /fv environment, we need to get the referable addr.
  recvAddr <- referableAddr <$> getTMAbsAddr

  maybe
    (logDebugStr $ printf "addNotifier: ref %s is not found" (show ref))
    ( \srcAddr -> do
        ctx <- getTMContext
        putTMContext $ addCtxNotifier ctx (srcAddr, recvAddr)
        logDebugStr $ printf "addNotifier: (%s -> %s)" (show srcAddr) (show recvAddr)
    )
    srcAddrM

{- | Get the value pointed by the reference.

If the reference addr is self or visited, then return the tuple of the absolute addr of the start of the cycle and
the cycle tail relative addr.
-}
getDstVal ::
  (TreeMonad s m) =>
  Path.Reference ->
  -- | The original addresses of the reference.
  Maybe (TreeAddr, TreeAddr) ->
  -- | keeps track of the followed *referable* addresses.
  Set.Set TreeAddr ->
  m (Either Tree (Maybe (TreeAddr, Tree)))
getDstVal ref origAddrsM trail = withAddrAndFocus $ \srcAddr _ ->
  debugSpan
    ( printf
        "deref_getDstVal: addr: %s, ref: %s, origSubTAddr: %s, trail: %s"
        (show srcAddr)
        (show ref)
        (show origAddrsM)
        (show $ Set.toList trail)
    )
    $ do
      recurClose <- treeRecurClosed <$> getTMTree
      let f = locateRefAndRun ref (fetch srcAddr recurClose)
      rE <-
        maybe
          f
          ( \(origSubTAddr, origValAddr) -> inAbsAddrTMMust origSubTAddr $ do
              -- If the ref is an outer reference inside the referenced value, we should check if the ref leads to
              -- infinite structure (structural cycle). For example, x: a, y: 1, a: {b: y}, the y in the struct a is an
              -- outer reference.
              infE <- locateRefAndRun ref (checkInf srcAddr origValAddr)
              rE <- f
              return $ infE >> rE
          )
          origAddrsM
      case rE of
        Right (Just (dstAddr, tar)) -> tryFollow rE dstAddr tar
        _ -> return rE
 where
  -- Check if the reference leads to a structural cycle. If it does, return the cycle with the start address being the
  -- srcAddr, which is the current ref's addr.
  checkInf srcAddr origValAddr = do
    dstAddr <- getTMAbsAddr
    let
      canSrcAddr = canonicalizeAddr origValAddr
      canDstAddr = canonicalizeAddr dstAddr

    t <- getTMTree
    let
      r :: Either Tree (Maybe (TreeAddr, Tree))
      r =
        -- Pointing to ancestor generates a structural cycle. Notice that dstAddr can be equal to srcAddr because
        -- the srcAddr is the original value address which is the the scope address. Any internal reference actually
        -- has this addr.
        if isPrefix canDstAddr canSrcAddr && canSrcAddr /= canDstAddr
          then Left (setTN t $ TNStructuralCycle $ StructuralCycle srcAddr)
          else Right Nothing

    logDebugStr $
      printf
        "deref_getDstVal checkInf, ref: %s, origValAddr: %s, dst: %s, result: %s"
        (show ref)
        (show origValAddr)
        (show dstAddr)
        (show r)

    return r

  -- Fetch the value of the reference.
  fetch srcAddr recurClose = do
    dstAddr <- getTMAbsAddr
    logDebugStr $
      printf "deref_getDstVal ref: %s, ref is found, src: %s, dst: %s" (show ref) (show srcAddr) (show dstAddr)
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
        | canDstAddr == referableAddr canSrcAddr && srcAddr /= dstAddr -> withTree $ \tar ->
            case treeNode tar of
              -- In the validation phase, the subnode of the Constraint node might find the parent Constraint node.
              TNAtomCnstr c -> return (mkAtomVTree $ cnsOrigAtom c, False)
              _ -> do
                logDebugStr $
                  printf
                    "deref_getDstVal: vertical reference cycle tail detected: %s == %s."
                    (show dstAddr)
                    (show srcAddr)
                return (setTN t $ TNRefCycle (RefCycleVertMerger (dstAddr, srcAddr)), False)
        | isPrefix canDstAddr canSrcAddr && canSrcAddr /= canDstAddr ->
            return
              ( setTN t $ TNStructuralCycle $ StructuralCycle dstAddr
              , False
              )
        | otherwise -> return (t, True)
    r <-
      if noError
        then do
          copyRefVal trail recurClose val
        else
          return val
    return . Right $ Just (dstAddr, r)

  -- Try to follow the reference if the target is a reference or an index.
  tryFollow rE dstAddr tar = case getMutableFromTree tar of
    -- follow the reference.
    Just (Ref rf) -> do
      withAddrAndFocus $ \addr _ ->
        logDebugStr $
          printf
            "deref_getDstVal: addr: %s, dstAddr: %s, follow the new reference: %s"
            (show addr)
            (show dstAddr)
            (show $ refPath rf)
      getDstVal (refPath rf) (refOrigAddrs rf) (Set.insert dstAddr trail)
    Just (SFunc f)
      | IndexMutable <- sfnType f -> do
            nt <- indexerToRef tar

    -- TODO: follow ref in an index.
    -- Just (Index _) -> do
    --   nt <- indexerToRef tar
    --   logDebugStr $ printf "deref_getDstVal: addr: %s, follow the index, index reduced to: %s" (show dstAddr) (show nt)
    --   case getMutableFromTree nt of
    --     Just (Ref _) -> tryFollow rE dstAddr nt
    --     _ -> return rE
    _ -> return rE

-- {- | Convert the indexer to a ref. If the result is not a ref, then return the original tree.

-- When evaluating the index arguments, the index arguments are evaluated in the temp scope.
-- -}
-- indexerToRef :: (TreeMonad s m) => Tree -> m Tree
-- indexerToRef t = case getMutableFromTree t of
--   Just (Index idx) -> go (idxSels idx)
--   _ -> return t
--  where
--   evalIndexArg :: (TreeMonad s m) => [Tree] -> Int -> m Tree
--   evalIndexArg ts i = inTempSubTM (ts !! i) $ do
--     Functions{fnReduce = reduce} <- asks cfFunctions
--     reduce >> getTMTree

--   go :: (TreeMonad s m) => [Tree] -> m Tree
--   go ts@(h : _)
--     | length ts > 1 = do
--         idxRefM <- treesToRef <$> mapM (evalIndexArg ts) [1 .. length ts - 1]
--         logDebugStr $ printf "indexerToRef: idxRefM is %s" (show idxRefM)
--         maybe
--           (return t)
--           ( \idxRef -> case treeNode h of
--               TNMutable mut
--                 -- If the function is a ref, then we should append the addr to the ref. For example, if the ref is a.b, and
--                 -- the addr is c, then the new ref should be a.b.c.
--                 | (Ref ref) <- mut -> do
--                     let
--                       newRef = appendRefs (refPath ref) idxRef
--                       refMutable = mkRefMutable newRef
--                     return (mkMutableTree refMutable)
--               _ -> return t
--           )
--           idxRefM
--   go _ = throwErrSt "invalid index arguments"

{- | Copy the value of the reference from within the dst environment.

dstAddr and trail are used to decide whether to close the deref'd value.

From the spec:
The value of a reference is a copy of the expression associated with the field that it is bound to, with
any references within that expression bound to the respective copies of the fields they were originally
bound to.
-}
copyRefVal :: (TreeMonad s m) => Set.Set TreeAddr -> Bool -> Tree -> m Tree
copyRefVal trail recurClose tar = do
  case treeNode tar of
    -- The atom value is final, so we can just return it.
    TNAtom _ -> return tar
    TNBottom _ -> return tar
    TNAtomCnstr c -> return (mkAtomVTree $ cnsAtom c)
    _ -> do
      dstAddr <- getTMAbsAddr
      -- evaluate the original expression.
      orig <- evalTarExpr
      let visited = Set.insert dstAddr trail
      val <- checkRefDef orig visited

      withAddrAndFocus $ \addr _ ->
        logDebugStr $
          printf
            "deref: addr: %s, deref's copy is: %s, visited: %s, tar: %s"
            (show addr)
            (show val)
            (show $ Set.toList visited)
            (show tar)
      return val
 where
  evalTarExpr = do
    raw <-
      maybe (buildASTExpr False tar) return (treeExpr tar)
        >>= evalExprTM

    tc <- getTMCursor
    markOuterIdents raw tc

  checkRefDef orig visited = do
    let shouldClose = any addrHasDef visited
    if shouldClose || recurClose
      then do
        withAddrAndFocus $ \addr _ ->
          logDebugStr $
            printf
              "deref: addr: %s, visitedRefs: %s, has definition or recurClose: %s is set, recursively close the value. %s"
              (show addr)
              (show $ Set.toList visited)
              (show recurClose)
              (show orig)
        tc <- getTMCursor
        markRecurClosed orig tc
      else return orig

{- | Mark all outer references inside a container node with original value address.

The outer references are the nodes inside a container pointing to the ancestors.
-}
markOuterIdents ::
  (Env m) =>
  -- | The new evaluated value.
  Tree ->
  -- | The current tree cursor.
  TreeCursor Tree ->
  m Tree
markOuterIdents val ptc = do
  let subtAddr = tcTreeAddr ptc
  utc <- traverseTC (mark subtAddr) (val <$ ptc)
  logDebugStr $
    printf "markOuterRefs: scope: %s, val: %s, result: %s" (show subtAddr) (show val) (show $ vcFocus utc)
  return $ vcFocus utc
 where
  -- Mark the outer references with the original value address.
  mark :: (Env m) => TreeAddr -> TreeCursor Tree -> m Tree
  mark subtAddr tc = do
    let focus = vcFocus tc
    rM <- case getMutableFromTree focus of
      Just (Ref rf) -> return $ Just (rf, \as -> setTN focus $ TNMutable . Ref $ rf{refOrigAddrs = Just as})
      -- Just (Index idx) -> do
      --   let identT = idxSels idx !! 0
      --   case getMutableFromTree identT of
      --     Just (Ref rf) -> return $ Just (rf, \as -> setTN focus $ TNMutable . Index $ idx{idxOrigAddrs = Just as})
      --     _ -> throwErrSt $ printf "invalid index argument: %s" (show identT)
      _ -> return Nothing
    maybe
      (return focus)
      ( \(rf, f) -> do
          isOuter <- isOuterScope subtAddr tc rf
          if isOuter
            then return $ f (subtAddr, tcTreeAddr tc)
            else return focus
      )
      rM

  -- Check if the reference is an outer reference.
  isOuterScope ::
    (Env m) =>
    -- The sub-tree address. It is the container node address.
    TreeAddr ->
    TreeCursor Tree ->
    Value.Tree.Reference Tree ->
    m Bool
  isOuterScope subtAddr tc rf = do
    tarIdentAddrM <- searchIdent (refPath rf) tc
    isOuter <-
      maybe
        (return False)
        ( \tarIdentAddr -> do
            let tarIdentInVarScope = isPrefix subtAddr tarIdentAddr && tarIdentAddr /= subtAddr
            return $ not tarIdentInVarScope
        )
        tarIdentAddrM
    logDebugStr $
      printf
        "markOuterRefs: ref to mark: %s, cursor_addr: %s, subtAddr: %s, tarIdentAddrM: %s, isOuterScope: %s"
        (show $ refPath rf)
        (show $ tcTreeAddr tc)
        (show subtAddr)
        (show tarIdentAddrM)
        (show isOuter)
    return isOuter

  -- Search the first identifier of the reference and convert it to absolute tree addr if it exists.
  searchIdent :: (Env m) => Path.Reference -> TreeCursor Tree -> m (Maybe TreeAddr)
  searchIdent ref tc = do
    let fstSel = fromJust $ headSel ref
    var <- selToVar fstSel
    resM <- searchTCVar var tc
    return $ fst <$> resM

markRecurClosed :: (Env m) => Tree -> TreeCursor Tree -> m Tree
markRecurClosed val ptc = do
  utc <- traverseTC mark (val <$ ptc)
  return $ vcFocus utc
 where
  mark :: (Env m) => TreeCursor Tree -> m Tree
  mark tc = do
    let focus = vcFocus tc
    return $
      focus
        { treeRecurClosed = True
        , treeNode = case treeNode focus of
            TNStruct struct -> TNStruct $ struct{stcClosed = True}
            _ -> treeNode focus
        }

{- | Visit every node in the tree in pre-order and apply the function.

It does not constrain struct fields.
-}
traverseTC :: (Env m) => (TreeCursor Tree -> m Tree) -> TreeCursor Tree -> m (TreeCursor Tree)
traverseTC f tc = do
  newFocus <- f tc
  let
    subs = subNodes newFocus
    utc = newFocus <$ tc
  foldM
    ( \acc (seg, sub) ->
        traverseTC f (mkSubTC seg sub acc) >>= propUpTC
    )
    utc
    subs

{- | Convert the reference target to absolute tree addr.

It does not follow the reference.
-}
refToPotentialAddr :: (TreeMonad s m) => Path.Reference -> Maybe (TreeAddr, TreeAddr) -> m (Maybe TreeAddr)
refToPotentialAddr ref origAddrsM = do
  let fstSel = fromJust $ headSel ref
  var <- selToVar fstSel
  let f = searchTMVar var >>= (\x -> return $ fst <$> x)

  -- Search the address of the first identifier, whether from the current env or the original env.
  fstSegAbsAddrM <- maybe f (\(origSubTAddr, _) -> inAbsAddrTMMust origSubTAddr f) origAddrsM

  -- If the first segment is not found, return Nothing.
  return $
    fstSegAbsAddrM
      >>= ( \fstSegAbsAddr ->
              Just $
                maybe
                  fstSegAbsAddr
                  (\rest -> refToAddr rest `appendTreeAddr` fstSegAbsAddr)
                  (tailRef ref)
          )

-- | Locate the reference and if the reference is found, run the action.
locateRefAndRun :: (TreeMonad s m) => Path.Reference -> m (Either Tree (Maybe a)) -> m (Either Tree (Maybe a))
locateRefAndRun ref f = do
  origAbsAddr <- getTMAbsAddr
  tarE <- goLAAddrTM ref
  res <- case tarE of
    -- modify the tree focus if it is an error.
    Left err -> return $ Left err
    Right False -> return $ Right Nothing
    Right True -> f

  ok <- goTMAbsAddr origAbsAddr
  unless ok $ throwErrSt $ printf "failed to go back to the original addr %s" (show origAbsAddr)
  return res

{- | Locate the node in the lowest ancestor tree by specified addr. The addr must start with a locatable var.

TODO: move the mark refered logic to descendTM
-}
goLAAddrTM :: (TreeMonad s m) => Path.Reference -> m (Either Tree Bool)
goLAAddrTM ref = do
  when (isRefEmpty ref) $ throwErrSt "empty reference"
  let fstSel = fromJust $ headSel ref
  var <- selToVar fstSel
  tc <- getTMCursor
  searchTCVar var tc >>= \case
    Nothing -> return . Left $ mkBottomTree $ printf "identifier %s is not found" (show fstSel)
    Just (varAddr, _) -> do
      ok <- goTMAbsAddr varAddr
      unless ok $ throwErrSt $ printf "failed to go to the var addr %s" (show varAddr)
      varTC <- getTMCursor
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
    $ addrToNormOrdList p

-- | Mark the let binding specified by the its name selector as referred if the focus of the cursor is a let binding.
markTCFocusReferred :: TreeCursor Tree -> TreeCursor Tree
markTCFocusReferred tc@(ValCursor sub ((seg@(StructTASeg (LetTASeg name)), par) : cs)) =
  maybe
    tc
    ( \struct ->
        let newPar = setTN par (TNStruct $ markLetBindReferred name struct)
         in -- sub is not changed.
            ValCursor sub ((seg, newPar) : cs)
    )
    (getStructFromTree par)
markTCFocusReferred tc = tc

selToVar :: (Env m) => Selector -> m String
selToVar (StringSel s) = return s
selToVar _ = throwErrSt "invalid selector"

{- | Search in the tree for the first variable that can match the name.

Return if the variable is a let binding.
-}
searchTMVar :: (TreeMonad s m) => String -> m (Maybe (TreeAddr, Bool))
searchTMVar name = do
  tc <- getTMCursor
  searchTCVar name tc

-- resM <- searchTCVar sel tc
-- return $ (\(rtc, isLB) -> Just (tcTreeAddr rtc, isLB)) =<< resM

{- | Search in the parent scope for the first variable that can match the segment. Also return if the variable is a
 - let binding.
-}
searchTMVarInPar :: (TreeMonad s m) => String -> m (Maybe (TreeAddr, Bool))
searchTMVarInPar name = do
  ptc <- do
    tc <- getTMCursor
    maybe (throwErrSt "already on the top") return $ parentTC tc
  if isTCTop ptc
    then return Nothing
    else searchTCVar name ptc

{- | Search in the tree for the first variable that can match the name.

Return a pair. The first is address of the variable, the second is the variable is a let binding.

The child value will not be propagated to the parent block. Propagation is not needed because all static fields should
already exist.

The tree cursor must at least have the root segment.
-}
searchTCVar :: (Env m) => String -> TreeCursor Tree -> m (Maybe (TreeAddr, Bool))
searchTCVar name tc = do
  maybe
    (goUp tc)
    ( \(field, isLB) ->
        let
          -- The var address is the address of the field, with the updated segment paired with the it.
          newTC = mkSubTC (mkSeg isLB) field tc
         in
          return $ Just (tcTreeAddr newTC, isLB)
    )
    (getStructField name $ vcFocus tc)
 where
  mkSeg isLB = StructTASeg $ if isLB then LetTASeg name else StringTASeg name

  goUp :: (Env m) => TreeCursor Tree -> m (Maybe (TreeAddr, Bool))
  goUp (ValCursor _ [(RootTASeg, _)]) = return Nothing -- stop at the root.
  goUp utc = do
    ptc <- maybe (throwErrSt "already on the top") return $ parentTC utc
    searchTCVar name ptc

-- | Go to the absolute addr in the tree.
goTMAbsAddr :: (TreeMonad s m) => TreeAddr -> m Bool
goTMAbsAddr dst = do
  when (headSeg dst /= Just RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  propUpTMUntilSeg RootTASeg
  let dstNoRoot = fromJust $ tailTreeAddr dst
  descendTM dstNoRoot

evalExprTM :: (TreeMonad s m) => AST.Expression -> m Tree
evalExprTM e = do
  Functions{fnEvalExpr = evalExpr} <- asks cfFunctions
  curSID <- getTMObjID
  (rawT, newOID) <- runStateT (evalExpr e) curSID
  setTMObjID newOID
  return rawT
