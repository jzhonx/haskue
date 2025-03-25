{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RefSys where

import qualified AST
import Common (BuildASTExpr (buildASTExpr), Env, TreeOp (isTreeBottom))
import Control.Monad (unless, when)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (StateT, evalStateT, get, modify, put, runStateT)
import Control.Monad.Trans (lift)
import Cursor (
  Context (ctxReduceStack, ctxRefSysGraph),
  TreeCursor,
  ValCursor (ValCursor, vcFocus),
  addCtxNotifiers,
  isTCTop,
  mkSubTC,
  parentTC,
  tcTreeAddr,
 )
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe, isNothing)
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified TCursorOps
import Text.Printf (printf)
import Util (debugSpan, getTraceID, logDebugStr)
import qualified Value.Tree as VT

{- | RefSysy starts notification propagation in the tree.

The propagation is done in a breadth-first manner. It first reduces the current visiting node if needed and then
propagates to the dependents of the visiting node and the dependents of its ancestors.

The propagation starts from the current focus.
-}
notify :: (RM.ReduceMonad s r m) => m ()
notify = RM.withAddrAndFocus $ \addr _ -> debugSpan (printf "notify: addr: %s" (show addr)) $ do
  origRefSysEnabled <- RM.getRMRefSysEnabled
  -- Disable the notification to avoid notifying the same node multiple times.
  RM.setRMRefSysEnabled False
  let
    visiting = [addr]
    -- The initial node has already been reduced.
    q = [(addr, False)]

  tid <- getTraceID
  evalStateT (bfsLoopQ tid) (BFSState visiting q)
  RM.setRMRefSysEnabled origRefSysEnabled

data BFSState = BFSState
  { _bfsVisiting :: [Path.TreeAddr]
  , bfsQueue :: [(Path.TreeAddr, Bool)]
  }

type BFSMonad m a = StateT BFSState m a

bfsLoopQ :: (RM.ReduceMonad s r m) => Int -> BFSMonad m ()
bfsLoopQ tid = do
  state@(BFSState{bfsQueue = q}) <- get
  case q of
    [] -> return ()
    ((addr, toReduce) : xs) -> do
      put state{bfsQueue = xs}

      origAddr <- lift RM.getRMAbsAddr
      -- First try to go to the addr.
      found <- lift $ goRMAbsAddr addr
      if found
        then do
          when toReduce (lift reduceImParMut)
          -- Adding new deps should be in the exact environment of the result of the reduceImParMut.
          addDepsUntilRoot
        else
          -- Remove the notification if the receiver is not found. The receiver might be relocated. For
          -- example, the receiver could first be reduced in a unifying function reducing arguments phase with
          -- addr a/fa0. Then the receiver is relocated to "/a" due to unifying fields.
          lift $ Mutate.delRefSysRecvPrefix addr

      -- We must go back to the original addr even when the addr is not found, because that would lead to unexpected
      -- address.
      lift $ goRMAbsAddrMust origAddr
      logDebugStr $ printf "id=%s, bfsLoopQ: visiting addr: %s, found: %s" (show tid) (show addr) (show found)
      bfsLoopQ tid
 where
  -- Add the dependents of the current focus and its ancestors to the visited list and the queue.
  -- Notice that it changes the tree focus. After calling the function, the caller should restore the focus.
  addDepsUntilRoot :: (RM.ReduceMonad s r m) => BFSMonad m ()
  addDepsUntilRoot = do
    cs <- lift RM.getRMCrumbs
    -- We should not use root value to notify.
    when (length cs > 1) $ do
      recvs <- lift $ do
        notifyG <- ctxRefSysGraph <$> RM.getRMContext
        addr <- RM.getRMAbsAddr
        -- We need to use the finalized addr to find the notifiers so that some dependents that reference on the
        -- finalized address can be notified.
        -- For example, { a: r, r: y:{}, p: a.y}. p's a.y references the finalized address while a's value might
        -- always have address of /a/sv/y.
        return $
          fromMaybe
            []
            ( do
                srcFinalizedAddr <- Path.referableAddr addr
                Map.lookup srcFinalizedAddr notifyG
            )

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
        ptc <- RM.getRMCursor
        -- We must check if the parent is reducing. If the parent is reducing, we should not go up and keep
        -- notifying the dependents.
        -- Because once parent is done with reducing, it will notify its dependents.
        parentIsReducing $ tcTreeAddr ptc

      unless inReducing $ do
        lift RM.propUpRM
        addDepsUntilRoot

  parentIsReducing parTreeAddr = do
    stack <- ctxReduceStack <$> RM.getRMContext
    return $ length stack > 1 && stack !! 1 == parTreeAddr

drainRefSysQueue :: (RM.ReduceMonad s r m) => m ()
drainRefSysQueue = do
  q <- RM.getRMRefSysQ
  more <- RM.withAddrAndFocus $ \daddr _ ->
    debugSpan (printf "drainRefSysQueue: addr: %s, q: %s" (show daddr) (show q)) $ do
      headM <- RM.popRMRefSysQ
      case headM of
        Nothing -> return False
        Just addr -> do
          logDebugStr $ printf "drainRefSysQueue: addr: %s" (show addr)
          maybe
            (logDebugStr $ printf "drainRefSysQueue: addr: %s, not found" (show addr))
            (const $ return ())
            =<< inAbsAddrRM addr notify
          return True

  when more drainRefSysQueue

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrRM :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m a -> m (Maybe a)
inAbsAddrRM p f = do
  origAbsAddr <- RM.getRMAbsAddr

  tarM <- whenM (goRMAbsAddr p) f
  backOk <- goRMAbsAddr origAbsAddr
  unless backOk $ do
    throwErrSt $
      printf
        "failed to go back to the original addr %s, dest: %s"
        (show origAbsAddr)
        (show p)
  return tarM
 where
  whenM :: (RM.ReduceMonad s r m) => m Bool -> m a -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then Just <$> g else return Nothing

inAbsAddrRMMust :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m a -> m a
inAbsAddrRMMust p f = do
  r <- inAbsAddrRM p f
  maybe (throwErrSt $ printf "addr %s not found" (show p)) return r

-- | Reduce the immediate parent mutable.
reduceImParMut :: (RM.ReduceMonad s r m) => m ()
reduceImParMut = do
  -- Locate immediate parent mutable to trigger the re-evaluation of the parent mutable.
  -- Notice the tree focus now changes to the Im mutable.
  locateImMutable
  addr <- RM.getRMAbsAddr
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNMutable mut
      | Just _ <- VT.getRefFromMutable mut -> do
          logDebugStr $
            printf "reduceImParMut: ImPar is a reference, addr: %s, node: %s" (show addr) (show t)
          reduce
      -- re-evaluate the mutable when it is not a reference.
      | otherwise -> do
          logDebugStr $
            printf "reduceImParMut: re-evaluating the ImPar, addr: %s, node: %s" (show addr) (show t)
          reduce
    _ -> logDebugStr "reduceImParMut: ImPar is not found"

-- Locate the immediate parent mutable.
-- TODO: consider the mutable does not have arguments.
locateImMutable :: (RM.ReduceMonad s r m) => m ()
locateImMutable = do
  addr <- RM.getRMAbsAddr
  if hasEmptyTreeAddr addr || not (hasMutableArgSeg addr)
    then return ()
    -- If the addr has mutable argument segments, that means we are in a mutable node.
    else RM.propUpRM >> locateImMutable
 where
  hasEmptyTreeAddr (Path.TreeAddr sels) = null sels
  -- Check if the addr has mutable argument segments.
  hasMutableArgSeg (Path.TreeAddr sels) =
    any
      ( \case
          Path.MutableArgTASeg _ -> True
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
  (RM.ReduceMonad s r m) =>
  -- | the reference addr
  Path.Reference ->
  Maybe (Path.TreeAddr, Path.TreeAddr) ->
  m (Maybe Path.TreeAddr)
deref ref origAddrsM = RM.withAddrAndFocus $ \addr _ ->
  debugSpan (printf "deref: addr: %s, origAddrsM: %s, ref: %s" (show addr) (show origAddrsM) (show ref)) $ do
    -- Add the notifier anyway.
    addNotifiers ref origAddrsM

    let selfAddr = Path.noSubValAddr addr
    rE <- getDstVal ref origAddrsM (Set.fromList [selfAddr])
    case rE of
      Left err -> RM.putRMTree err >> return Nothing
      Right Nothing -> return Nothing
      Right (Just (tarAddr, tar)) -> do
        logDebugStr $ printf "deref: addr: %s, ref: %s, target is found: %s" (show addr) (show ref) (show tar)
        RM.putRMTree tar
        return $ Just tarAddr

{- | Add a notifier to the context.

If the referenced value changes, then the reference should be updated. Duplicate cases are handled by the
addCtxNotifiers.
-}
addNotifiers :: (RM.ReduceMonad s r m) => Path.Reference -> Maybe (Path.TreeAddr, Path.TreeAddr) -> m ()
addNotifiers ref origAddrsM = do
  srcAddrM <-
    refToPotentialAddr ref origAddrsM >>= \xM -> return $ do
      x <- xM
      Path.referableAddr x
  -- Since we are in the /sv environment, we need to get the referable addr.
  recvAddr <- Path.noSubValAddr <$> RM.getRMAbsAddr

  maybe
    (logDebugStr $ printf "addNotifiers: ref %s is not found" (show ref))
    ( \srcAddr -> do
        ctx <- RM.getRMContext
        RM.putRMContext $ addCtxNotifiers ctx (srcAddr, recvAddr)
        logDebugStr $ printf "addNotifiers: (%s -> %s)" (show srcAddr) (show recvAddr)
    )
    srcAddrM

{- | Get the value pointed by the reference.

If the reference addr is self or visited, then return the tuple of the absolute addr of the start of the cycle and
the cycle tail relative addr.
-}
getDstVal ::
  (RM.ReduceMonad s r m) =>
  Path.Reference ->
  -- | The original addresses of the reference.
  Maybe (Path.TreeAddr, Path.TreeAddr) ->
  -- | keeps track of the followed *referable* addresses.
  Set.Set Path.TreeAddr ->
  m (Either VT.Tree (Maybe (Path.TreeAddr, VT.Tree)))
getDstVal ref origAddrsM trail = RM.withAddrAndFocus $ \srcAddr _ ->
  debugSpan
    ( printf
        "deref_getDstVal: addr: %s, ref: %s, origSubTAddr: %s, trail: %s"
        (show srcAddr)
        (show ref)
        (show origAddrsM)
        (show $ Set.toList trail)
    )
    $ do
      recurClose <- VT.treeRecurClosed <$> RM.getRMTree
      let f = locateRefAndRun ref (fetch srcAddr recurClose)
      rE <-
        maybe
          f
          -- If the ref is an outer reference, we should first go to the original value address.
          ( \(origSubTAddr, origValAddr) -> inAbsAddrRMMust origSubTAddr $ do
              -- If the ref is an outer reference inside the referenced value, we should check if the ref leads to
              -- infinite structure (structural cycle).
              -- For example, { x: a, y: 1, a: {b: y} }, where /a is the address of the subt value.
              -- The "y" in the struct {b: y} is an outer reference.
              -- We should first go to the original value address, which is /a/b.
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
  -- The origValAddr is the original value address. See the comment of the caller.
  checkInf srcAddr origValAddr = do
    -- dstAddr is the destination address of the reference.
    dstAddr <- RM.getRMAbsAddr
    let
      canSrcAddr = Path.canonicalizeAddr origValAddr
      canDstAddr = Path.canonicalizeAddr dstAddr

    t <- RM.getRMTree
    let
      r :: Either VT.Tree (Maybe (Path.TreeAddr, VT.Tree))
      r =
        -- Pointing to ancestor generates a structural cycle.
        if Path.isPrefix canDstAddr canSrcAddr && canSrcAddr /= canDstAddr
          then Left (VT.setTN t $ VT.TNStructuralCycle $ VT.StructuralCycle srcAddr)
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
    dstAddr <- RM.getRMAbsAddr
    logDebugStr $
      printf "deref_getDstVal ref: %s, ref is found, src: %s, dst: %s" (show ref) (show srcAddr) (show dstAddr)
    let
      canSrcAddr = Path.canonicalizeAddr srcAddr
      canDstAddr = Path.canonicalizeAddr dstAddr
    t <- RM.getRMTree
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
            return (VT.setTN t $ VT.TNRefCycle (VT.RefCycleHori (dstAddr, srcAddr)), False)
        -- This handles the case when the reference refers to itself that is the ancestor.
        -- For example, { a: a + 1 } or { a: !a }.
        -- The tree representation of the latter is,
        -- { }
        --  | - a
        -- (!)
        --  | - unary_op
        -- ref_a
        -- Notice that for self-cycle, the srcTreeAddr could be /addr/sv, and the dstTreeAddr could be /addr. They
        -- are the same in the refNode form.
        | Just canDstAddr == Path.referableAddr canSrcAddr && srcAddr /= dstAddr -> RM.withTree $ \tar ->
            case VT.treeNode tar of
              -- In the validation phase, the subnode of the Constraint node might find the parent Constraint node.
              VT.TNAtomCnstr c -> return (VT.mkAtomVTree $ VT.cnsOrigAtom c, False)
              _ -> do
                logDebugStr $
                  printf
                    "deref_getDstVal: vertical reference cycle tail detected: %s == %s."
                    (show dstAddr)
                    (show srcAddr)
                return (VT.setTN t $ VT.TNRefCycle (VT.RefCycleVertMerger (dstAddr, srcAddr)), False)
        | Path.isPrefix canDstAddr canSrcAddr && canSrcAddr /= canDstAddr ->
            return
              ( VT.setTN t $ VT.TNStructuralCycle $ VT.StructuralCycle dstAddr
              , False
              )
        | otherwise -> return (t, True)
    r <-
      if noError
        then copyRefVal trail recurClose val
        else return val
    return . Right $ Just (dstAddr, r)

  -- Try to follow the reference if the target is a reference.
  tryFollow rE dstAddr tar = case ( do
                                      rf <- VT.getMutableFromTree tar >>= VT.getRefFromMutable
                                      newRef <- VT.refFromRefArg (\x -> Path.StringSel <$> VT.getStringFromTree x) (VT.refArg rf)
                                      return (newRef, VT.refOrigAddrs rf)
                                  ) of
    -- follow the reference.
    Just (rf, rfOirgAddrs) -> do
      RM.withAddrAndFocus $ \addr _ ->
        logDebugStr $
          printf
            "deref_getDstVal: addr: %s, dstAddr: %s, follow the new reference: %s"
            (show addr)
            (show dstAddr)
            (show rf)
      getDstVal rf rfOirgAddrs (Set.insert dstAddr trail)
    _ -> return rE

{- | Copy the value of the reference from within the dst environment.

dstAddr and trail are used to decide whether to close the deref'd value.

From the spec:
The value of a reference is a copy of the expression associated with the field that it is bound to, with
any references within that expression bound to the respective copies of the fields they were originally
bound to.
-}
copyRefVal :: (RM.ReduceMonad s r m) => Set.Set Path.TreeAddr -> Bool -> VT.Tree -> m VT.Tree
copyRefVal trail recurClose tar = do
  case VT.treeNode tar of
    VT.TNAtom _ -> return tar
    VT.TNBottom _ -> return tar
    VT.TNAtomCnstr c -> return (VT.mkAtomVTree $ VT.cnsAtom c)
    _ -> do
      dstAddr <- RM.getRMAbsAddr
      -- evaluate the original expression.
      orig <- evalTarExpr
      let visited = Set.insert dstAddr trail
      val <- checkRefDef orig visited

      RM.withAddrAndFocus $ \addr _ ->
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
      maybe (buildASTExpr False tar) return (VT.treeExpr tar)
        >>= evalExprRM

    tc <- RM.getRMCursor
    markOuterIdents raw tc

  checkRefDef orig visited = do
    let shouldClose = any addrHasDef visited
    if shouldClose || recurClose
      then do
        RM.withAddrAndFocus $ \addr _ ->
          logDebugStr $
            printf
              "deref: addr: %s, visitedRefs: %s, has definition or recurClose: %s is set, recursively close the value. %s"
              (show addr)
              (show $ Set.toList visited)
              (show recurClose)
              (show orig)
        tc <- RM.getRMCursor
        markRecurClosed orig tc
      else return orig

{- | Mark all outer references inside a container node with original value address.

The outer references are the nodes inside a container pointing to the ancestors.
-}
markOuterIdents ::
  (Env r m) =>
  -- | The new evaluated value.
  VT.Tree ->
  -- | The current tree cursor.
  TreeCursor VT.Tree ->
  m VT.Tree
markOuterIdents val ptc = do
  let subtAddr = tcTreeAddr ptc
  utc <- TCursorOps.traverseTCSimple VT.subNodes (mark subtAddr) (val <$ ptc)
  logDebugStr $
    printf "markOuterRefs: scope: %s, val: %s, result: %s" (show subtAddr) (show val) (show $ vcFocus utc)
  return $ vcFocus utc
 where
  -- Mark the outer references with the original value address.
  mark :: (Env r m) => Path.TreeAddr -> TreeCursor VT.Tree -> m VT.Tree
  mark subtAddr tc = do
    let focus = vcFocus tc
    rM <- case VT.getMutableFromTree focus of
      Just (VT.Ref rf) -> return $ do
        newRef <- VT.refFromRefArg (\x -> Path.StringSel <$> VT.getStringFromTree x) (VT.refArg rf)
        return (newRef, \as -> VT.setTN focus $ VT.TNMutable . VT.Ref $ rf{VT.refOrigAddrs = Just as})
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
    (Env r m) =>
    -- The sub-tree address. It is the container node address.
    Path.TreeAddr ->
    TreeCursor VT.Tree ->
    Path.Reference ->
    m Bool
  isOuterScope subtAddr tc rf = do
    tarIdentAddrM <- searchIdent rf tc
    isOuter <-
      maybe
        (return False)
        ( \tarIdentAddr -> do
            let tarIdentInVarScope = Path.isPrefix subtAddr tarIdentAddr && tarIdentAddr /= subtAddr
            return $ not tarIdentInVarScope
        )
        tarIdentAddrM
    logDebugStr $
      printf
        "markOuterRefs: ref to mark: %s, cursor_addr: %s, subtAddr: %s, tarIdentAddrM: %s, isOuterScope: %s"
        (show rf)
        (show $ tcTreeAddr tc)
        (show subtAddr)
        (show tarIdentAddrM)
        (show isOuter)
    return isOuter

  -- Search the first identifier of the reference and convert it to absolute tree addr if it exists.
  searchIdent :: (Env r m) => Path.Reference -> TreeCursor VT.Tree -> m (Maybe Path.TreeAddr)
  searchIdent ref tc = do
    let fstSel = fromJust $ Path.headSel ref
    var <- selToVar fstSel
    resM <- searchTCVar var tc
    return $ fst <$> resM

markRecurClosed :: (Env r m) => VT.Tree -> TreeCursor VT.Tree -> m VT.Tree
markRecurClosed val ptc = do
  utc <- TCursorOps.traverseTCSimple VT.subNodes mark (val <$ ptc)
  return $ vcFocus utc
 where
  mark :: (Env r m) => TreeCursor VT.Tree -> m VT.Tree
  mark tc = do
    let focus = vcFocus tc
    return $
      focus
        { VT.treeRecurClosed = True
        , VT.treeNode = case VT.treeNode focus of
            VT.TNStruct struct -> VT.TNStruct $ struct{VT.stcClosed = True}
            _ -> VT.treeNode focus
        }

{- | Convert the first identifier of the reference to absolute tree addr.

It does not follow the reference.
-}
refToPotentialAddr ::
  (RM.ReduceMonad s r m) => Path.Reference -> Maybe (Path.TreeAddr, Path.TreeAddr) -> m (Maybe Path.TreeAddr)
refToPotentialAddr ref origAddrsM = do
  let fstSel = fromJust $ Path.headSel ref
  var <- selToVar fstSel
  let f = searchRMVar var >>= (\x -> return $ fst <$> x)

  -- Search the address of the first identifier, whether from the current env or the original env.
  maybe f (\(origSubTAddr, _) -> inAbsAddrRMMust origSubTAddr f) origAddrsM

-- | Locate the reference and if the reference is found, run the action.
locateRefAndRun ::
  (RM.ReduceMonad s r m) => Path.Reference -> m (Either VT.Tree (Maybe a)) -> m (Either VT.Tree (Maybe a))
locateRefAndRun ref f = do
  origAbsAddr <- RM.getRMAbsAddr
  tarE <- goLAAddrRM ref
  res <- case tarE of
    Left err -> return $ Left err
    Right False -> return $ Right Nothing
    Right True -> f

  ok <- goRMAbsAddr origAbsAddr
  unless ok $ throwErrSt $ printf "failed to go back to the original addr %s" (show origAbsAddr)
  return res

-- | Locate the node in the lowest ancestor tree by given reference path. The path must start with a locatable var.
goLAAddrRM :: (RM.ReduceMonad s r m) => Path.Reference -> m (Either VT.Tree Bool)
goLAAddrRM ref = do
  when (Path.isRefEmpty ref) $ throwErrSt "empty reference"
  let fstSel = fromJust $ Path.headSel ref
  var <- selToVar fstSel
  tc <- RM.getRMCursor
  searchTCVar var tc >>= \case
    Nothing -> return . Left $ VT.mkBottomTree $ printf "identifier %s is not found" (show fstSel)
    Just (varAddr, _) -> do
      ok <- goRMAbsAddr varAddr
      unless ok $ throwErrSt $ printf "failed to go to the var addr %s" (show varAddr)
      -- varTC <- RM.getRMCursor
      -- -- var must be found. Mark the var as referred if it is a let binding.
      -- RM.putRMCursor $ _markTCFocusReferred varTC

      -- The ref is non-empty, so the rest must be a valid addr.
      let rest = fromJust $ Path.tailRef ref
      r <- RM.descendRM (Path.refToAddr rest)
      return $ Right r

searchRMLetBindValue :: (RM.ReduceMonad s r m) => String -> m (Maybe VT.Tree)
searchRMLetBindValue var = do
  m <- searchRMVar var
  case m of
    Just (addr, True) -> do
      r <- inAbsAddrRMMust addr $ do
        varTC <- RM.getRMCursor
        -- var must be found. Mark the var as referred if it is a let binding.
        RM.putRMCursor $ _markTCFocusReferred varTC
        RM.getRMTree
      return $ Just r
    _ -> return Nothing

addrHasDef :: Path.TreeAddr -> Bool
addrHasDef p =
  any
    ( \case
        Path.StructTASeg (Path.StringTASeg s) -> fromMaybe False $ do
          typ <- VT.getFieldType s
          return $ typ == VT.SFTDefinition
        _ -> False
    )
    $ Path.addrToNormOrdList p

-- | Mark the let binding specified by the its name selector as referred if the focus of the cursor is a let binding.
_markTCFocusReferred :: TreeCursor VT.Tree -> TreeCursor VT.Tree
_markTCFocusReferred tc@(ValCursor sub ((seg@(Path.StructTASeg (Path.LetTASeg name)), par) : cs)) =
  maybe
    tc
    ( \struct ->
        let newPar = VT.setTN par (VT.TNStruct $ VT.markLetBindReferred name struct)
         in -- sub is not changed.
            ValCursor sub ((seg, newPar) : cs)
    )
    (VT.getStructFromTree par)
_markTCFocusReferred tc = tc

selToVar :: (Env r m) => Path.Selector -> m String
selToVar (Path.StringSel s) = return s
selToVar _ = throwErrSt "invalid selector"

{- | Search in the tree for the first variable that can match the name.

Return if the variable address and whether it is a let binding.
-}
searchRMVar :: (RM.ReduceMonad s r m) => String -> m (Maybe (Path.TreeAddr, Bool))
searchRMVar name = do
  tc <- RM.getRMCursor
  searchTCVar name tc

{- | Search in the parent scope for the first variable that can match the segment. Also return if the variable is a
 let binding.
-}
searchRMVarInPar :: (RM.ReduceMonad s r m) => String -> m (Maybe (Path.TreeAddr, Bool))
searchRMVarInPar name = do
  ptc <- do
    tc <- RM.getRMCursor
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
searchTCVar :: (Env r m) => String -> TreeCursor VT.Tree -> m (Maybe (Path.TreeAddr, Bool))
searchTCVar name tc = do
  subM <- findSub name $ vcFocus tc
  r <-
    maybe
      (goUp tc)
      ( \(sub, isLB) ->
          let
            -- The var address is the address of the value, with the updated segment paired with the it.
            newTC = mkSubTC (mkSeg isLB) sub tc
           in
            return $ Just (tcTreeAddr newTC, isLB)
      )
      subM

  logDebugStr $ printf "searchTCVar: name: %s, cur_path: %s, result: %s" name (show $ tcTreeAddr tc) (show r)
  -- logDebugStr $ printf "searchTCVar: name: %s, cur_path: %s, tc:\n%s" name (show $ tcTreeAddr tc) (show tc)
  return r
 where
  mkSeg isLB = Path.StructTASeg $ if isLB then Path.LetTASeg name else Path.StringTASeg name

  goUp :: (Env r m) => TreeCursor VT.Tree -> m (Maybe (Path.TreeAddr, Bool))
  goUp (ValCursor _ [(Path.RootTASeg, _)]) = return Nothing -- stop at the root.
  goUp utc = do
    ptc <- maybe (throwErrSt "already on the top") return $ parentTC utc
    searchTCVar name ptc

  -- TODO: findSub for default disjunct
  findSub :: (Env r m) => String -> VT.Tree -> m (Maybe (VT.Tree, Bool))
  findSub var t = case VT.treeNode t of
    VT.TNStruct struct -> do
      let m =
            catMaybes
              [ do
                  sf <- VT.lookupStructField var struct
                  if VT.lbAttrIsVar (VT.ssfAttr sf)
                    then Just (VT.ssfValue sf, False)
                    else Nothing
              , do
                  lb <- VT.lookupStructLet var struct
                  return (VT.lbValue lb, True)
              ]
      case m of
        [] -> return Nothing
        [x] -> return $ Just x
        _ -> return $ Just (VT.mkBottomTree $ printf "multiple fields found for %s" var, False)
    VT.TNMutable (VT.Compreh c) -> return Nothing
    _ -> return Nothing

-- | Go to the absolute addr in the tree.
goRMAbsAddr :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m Bool
goRMAbsAddr dst = do
  when (Path.headSeg dst /= Just Path.RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  RM.propUpRMUntilSeg Path.RootTASeg
  let dstNoRoot = fromJust $ Path.tailTreeAddr dst
  RM.descendRM dstNoRoot

goRMAbsAddrMust :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m ()
goRMAbsAddrMust addr = do
  backOk <- goRMAbsAddr addr
  unless backOk $
    throwErrSt $
      printf "failed to to the addr %s" (show addr)

evalExprRM :: (RM.ReduceMonad s r m) => AST.Expression -> m VT.Tree
evalExprRM e = do
  MutEnv.Functions{MutEnv.fnEvalExpr = evalExpr} <- asks MutEnv.getFuncs
  curSID <- RM.getRMObjID
  (rawT, newOID) <- runStateT (evalExpr e) curSID
  RM.setRMObjID newOID
  return rawT

mustReferableAddr :: (Env r m) => Path.TreeAddr -> m Path.TreeAddr
mustReferableAddr addr = do
  let r = Path.referableAddr addr
  when (isNothing r) $ throwErrSt $ printf "the addr %s is not referable" (show addr)
  return $ fromJust r