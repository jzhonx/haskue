{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Ref (
  notify,
  deref,
  searchTMVarInPar,
)
where

import Class
import Config
import Control.Monad (unless, void, when)
import Control.Monad.Reader (ask)
import Control.Monad.State.Strict (runStateT)
import Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isNothing)
import qualified Data.Set as Set
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
    rawT <- do
      focus <- getTMTree
      e <- buildASTExpr False focus
      Config{cfEvalExpr = evalExpr} <- ask
      curSID <- getTMScopeID
      (rawT, newSID) <- runStateT (evalExpr e) curSID
      setTMScopeID newSID
      return rawT

    -- We should not use root value to notify.
    when (length cs > 1) $ do
      notifiers <- ctxNotifiers <$> getTMContext
      let
        srcRefAddr = getReferableAddr addr
        notifs = fromMaybe [] (Map.lookup srcRefAddr notifiers)
      logDebugStr $ printf "notifyWithTC: srcRefAddr: %s, notifs %s" (show srcRefAddr) (show notifs)
      unless (null notifs) $ do
        notifyWithTree rawT notifs
        -- The current focus notifying its dependents means it is referred.
        markReferred
      inParentTM $ do
        ptc <- getTMCursor
        -- We must check if the parent is reducing. If the parent is reducing, we should not go up and keep
        -- notifying the dependents.
        -- Because once parent is done with reducing, it will notify its dependents.
        inReducing <- parentIsReducing $ tcTreeAddr ptc
        unless inReducing notify
 where
  parentIsReducing parTreeAddr = do
    stack <- ctxReduceStack <$> getTMContext
    return $ length stack > 1 && stack !! 1 == parTreeAddr

  markReferred :: (TreeMonad s m) => m ()
  markReferred = do
    tc <- getTMCursor
    putTMCursor $ markTCFocusReferred tc

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

notifyWithTree :: (TreeMonad s m) => Tree -> [TreeAddr] -> m ()
notifyWithTree rawT notifs = do
  mapM_
    ( \dep ->
        inAbsRemoteTMMaybe dep (populateRef rawT)
          -- Remove the notifier if the receiver is not found. The receiver might be relocated. For example,
          -- the receiver could first be reduced in a unifying function reducing arguments phase with addr a/fa0.
          -- Then the receiver is relocated to a due to unifying fields.
          >>= maybe (delNotifRecvPrefix dep) return
    )
    notifs

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
populateRef :: (TreeMonad s m) => Tree -> m ()
populateRef rawT = withAddrAndFocus $ \addr x ->
  debugSpan (printf "populateRef: addr: %s, focus: %s, new value: %s" (show addr) (show x) (show rawT)) $ do
    case getMutableFromTree x of
      Just (Ref _) -> do
        mustSetMutValTree rawT
        tryReduceRef
        reduceLAMut addr
      _ -> logDebugStr "populateRef: the focus is not a ref mutable"

reduceLAMut :: (TreeMonad s m) => TreeAddr -> m ()
reduceLAMut from = do
  -- Locate the lowest ancestor mutable to trigger the re-evaluation of the ancestor mutable.
  -- Notice the tree focus now changes to the LA mutable.
  locateLAMutable
  addr <- getTMAbsAddr
  withTree $ \t -> case treeNode t of
    TNMutable mut
      | Just _ <- getRefFromMutable mut -> do
          when (from /= addr) $
            throwErrSt $
              printf "the lowest ancestor mutable %s is not the same as the ref addr: %s" (show addr) (show from)
          -- If it is a reference, the re-evaluation can be skipped because
          -- 1. The la mutable is actually itself.
          -- 2. Re-evaluating the reference would get the same value.
          logDebugStr $
            printf
              -- "populateRef: lowest ancestor mutable is a reference, skip re-evaluation. addr: %s, node: %s"
              "populateRef: lowest ancestor mutable is a reference, addr: %s, node: %s, trigger notify"
              (show addr)
              (show t)
          notify
      -- re-evaluate the highest mutable when it is not a reference.
      | otherwise -> do
          logDebugStr $
            printf "populateRef: re-evaluating the lowest ancestor mutable, addr: %s, node: %s" (show addr) (show t)
          Config{cfReduce = reduce} <- ask
          reduce
          notify
    _ -> logDebugStr "populateRef: the lowest ancestor node is not found"

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
        rE <- getDstVal ref (Set.fromList [getReferableAddr addr])
        case rE of
          Left err -> putTMTree err
          Right rM ->
            maybe
              (addNotifier ref)
              ( \(_, tar) -> do
                  logDebugStr $ printf "deref: addr: %s, ref: %s, target is found: %s" (show addr) (show ref) (show tar)
                  putTMTree tar
                  case treeNode tar of
                    TNBottom _ -> return ()
                    TNRefCycle (RefCycleHori (start, _))
                      | start == getReferableAddr addr ->
                          logDebugStr $
                            printf
                              "deref, addr: %s, self-cycle: %s, skipping add notifier"
                              (show addr)
                              (show tar)
                    _ -> addNotifier ref
              )
              rM

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
This must not introduce a cycle.
-}
addNotifier :: (TreeMonad s m) => Path.Reference -> m ()
addNotifier ref = do
  srcTreeAddr <- refToAbsTreeAddr ref
  recvTreeAddr <- getTMAbsAddr
  let
    srcRefTreeAddr = getReferableAddr srcTreeAddr
    recvRefTreeAddr = getReferableAddr recvTreeAddr

  logDebugStr $ printf "addNotifier: (%s -> %s)" (show srcRefTreeAddr) (show recvRefTreeAddr)
  ctx <- getTMContext
  putTMContext $ addCtxNotifier ctx (srcRefTreeAddr, recvRefTreeAddr)

{- | Get the value pointed by the reference.

If the reference addr is self or visited, then return the tuple of the absolute addr of the start of the cycle and
the cycle tail relative addr.
-}
getDstVal ::
  (TreeMonad s m) =>
  Path.Reference ->
  -- | keeps track of the followed referable addresses.
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
      locateRefAndRun ref $ do
        dstAddr <- getTMAbsAddr
        logDebugStr $
          printf "deref_getDstVal ref: %s, ref is found, dstAddr: %s" (show ref) (show dstAddr)
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
            | Set.member (getReferableAddr dstAddr) trail -> do
                logDebugStr $
                  printf
                    "deref_getDstVal: horizontal reference cycle detected: %s, dst: %s, trail: %s"
                    (show ref)
                    (show dstAddr)
                    (show $ Set.toList trail)
                return (mkNewTree $ TNRefCycle (RefCycleHori (dstAddr, srcAddr)), False)
            -- This handles the case when the reference refers to itself that is the ancestor.
            -- For example, { a: a + 1 } or { a: !a }.
            -- The tree representation of the latter is,
            -- { }
            --  | - a
            -- (!)
            --  | - unary_op
            -- ref_a
            -- Notice that for self-cycle, the srcTreeAddr could be /addr/fv, and the dstTreeAddr could be /addr. They are the
            -- same in the getReferableAddr form.
            | canDstAddr == canSrcAddr && getReferableAddr srcAddr /= getReferableAddr dstAddr -> withTree $ \tar ->
                case treeNode tar of
                  -- In the validation phase, the subnode of the Constraint node might find the parent Constraint node.
                  TNConstraint c -> return (mkAtomVTree $ cnsOrigAtom c, False)
                  _ -> do
                    logDebugStr $ printf "deref_getDstVal: vertical reference cycle tail detected: %s == %s." (show dstAddr) (show srcAddr)
                    return (mkNewTree $ TNRefCycle (RefCycleVertMerger (dstAddr, srcAddr)), False)
            | isPrefix canDstAddr canSrcAddr && canSrcAddr /= canDstAddr ->
                return
                  ( mkBottomTree $
                      printf "structural cycle detected. %s is a prefix of %s" (show dstAddr) (show srcAddr)
                  , False
                  )
            | otherwise -> return (t, True)
        if noError
          then do
            r <- copyRefVal dstAddr trail val
            case getMutableFromTree r of
              -- follow the reference.
              Just (Ref rf) -> do
                logDebugStr $
                  printf
                    "deref_getDstVal: addr: %s, follow the new reference: %s"
                    (show dstAddr)
                    (show $ refPath rf)
                getDstVal (refPath rf) (Set.insert (getReferableAddr dstAddr) trail)
              _ -> return . Right $ Just (dstAddr, r)
          else
            return . Right $ Just (dstAddr, val)

{- | Copy the value of the reference.

dstAddr and trail are used to decide whether to close the deref'd value.

From the spec:
The value of a reference is a copy of the expression associated with the field that it is bound to, with
any references within that expression bound to the respective copies of the fields they were originally
bound to.
-}
copyRefVal :: (TreeMonad s m) => TreeAddr -> Set.Set TreeAddr -> Tree -> m Tree
copyRefVal dstAddr trail tar = do
  case treeNode tar of
    -- The atom value is final, so we can just return it.
    TNAtom _ -> return tar
    TNBottom _ -> return tar
    TNConstraint c -> return (mkAtomVTree $ cnsAtom c)
    _ -> do
      -- evaluate the original expression.
      orig <-
        maybe
          (return tar)
          ( \e -> do
              Config{cfEvalExpr = evalExpr} <- ask
              curSID <- getTMScopeID
              (t, newSID) <- runStateT (evalExpr e) curSID
              setTMScopeID newSID
              return t
          )
          (treeOrig tar)
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

rewriteLetNames :: (TreeMonad s m) => TreeCursor Tree -> m (TreeCursor Tree)
rewriteLetNames tc =
  let t = vcFocus tc
   in case treeNode t of
        TNStruct struct -> undefined
        _ -> undefined

{- | Get the reference target absolute addr. The target might not exist at the time, but the addr should be valid as the
first selector is a locatable var.
-}
refToAbsTreeAddr :: (TreeMonad s m) => Path.Reference -> m TreeAddr
refToAbsTreeAddr ref = do
  let fstSel = fromJust $ headSel ref
  resM <- searchTMVar fstSel
  fstSegAbsTreeAddr <-
    maybe
      (throwErrSt $ printf "reference %s is not found" (show fstSel))
      (return . fst)
      resM
  return $
    maybe
      fstSegAbsTreeAddr
      (\rest -> refToAddr rest `appendTreeAddr` fstSegAbsTreeAddr)
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
searchTCVar :: (TreeMonad s m) => Selector -> TreeCursor Tree -> m (Maybe (TreeCursor Tree, Bool))
searchTCVar sel@(StringSel name) tc = do
  -- logDebugStr $ printf "searchTCVar: %s, tc: %s" name (show tc)
  maybe
    (goUp tc)
    (\(field, isLB) -> return $ Just (mkSubTC (mkSeg isLB) field tc, isLB))
    (getStructField name $ vcFocus tc)
 where
  mkSeg isLB = StructTASeg $ if isLB then LetTASeg name else StringTASeg name

  goUp :: (TreeMonad s m) => TreeCursor Tree -> m (Maybe (TreeCursor Tree, Bool))
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
