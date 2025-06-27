{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Notif where

import qualified Common
import Control.Monad (foldM, when)
import Control.Monad.State.Strict (get, gets, modify, put, runStateT)
import Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Sequence as Seq
import Exception (throwErrSt)
import Path
import Reduce.Mutate (delRefSysRecvPrefix)
import qualified Reduce.Nodes as Nodes
import Reduce.RMonad (
  ReduceMonad,
  debugInstantRM,
  debugSpanArgsRM,
  debugSpanRM,
  getRMContext,
  getRMNotifEnabled,
  getRMReadyQ,
  popRMReadyQ,
  setRMNotifEnabled,
 )
import {-# SOURCE #-} Reduce.Root (reduce)
import Text.Printf (printf)
import Util (
  HasTrace (..),
 )
import Value

drainRefSysQueue :: (ReduceMonad s r m) => TrCur -> m TrCur
drainRefSysQueue tc = do
  q <- getRMReadyQ
  graph <- Common.ctxNotifGraph <$> getRMContext
  (res, more) <- debugSpanArgsRM
    "drainRefSysQueue"
    (printf "q: %s, graph: %s" (show q) (show $ Map.toList graph))
    (Just <$> tcFocus . fst)
    tc
    $ do
      headM <- popRMReadyQ
      case headM of
        Nothing -> return (tc, False)
        Just addr -> do
          dstTCM <- goTCAbsAddr2 addr tc
          r <-
            maybe
              (return tc)
              (\dstTC -> notify dstTC)
              dstTCM
          return (r, True)

  if more
    then drainRefSysQueue res
    else do
      -- go back to the root
      propUpTCUntilSeg RootTASeg res

{- | RefSysy starts notification propagation in the tree.

The propagation is done in a breadth-first manner. It first reduces the current visiting node if needed and then
propagates to the dependents of the visiting node and the dependents of its ancestors.

The propagation starts from the current focus.
-}
notify :: (ReduceMonad s r m) => TrCur -> m TrCur
notify tc = debugSpanRM "notify" (Just <$> tcFocus) tc $ do
  origRefSysEnabled <- getRMNotifEnabled
  -- Disable the notification to avoid notifying the same node multiple times.
  setRMNotifEnabled False
  let
    addr = tcCanAddr tc
    t = tcFocus tc
    visiting = [addr]
    -- The initial node has already been reduced.
    q = Seq.fromList [(addr, False, treeVersion t)]

  s <- get
  (r, ns) <- runStateT (bfsLoopQ tc) (WithBFSState (BFSState visiting q) s)
  put (wbOther ns)
  setRMNotifEnabled origRefSysEnabled
  return r

class HasBFSState s where
  getBFSState :: s -> BFSState
  setBFSState :: s -> BFSState -> s

data BFSState = BFSState
  { _bfsVisiting :: [TreeAddr]
  , bfsQueue :: Seq.Seq (TreeAddr, Bool, Int)
  -- ^ The queue contains pairs of (address of the source, toReduce, version of the source).
  }

data WithBFSState s = WithBFSState
  { wbState :: BFSState
  , wbOther :: s
  }

instance HasBFSState (WithBFSState s) where
  getBFSState = wbState
  setBFSState s bfs = s{wbState = bfs}

instance (HasTrace s) => HasTrace (WithBFSState s) where
  getTrace s = getTrace (wbOther s)
  setTrace s trace = s{wbOther = setTrace (wbOther s) trace}

instance (HasTreeCursor s) => HasTreeCursor (WithBFSState s) where
  getTreeCursor s = getTreeCursor (wbOther s)
  setTreeCursor s cursor = s{wbOther = setTreeCursor (wbOther s) cursor}

instance (Common.HasContext s) => Common.HasContext (WithBFSState s) where
  getContext s = Common.getContext (wbOther s)
  setContext s ctx = s{wbOther = Common.setContext (wbOther s) ctx}
  modifyContext s f = s{wbOther = Common.modifyContext (wbOther s) f}

bfsLoopQ :: (ReduceMonad r s m, HasBFSState s) => TrCur -> m TrCur
bfsLoopQ tc = do
  state@(BFSState{bfsQueue = q}) <- gets getBFSState
  case q of
    Seq.Empty -> return tc
    ((addr, toReduce, srcVers) Seq.:<| xs) -> do
      r <- debugSpanArgsRM "bfsLoopQ" (printf "q:%s" (show q)) (Just <$> tcFocus) tc $ do
        -- pop the first element of the queue.
        modify $ \s -> setBFSState s state{bfsQueue = xs}

        -- First try to go to the addr.
        dstTCM <- goTCAbsAddr2 addr tc
        maybe
          ( do
              -- Remove the notification if the receiver is not found. The receiver might be relocated. For
              -- example, the receiver could first be reduced in a unifying function reducing arguments phase with
              -- addr a/fa0. Then the receiver is relocated to "/a" due to unifying fields.
              delRefSysRecvPrefix addr
              return tc
          )
          ( \dstTC ->
              do
                utc <-
                  if toReduce
                    then reduceImParMut srcVers dstTC
                    else return dstTC
                -- Adding new deps should be in the exact environment of the result of the reduceImParMut.
                loopAddDeps utc
          )
          dstTCM

      bfsLoopQ r

goTCAbsAddr2 :: (ReduceMonad r s m) => TreeAddr -> TrCur -> m (Maybe TrCur)
goTCAbsAddr2 dst tc = do
  when (headSeg dst /= Just RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  top <- propUpTCUntilSeg RootTASeg tc
  let dstNoRoot = fromJust $ tailTreeAddr dst
  return $ goDownTCAddr dstNoRoot top

-- Propagate the value up until the lowest segment is matched.
propUpTCUntilSeg :: (ReduceMonad r s m) => TASeg -> TrCur -> m TrCur
propUpTCUntilSeg seg tc = do
  if isMatched tc
    then return tc
    else do
      propUpTC2 tc >>= propUpTCUntilSeg seg
 where
  isMatched :: TrCur -> Bool
  isMatched (TrCur _ []) = False -- propUpTM would panic.
  isMatched (TrCur _ ((s, _) : _)) = s == seg

propUpTC2 :: (ReduceMonad r s m) => TrCur -> m TrCur
propUpTC2 tc = do
  let addr = tcCanAddr tc
      focus = tcFocus tc
  seg <- getTCFocusSeg tc

  -- If the focus is a bottom and the address is not an immediate disj, then we should overwrite the parent with the
  -- bottom.
  case focus of
    IsBottom _ | isInDisj addr && not (isSegDisj seg) -> do
      ptc <- parentTCMust tc
      return $ setTCFocus focus ptc
    _ -> propUpTC tc

-- Add the dependents of the current focus and its ancestors to the visited list and the queue.
-- Notice that it changes the tree focus. After calling the function, the caller should restore the focus.
loopAddDeps :: (ReduceMonad r s m, HasBFSState s) => TrCur -> m TrCur
loopAddDeps tc = do
  let cs = tcCrumbs tc
  -- We should not use root value to notify.
  if length cs <= 1
    then return tc
    else do
      recvs <- do
        notifyG <- Common.ctxNotifGraph <$> getRMContext
        -- We need to use the finalized addr to find the notifiers so that some dependents that reference on the
        -- finalized address can be notified.
        -- For example, { a: r, r: y:{}, p: a.y}. p's a.y references the finalized address while a's value might
        -- always have address of /a/sv/y.
        return $
          fromMaybe
            []
            ( do
                srcFinalizedAddr <- getReferableAddr (tcCanAddr tc)
                Map.lookup srcFinalizedAddr notifyG
            )

      let srcVers = treeVersion (tcFocus tc)

      -- Add the receivers to the visited list and the queue.
      modify $ \st ->
        let bfsState = getBFSState st
            newBFSState =
              foldr
                ( \recv s@(BFSState v q) ->
                    if recv `notElem` v
                      then BFSState (recv : v) (q Seq.|> (recv, True, srcVers))
                      else s
                )
                bfsState
                recvs
         in setBFSState st newBFSState

      propFocusUpWithPostHandling tc >>= loopAddDeps

propFocusUpWithPostHandling :: (ReduceMonad s r m) => TrCur -> m TrCur
propFocusUpWithPostHandling subTC = do
  seg <- focusTCSeg subTC
  debugSpanRM "propFocusUpWithPostHandling" (Just <$> tcFocus) subTC $ do
    tc <- propUpTC2 subTC
    case (seg, tcFocus tc) of
      (StructTASeg sseg, IsBlock _) -> do
        (utc, affected) <- Nodes.handleStructMutObjChange sseg tc
        if null affected
          then return utc
          else foldM (flip Nodes.reduceStructField) utc affected
      _ -> return tc

-- | Reduce the immediate parent mutable.
reduceImParMut :: (ReduceMonad s r m) => Int -> TrCur -> m TrCur
reduceImParMut srcVers tc = debugSpanRM "reduceImParMut" (Just <$> tcFocus) tc $ do
  let focus = tcFocus tc
  (utc, toReduce) <- case treeNode focus of
    TNMutable mut
      | Just ref <- getRefFromMutable mut ->
          if maybe True (< srcVers) (refVers ref)
            then do
              let newRef = ref{refVers = Just srcVers}
              return (setTCFocusTN (TNMutable $ Ref newRef) tc, True)
            else do
              debugInstantRM "reduceImParMut" (printf "reduceImParMut: ref %s is already up to date" (show ref)) tc
              return (tc, False)
    _ -> throwErrSt $ printf "ImPar %s is not a ref node" (showTreeSymbol focus)

  if not toReduce
    then return utc
    else do
      -- Locate immediate parent mutable to trigger the re-evaluation of the parent mutable.
      -- Notice the tree focus now changes to the Im mutable.
      mtc <- locateImMutable utc
      case treeNode (tcFocus mtc) of
        TNMutable mut
          | Just _ <- getRefFromMutable mut -> do
              r <- reduce mtc
              return $ setTCFocus r mtc
          -- re-evaluate the mutable when it is not a reference.
          | otherwise -> do
              r <- reduce mtc
              return $ setTCFocus r mtc
        _ -> return mtc

-- Locate the immediate parent mutable.
-- TODO: consider the mutable does not have arguments.
-- TODO: it can be simpler.
locateImMutable :: (ReduceMonad s r m) => TrCur -> m TrCur
locateImMutable tc = do
  let addr = tcCanAddr tc
  if hasEmptyTreeAddr addr || not (hasMutableArgSeg addr)
    then return tc
    -- If the addr has mutable argument segments, that means we are in a mutable node.
    else propUpTC2 tc >>= locateImMutable
 where
  hasEmptyTreeAddr (TreeAddr sels) = null sels
  -- Check if the addr has mutable argument segments.
  hasMutableArgSeg (TreeAddr sels) =
    any
      ( \case
          MutArgTASeg _ -> True
          _ -> False
      )
      sels