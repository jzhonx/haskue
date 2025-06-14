{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Notif where

import qualified Common
import Control.Monad (foldM, unless, when)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (execStateT, get, gets, modify, put, runStateT)
import qualified Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.Nodes as Nodes
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified TCOps
import Text.Printf (printf)
import Util (
  HasTrace (..),
 )
import qualified Value.Tree as VT

drainRefSysQueue :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m TCOps.TrCur
drainRefSysQueue tc = do
  q <- RM.getRMReadyQ
  graph <- Common.ctxNotifGraph <$> RM.getRMContext
  (res, more) <- RM.debugSpanArgsRM
    "drainRefSysQueue"
    (printf "q: %s, graph: %s" (show q) (show $ Map.toList graph))
    (Just <$> Cursor.tcFocus . fst)
    tc
    $ do
      headM <- RM.popRMReadyQ
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
      propUpTCUntilSeg Path.RootTASeg res

{- | RefSysy starts notification propagation in the tree.

The propagation is done in a breadth-first manner. It first reduces the current visiting node if needed and then
propagates to the dependents of the visiting node and the dependents of its ancestors.

The propagation starts from the current focus.
-}
notify :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m TCOps.TrCur
notify tc = RM.debugSpanRM "notify" (Just <$> Cursor.tcFocus) tc $ do
  origRefSysEnabled <- RM.getRMNotifEnabled
  -- Disable the notification to avoid notifying the same node multiple times.
  RM.setRMNotifEnabled False
  let
    addr = Cursor.tcCanAddr tc
    t = Cursor.tcFocus tc
    visiting = [addr]
    -- The initial node has already been reduced.
    q = [(addr, False, VT.treeVersion t)]

  s <- get
  (r, ns) <- runStateT (bfsLoopQ tc) (WithBFSState (BFSState visiting q) s)
  put (wbOther ns)
  RM.setRMNotifEnabled origRefSysEnabled
  return r

class HasBFSState s where
  getBFSState :: s -> BFSState
  setBFSState :: s -> BFSState -> s

data BFSState = BFSState
  { _bfsVisiting :: [Path.TreeAddr]
  , bfsQueue :: [(Path.TreeAddr, Bool, Int)]
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

instance (Cursor.HasTreeCursor s VT.Tree) => Cursor.HasTreeCursor (WithBFSState s) VT.Tree where
  getTreeCursor s = Cursor.getTreeCursor (wbOther s)
  setTreeCursor s cursor = s{wbOther = Cursor.setTreeCursor (wbOther s) cursor}

instance (Common.HasContext s) => Common.HasContext (WithBFSState s) where
  getContext s = Common.getContext (wbOther s)
  setContext s ctx = s{wbOther = Common.setContext (wbOther s) ctx}
  modifyContext s f = s{wbOther = Common.modifyContext (wbOther s) f}

bfsLoopQ :: (RM.ReduceMonad r s m, HasBFSState s) => TCOps.TrCur -> m TCOps.TrCur
bfsLoopQ tc = do
  state@(BFSState{bfsQueue = q}) <- gets getBFSState
  case q of
    [] -> return tc
    ((addr, toReduce, srcVers) : xs) -> do
      r <- RM.debugSpanArgsRM "bfsLoopQ" (printf "q:%s" (show q)) (Just <$> Cursor.tcFocus) tc $ do
        -- pop the first element of the queue.
        modify $ \s -> setBFSState s state{bfsQueue = xs}

        -- First try to go to the addr.
        dstTCM <- goTCAbsAddr2 addr tc
        maybe
          ( do
              -- Remove the notification if the receiver is not found. The receiver might be relocated. For
              -- example, the receiver could first be reduced in a unifying function reducing arguments phase with
              -- addr a/fa0. Then the receiver is relocated to "/a" due to unifying fields.
              Mutate.delRefSysRecvPrefix addr
              return tc
          )
          ( \dstTC ->
              do
                utc <-
                  if toReduce
                    then do
                      RM.debugInstantRM "bfsLoopQ" (printf "reducing %s" (show $ Cursor.tcFocus dstTC)) dstTC

                      reduceImParMut srcVers dstTC
                    else
                      return dstTC
                -- Adding new deps should be in the exact environment of the result of the reduceImParMut.
                addDepsUntilRoot utc
          )
          dstTCM

      bfsLoopQ r

goTCAbsAddr2 :: (RM.ReduceMonad r s m) => Path.TreeAddr -> TCOps.TrCur -> m (Maybe TCOps.TrCur)
goTCAbsAddr2 dst tc = do
  when (Path.headSeg dst /= Just Path.RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  top <- propUpTCUntilSeg Path.RootTASeg tc
  let dstNoRoot = fromJust $ Path.tailTreeAddr dst
  return $ TCOps.goDownTCAddr dstNoRoot top

-- Propagate the value up until the lowest segment is matched.
propUpTCUntilSeg :: (RM.ReduceMonad r s m) => Path.TASeg -> TCOps.TrCur -> m TCOps.TrCur
propUpTCUntilSeg seg tc = do
  if isMatched tc
    then return tc
    else do
      propUpTC2 tc >>= propUpTCUntilSeg seg
 where
  isMatched :: TCOps.TrCur -> Bool
  isMatched (Cursor.TreeCursor _ []) = False -- propUpTM would panic.
  isMatched (Cursor.TreeCursor _ ((s, _) : _)) = s == seg

propUpTC2 :: (RM.ReduceMonad r s m) => TCOps.TrCur -> m TCOps.TrCur
propUpTC2 tc = do
  let addr = Cursor.tcCanAddr tc
      focus = Cursor.tcFocus tc
  seg <- TCOps.getTCFocusSeg tc

  -- If the focus is a bottom and the address is not an immediate disj, then we should overwrite the parent with the
  -- bottom.
  if Common.isTreeBottom focus && Path.isInDisj addr && not (Path.isSegDisj seg)
    then do
      ptc <- Cursor.parentTCMust tc
      return $ Cursor.setTCFocus focus ptc
    else TCOps.propUpTC tc

-- Add the dependents of the current focus and its ancestors to the visited list and the queue.
-- Notice that it changes the tree focus. After calling the function, the caller should restore the focus.
addDepsUntilRoot :: (RM.ReduceMonad r s m, HasBFSState s) => TCOps.TrCur -> m TCOps.TrCur
addDepsUntilRoot tc = do
  let cs = Cursor.tcCrumbs tc
  -- We should not use root value to notify.
  if length cs <= 1
    then return tc
    else do
      recvs <- do
        notifyG <- Common.ctxNotifGraph <$> RM.getRMContext
        -- We need to use the finalized addr to find the notifiers so that some dependents that reference on the
        -- finalized address can be notified.
        -- For example, { a: r, r: y:{}, p: a.y}. p's a.y references the finalized address while a's value might
        -- always have address of /a/sv/y.
        return $
          fromMaybe
            []
            ( do
                srcFinalizedAddr <- Path.getReferableAddr (Cursor.tcCanAddr tc)
                Map.lookup srcFinalizedAddr notifyG
            )

      let srcVers = VT.treeVersion (Cursor.tcFocus tc)

      -- Add the receivers to the visited list and the queue.
      modify $ \st ->
        let bfsState = getBFSState st
            newBFSState =
              foldr
                ( \recv s@(BFSState v q) ->
                    if recv `notElem` v
                      then BFSState (recv : v) (q ++ [(recv, True, srcVers)])
                      else s
                )
                bfsState
                recvs
         in setBFSState st newBFSState

      -- TODO: remove checking
      inReducing <- do
        -- We must check if the parent is reducing. If the parent is reducing, we should not go up and keep
        -- notifying the dependents.
        -- Because once parent is done with reducing, it will notify its dependents.
        parentIsReducing $ Cursor.tcCanAddr tc
      if not inReducing
        then do
          ptc <- propFocusUpWithPostHandling tc
          addDepsUntilRoot ptc
        else return tc
 where
  parentIsReducing parTreeAddr = do
    stack <- Common.ctxReduceStack <$> RM.getRMContext
    return $ length stack > 1 && stack !! 1 == parTreeAddr

propFocusUpWithPostHandling :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m TCOps.TrCur
propFocusUpWithPostHandling subTC = do
  seg <- Cursor.focusTCSeg subTC
  RM.debugSpanRM "propFocusUpWithPostHandling" (Just <$> Cursor.tcFocus) subTC $ do
    tc <- propUpTC2 subTC
    case (seg, VT.getBlockFromTree (Cursor.tcFocus tc)) of
      (Path.StructTASeg sseg, Just _) -> do
        (utc, affected) <- Nodes.handleStructMutObjChange sseg tc
        if null affected
          then return utc
          else foldM (flip Nodes.reduceStructField) utc affected
      _ -> return tc

-- | Reduce the immediate parent mutable.
reduceImParMut :: (RM.ReduceMonad s r m) => Int -> TCOps.TrCur -> m TCOps.TrCur
reduceImParMut srcVers tc = RM.debugSpanRM "reduceImParMut" (Just <$> Cursor.tcFocus) tc $ do
  let focus = Cursor.tcFocus tc
  (utc, toReduce) <- case VT.treeNode focus of
    VT.TNMutable mut
      | Just ref <- VT.getRefFromMutable mut ->
          if maybe True (< srcVers) (VT.refVers ref)
            then do
              let newRef = ref{VT.refVers = Just srcVers}
              return (TCOps.setTCFocusTN (VT.TNMutable $ VT.Ref newRef) tc, True)
            else do
              RM.debugInstantRM "reduceImParMut" (printf "reduceImParMut: ref %s is already up to date" (show ref)) tc
              return (tc, False)
    _ -> throwErrSt $ printf "ImPar %s is not a ref node" (VT.showTreeSymbol focus)

  if not toReduce
    then return utc
    else do
      -- Locate immediate parent mutable to trigger the re-evaluation of the parent mutable.
      -- Notice the tree focus now changes to the Im mutable.
      mtc <- locateImMutable utc
      MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
      case VT.treeNode (Cursor.tcFocus mtc) of
        VT.TNMutable mut
          | Just _ <- VT.getRefFromMutable mut -> do
              r <- reduce mtc
              return $ Cursor.setTCFocus r mtc
          -- re-evaluate the mutable when it is not a reference.
          | otherwise -> do
              r <- reduce mtc
              return $ Cursor.setTCFocus r mtc
        _ -> return mtc

-- Locate the immediate parent mutable.
-- TODO: consider the mutable does not have arguments.
-- TODO: it can be simpler.
locateImMutable :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m TCOps.TrCur
locateImMutable tc = do
  let addr = Cursor.tcCanAddr tc
  if hasEmptyTreeAddr addr || not (hasMutableArgSeg addr)
    then return tc
    -- If the addr has mutable argument segments, that means we are in a mutable node.
    else propUpTC2 tc >>= locateImMutable
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