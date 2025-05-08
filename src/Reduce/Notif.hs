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
import Control.Monad.State.Strict (execStateT, get, gets, modify, put)
import qualified Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.Nodes as Nodes
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import Text.Printf (printf)
import Util (
  HasTrace (..),
  logDebugStr,
 )
import qualified Value.Tree as VT

{- | RefSysy starts notification propagation in the tree.

The propagation is done in a breadth-first manner. It first reduces the current visiting node if needed and then
propagates to the dependents of the visiting node and the dependents of its ancestors.

The propagation starts from the current focus.
-}
notify :: (RM.ReduceTCMonad s r m) => m ()
notify = RM.withAddrAndFocus $ \addr _ -> RM.debugSpanTM "notify" $ do
  origRefSysEnabled <- RM.getRMNotifEnabled
  -- Disable the notification to avoid notifying the same node multiple times.
  RM.setRMNotifEnabled False
  let
    visiting = [addr]
    -- The initial node has already been reduced.
    q = [(addr, False)]

  s <- get
  ns <- execStateT bfsLoopQ (WithBFSState (BFSState visiting q) s)
  put (wbOther ns)
  RM.setRMNotifEnabled origRefSysEnabled

class HasBFSState s where
  getBFSState :: s -> BFSState
  setBFSState :: s -> BFSState -> s

data BFSState = BFSState
  { _bfsVisiting :: [Path.TreeAddr]
  , bfsQueue :: [(Path.TreeAddr, Bool)]
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

bfsLoopQ :: (RM.ReduceTCMonad r s m, HasBFSState s) => m ()
bfsLoopQ = do
  state@(BFSState{bfsQueue = q}) <- gets getBFSState
  RM.debugSpanArgsTM "bfsLoopQ" (printf "q:%s" (show q)) $ do
    case q of
      [] -> return ()
      ((addr, toReduce) : xs) -> do
        -- pop the first element of the queue.
        modify $ \s -> setBFSState s state{bfsQueue = xs}

        origAddr <- RM.getTMAbsAddr
        -- First try to go to the addr.
        found <- RefSys.goRMAbsAddr addr
        if found
          then do
            when toReduce reduceImParMut
            -- Adding new deps should be in the exact environment of the result of the reduceImParMut.
            addDepsUntilRoot
          else
            -- Remove the notification if the receiver is not found. The receiver might be relocated. For
            -- example, the receiver could first be reduced in a unifying function reducing arguments phase with
            -- addr a/fa0. Then the receiver is relocated to "/a" due to unifying fields.
            Mutate.delRefSysRecvPrefix addr

        -- We must go back to the original addr even when the addr is not found, because that would lead to unexpected
        -- address.
        RefSys.goRMAbsAddrMust origAddr
        bfsLoopQ
 where
  -- Add the dependents of the current focus and its ancestors to the visited list and the queue.
  -- Notice that it changes the tree focus. After calling the function, the caller should restore the focus.
  addDepsUntilRoot :: (RM.ReduceTCMonad r s m, HasBFSState s) => m ()
  addDepsUntilRoot = do
    cs <- RM.getTMCrumbs
    -- We should not use root value to notify.
    when (length cs > 1) $ do
      recvs <- do
        notifyG <- Common.ctxNotifGraph <$> RM.getRMContext
        addr <- RM.getTMAbsAddr
        -- We need to use the finalized addr to find the notifiers so that some dependents that reference on the
        -- finalized address can be notified.
        -- For example, { a: r, r: y:{}, p: a.y}. p's a.y references the finalized address while a's value might
        -- always have address of /a/sv/y.
        return $
          fromMaybe
            []
            ( do
                srcFinalizedAddr <- Path.getReferableAddr addr
                Map.lookup srcFinalizedAddr notifyG
            )

      -- Add the receivers to the visited list and the queue.
      modify $ \st ->
        let bfsState = getBFSState st
            newBFSState =
              foldr
                ( \recv s@(BFSState v q) ->
                    if recv `notElem` v
                      then BFSState (recv : v) (q ++ [(recv, True)])
                      else s
                )
                bfsState
                recvs
         in setBFSState st newBFSState

      inReducing <- do
        ptc <- RM.getTMCursor
        -- We must check if the parent is reducing. If the parent is reducing, we should not go up and keep
        -- notifying the dependents.
        -- Because once parent is done with reducing, it will notify its dependents.
        parentIsReducing $ Cursor.tcCanAddr ptc

      unless inReducing $ do
        propFocusUpWithPostHandling
        addDepsUntilRoot

  parentIsReducing parTreeAddr = do
    stack <- Common.ctxReduceStack <$> RM.getRMContext
    return $ length stack > 1 && stack !! 1 == parTreeAddr

propFocusUpWithPostHandling :: (RM.ReduceTCMonad s r m) => m ()
propFocusUpWithPostHandling = do
  subTC <- RM.getTMCursor
  seg <- Cursor.focusTCSeg subTC
  p <- RM.getTMParent
  RM.debugSpanArgsTM "propFocusUpWithPostHandling" (printf "bpar: %s" (show p)) $ do
    RM.propUpTM
    RM.withTree $ \t -> case (seg, VT.getBlockFromTree t) of
      (Path.StructTASeg sseg, Just _) -> do
        tc <- RM.getTMCursor
        (utc, affected) <- Nodes.updateStructTCWithObj sseg tc
        final <-
          if null affected
            then return utc
            else foldM (flip Nodes.reduceStructField) utc affected
        RM.putTMCursor final
      _ -> return ()

drainRefSysQueue :: (RM.ReduceTCMonad s r m) => m ()
drainRefSysQueue = do
  q <- RM.getRMNotifQ
  deps <- Common.ctxNotifGraph <$> RM.getRMContext
  more <- RM.debugSpanArgsTM "drainRefSysQueue" (printf "q: %s, deps: %s" (show q) (show $ Map.toList deps)) $ do
    headM <- RM.popRMNotifQ
    case headM of
      Nothing -> return False
      Just addr -> do
        logDebugStr $ printf "drainRefSysQueue: addr: %s" (show addr)
        maybe
          (logDebugStr $ printf "drainRefSysQueue: addr: %s, not found" (show addr))
          (const $ return ())
          =<< RefSys.inAbsAddrRM addr notify
        return True

  when more drainRefSysQueue

-- | Reduce the immediate parent mutable.
reduceImParMut :: (RM.ReduceTCMonad s r m) => m ()
reduceImParMut = RM.debugSpanTM "reduceImParMut" $ do
  -- Locate immediate parent mutable to trigger the re-evaluation of the parent mutable.
  -- Notice the tree focus now changes to the Im mutable.
  locateImMutable
  addr <- RM.getTMAbsAddr
  RM.debugInstantTM "reduceImParMut" (printf "addr: %s" (show addr))
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNMutable mut
      | Just _ <- VT.getRefFromMutable mut -> do
          logDebugStr $
            printf "reduceImParMut: ImPar is a reference, addr: %s, node: %s" (show addr) (show t)
          reduceFocus
      -- re-evaluate the mutable when it is not a reference.
      | otherwise -> do
          logDebugStr $
            printf "reduceImParMut: re-evaluating the ImPar, addr: %s, node: %s" (show addr) (show t)
          reduceFocus
    _ -> logDebugStr "reduceImParMut: ImPar is not found"

reduceFocus :: (RM.ReduceTCMonad s r m) => m ()
reduceFocus = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  tc <- RM.getTMCursor
  r <- reduce tc
  RM.putTMCursor (r `Cursor.setTCFocus` tc)

-- Locate the immediate parent mutable.
-- TODO: consider the mutable does not have arguments.
locateImMutable :: (RM.ReduceTCMonad s r m) => m ()
locateImMutable = do
  addr <- RM.getTMAbsAddr
  if hasEmptyTreeAddr addr || not (hasMutableArgSeg addr)
    then return ()
    -- If the addr has mutable argument segments, that means we are in a mutable node.
    else RM.propUpTM >> locateImMutable
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