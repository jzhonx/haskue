{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Notif where

import Common (ctxReduceStack, ctxRefSysGraph)
import Control.Monad (unless, when)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (StateT, evalStateT, get, modify, put)
import Control.Monad.Trans (lift)
import qualified Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import Text.Printf (printf)
import Util (
  getTraceID,
  logDebugStr,
 )
import qualified Value.Tree as VT

{- | RefSysy starts notification propagation in the tree.

The propagation is done in a breadth-first manner. It first reduces the current visiting node if needed and then
propagates to the dependents of the visiting node and the dependents of its ancestors.

The propagation starts from the current focus.
-}
notify :: (RM.ReduceMonad s r m) => m ()
notify = RM.withAddrAndFocus $ \addr _ -> RM.debugSpanRM "notify" $ do
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
      found <- lift $ RefSys.goRMAbsAddr addr
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
      lift $ RefSys.goRMAbsAddrMust origAddr
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
        parentIsReducing $ Cursor.tcTreeAddr ptc

      unless inReducing $ do
        lift RM.propUpRM
        addDepsUntilRoot

  parentIsReducing parTreeAddr = do
    stack <- ctxReduceStack <$> RM.getRMContext
    return $ length stack > 1 && stack !! 1 == parTreeAddr

drainRefSysQueue :: (RM.ReduceMonad s r m) => m ()
drainRefSysQueue = do
  q <- RM.getRMRefSysQ
  more <- RM.debugSpanArgsRM "drainRefSysQueue" (printf "q: %s" (show q)) $ do
    headM <- RM.popRMRefSysQ
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