{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Root where

import Cursor (
  Context (Context, ctxReduceStack),
  hasCtxNotifSender,
 )
import Data.Maybe (fromJust, isJust)
import Exception (throwErrSt)
import qualified Path
import qualified Reduce.Mutate as Mutate
import Reduce.Nodes (reduceCnstredVal, reduceDisj, reduceStruct)
import qualified Reduce.Notif as Notif
import qualified Reduce.RMonad as RM
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

fullReduce :: (RM.ReduceMonad s r m) => m ()
fullReduce = RM.debugSpanRM "fullReduce" $ do
  reduce
  Notif.drainRefSysQueue

-- | Reduce the tree to the lowest form.
reduce :: (RM.ReduceMonad s r m) => m ()
reduce = RM.withAddrAndFocus $ \addr _ -> RM.debugSpanRM "reduce" $ do
  RM.treeDepthCheck
  push addr

  -- save the original tree before effects are applied to the focus of the tree.
  orig <- RM.getRMTree
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNMutable _ -> Mutate.mutate
    VT.TNStruct _ -> reduceStruct
    VT.TNList _ -> RM.traverseSub reduce
    VT.TNDisj d -> reduceDisj d
    VT.TNCnstredVal cv -> reduceCnstredVal cv
    -- VT.TNStructuralCycle _ -> RM.putRMTree $ VT.mkBottomTree "structural cycle"
    VT.TNStub -> throwErrSt "stub node should not be reduced"
    _ -> return ()

  -- Overwrite the treenode of the raw with the reduced tree's VT.TreeNode to preserve tree attributes.
  RM.withTree $ \t -> RM.putRMTree $ VT.setTN orig (VT.treeNode t)

  notifyEnabled <- RM.getRMRefSysEnabled
  isSender <- hasCtxNotifSender addr <$> RM.getRMContext
  -- Only notify dependents when we are not in a temporary node.
  let refAddrM = Path.referableAddr addr
  if isSender && Path.isTreeAddrAccessible addr && notifyEnabled && isJust refAddrM
    then do
      let refAddr = fromJust refAddrM
      RM.debugInstantRM "enqueue" $ printf "addr: %s, enqueue new reduced Addr: %s" (show addr) (show refAddr)
      RM.addToRMRefSysQ refAddr
    else logDebugStr $ printf "reduce, addr: %s, not accessible or not enabled" (show addr)

  pop
 where
  push addr = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}

  pop = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}
