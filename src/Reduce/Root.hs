{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Root where

import Common (
  Context (Context, ctxReduceStack),
  hasCtxNotifSender,
 )
import Control.Monad (when)
import Data.Maybe (fromJust, isJust)
import Exception (throwErrSt)
import qualified Path
import qualified Reduce.Mutate as Mutate
import Reduce.Nodes (reduceCnstredVal, reduceDisj, reduceStruct)
import qualified Reduce.Notif as Notif
import qualified Reduce.RMonad as RM
import qualified Reduce.UnifyOp as UnifyOp
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

fullReduce :: (RM.ReduceTCMonad s r m) => m ()
fullReduce = RM.debugSpanTM "fullReduce" $ do
  reduce
  Notif.drainRefSysQueue

-- | Reduce the tree to the lowest form.
reduce :: (RM.ReduceTCMonad s r m) => m ()
reduce = RM.withAddrAndFocus $ \addr _ -> RM.debugSpanTM "reduce" $ do
  RM.treeDepthCheck
  push addr

  -- save the original tree before effects are applied to the focus of the tree.
  orig <- RM.getRMTree
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNMutable m -> Mutate.mutate $ case m of
      VT.Ref ref -> Mutate.mutateRef ref
      VT.SFunc fn -> Mutate.mutateFunc fn >> return Nothing
      VT.Compreh compreh -> Mutate.mutateCompreh compreh >> return Nothing
      VT.DisjOp disjOp -> Mutate.mutateDisjOp disjOp >> return Nothing
      VT.UOp u -> RM.mustMutable $ \_ -> RM.withTree $ \mutT -> do
        Mutate._runInMutValEnv $ UnifyOp.unify (VT.ufConjuncts u)
        -- Mutate.assertMVNotFunc
        Mutate._runWithExtMutVal $ \mv -> when (Mutate.isMutableTreeReducible mutT mv) $ Mutate.reduceToMutVal mv
        return Nothing
    VT.TNStruct _ -> reduceStruct
    VT.TNList _ -> RM.traverseSub reduce
    VT.TNDisj d -> reduceDisj d
    VT.TNCnstredVal cv -> reduceCnstredVal cv
    -- VT.TNStructuralCycle _ -> RM.putTMTree $ VT.mkBottomTree "structural cycle"
    VT.TNStub -> throwErrSt "stub node should not be reduced"
    _ -> return ()

  -- Overwrite the treenode of the raw with the reduced tree's VT.TreeNode to preserve tree attributes.
  RM.withTree $ \t -> RM.putTMTree $ VT.setTN orig (VT.treeNode t)

  notifyEnabled <- RM.getRMRefSysEnabled
  isSender <- hasCtxNotifSender addr <$> RM.getRMContext
  -- Only notify dependents when we are not in a temporary node.
  let refAddrM = Path.referableAddr addr
  if isSender && Path.isTreeAddrAccessible addr && notifyEnabled && isJust refAddrM
    then do
      let refAddr = fromJust refAddrM
      RM.debugInstantTM "enqueue" $ printf "addr: %s, enqueue new reduced Addr: %s" (show addr) (show refAddr)
      RM.addToRMRefSysQ refAddr
    else logDebugStr $ printf "reduce, addr: %s, not accessible or not enabled" (show addr)

  pop
 where
  push addr = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}

  pop = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}
