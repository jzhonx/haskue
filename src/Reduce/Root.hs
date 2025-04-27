{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Root where

import Common (
  Context (Context, ctxReduceStack),
  hasCtxNotifSender,
 )
import qualified Common
import Control.Monad (when)
import Control.Monad.Reader (local)
import qualified Cursor
import Data.Maybe (catMaybes, fromJust, isJust, listToMaybe)
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import Reduce.Nodes (close, reduceCnstredVal, reduceDisj, reduceList, reduceStruct)
import qualified Reduce.Notif as Notif
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified Reduce.RegOps as RegOps
import qualified Reduce.UnifyOp as UnifyOp
import qualified TCOps
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

fullReduce :: (RM.ReduceTCMonad s r m) => m ()
fullReduce = RM.debugSpanTM "fullReduce" $ do
  tc <- RM.getTMCursor
  r <- reduce tc
  RM.putTMTree r
  Notif.drainRefSysQueue

-- | Reduce the tree to the lowest form.
reduce :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m VT.Tree
reduce tc = RM.debugSpanRM "reduce" tc $ do
  let addr = Cursor.tcTreeAddr tc
  result <- reduceTCFocus tc

  notifyEnabled <- RM.getRMNotifEnabled
  isSender <- hasCtxNotifSender addr <$> RM.getRMContext
  -- Only notify dependents when we are not in a temporary node.
  let refAddrM = Path.referableAddr addr
  if isSender && Path.isTreeAddrAccessible addr && notifyEnabled && isJust refAddrM
    then do
      let refAddr = fromJust refAddrM
      -- RM.debugInstantTM "enqueue" $ printf "addr: %s, enqueue new reduced Addr: %s" (show addr) (show refAddr)
      RM.addToRMNotifQ refAddr
    else logDebugStr $ printf "reduce, addr: %s, not accessible or not enabled" (show addr)

  return result

withTreeDepthLimit :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m a -> m a
withTreeDepthLimit tc f = do
  let addr = Cursor.tcTreeAddr tc
  RM.treeDepthCheck tc
  push addr
  r <- f
  pop

  return r
 where
  push addr = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}

  pop = RM.modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}

reduceTCFocus :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m VT.Tree
reduceTCFocus tc = withTreeDepthLimit tc $ do
  let orig = Cursor.tcFocus tc

  r <- case VT.treeNode orig of
    VT.TNMutable mut -> do
      r <- case mut of
        VT.Ref ref -> do
          rM <- RefSys.index (VT.refOrigAddrs ref) (VT.refArg ref) tc
          maybe
            (return Nothing)
            ( \r -> do
                -- If the target is cyclic, and it is not used to only reduce mutable, we should return structural
                -- cycle.
                -- This handles two cases:
                -- 1. The ref had not been marked as cyclic. For example, f: {out: null | f}, the inner f.
                -- 2. The ref had been marked as cyclic. For example, reducing f when reducing the y.
                -- { f: {out: null | f },  y: f }
                if VT.treeIsCyclic r
                  then return $ Just $ VT.mkBottomTree "structural cycle"
                  else Just <$> reduceTCFocus (r `Cursor.setTCFocus` tc)
            )
            rM
        VT.RegOp rop -> case VT.ropOpType rop of
          VT.InvalidOpType -> throwErrSt "invalid op type"
          VT.UnaryOpType op -> RegOps.regUnaryOp op tc
          VT.BinOpType op -> do
            lTC <- TCOps.goDownTCSegMust Path.binOpLeftTASeg tc
            rTC <- TCOps.goDownTCSegMust Path.binOpRightTASeg tc
            RegOps.regBin op lTC rTC
          VT.CloseFunc -> close (VT.ropArgs rop) tc
        VT.Compreh compreh -> undefined
        VT.DisjOp disjOp -> do
          rM <- Mutate.mutateDisjOp False disjOp tc
          maybe
            (return Nothing)
            (\r -> Just <$> reduceTCFocus (r `Cursor.setTCFocus` tc))
            rM
        VT.UOp u -> do
          rM <- UnifyOp.unify (VT.ufConjuncts u) tc
          maybe
            (return Nothing)
            (\r -> Just <$> reduceTCFocus (r `Cursor.setTCFocus` tc))
            rM
      setMutRes mut r tc
    VT.TNStruct _ -> reduceStruct tc
    VT.TNList l -> reduceList l tc
    VT.TNDisj d -> reduceDisj d tc
    VT.TNCnstredVal cv -> reduceCnstredVal cv tc
    VT.TNStub -> throwErrSt "stub node should not be reduced"
    _ -> return orig

  -- Overwrite the treenode of the raw with the reduced tree's VT.TreeNode to preserve tree attributes.
  return $ VT.setTN orig (VT.treeNode r)

setMutRes :: (RM.ReduceMonad s r m) => VT.Mutable VT.Tree -> Maybe VT.Tree -> TCOps.TrCur -> m VT.Tree
setMutRes mut rM tc = do
  let
    mutT = Cursor.tcFocus tc
    addr = Cursor.tcTreeAddr tc

  -- If the rM is another mutable tree, we need to check if the mutval exists by trying to get it.
  r <- case listToMaybe (catMaybes [rM >>= VT.getMutableFromTree >>= VT.getMutVal, rM]) of
    Nothing -> do
      -- We still remove receivers in case some refs have been reduced.
      Mutate.delMutValRecvs addr
      return $ updateMutVal Nothing mutT
    Just r
      | isMutableTreeReducible mutT -> do
          -- TODO: change receivers
          return r
      | otherwise -> do
          Mutate.delMutValRecvs addr
          return $ updateMutVal (Just r) mutT
  RM.debugInstantRM "setMutRes" (printf "rM: %s, mut: %s, res: %s" (show rM) (show $ VT.mkMutableTree mut) (show r)) tc
  return r
 where
  updateMutVal m mutT = VT.setTN mutT (VT.TNMutable $ VT.setMutVal m mut)

{- | Check whether the mutator is reducible.

The first argument is a mutable node, and the second argument is the mutval.

If the mutible tree does not have any references, then we can safely replace the mutible with the result.
-}
isMutableTreeReducible :: VT.Tree -> Bool
isMutableTreeReducible mut = not (Common.treeHasRef mut)

{- | Reduce the conjunct for unification.

It only returns Nothing if the ref does not locate the reference.
-}
reduceUnifyConj :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m (Maybe VT.Tree)
reduceUnifyConj tc = RM.debugSpanRM "reduceUnifyConj" tc $ withTreeDepthLimit tc $ do
  let orig = Cursor.tcFocus tc
  case VT.treeNode orig of
    VT.TNMutable mut
      | VT.Ref ref <- mut -> do
          rM <- RefSys.index (VT.refOrigAddrs ref) (VT.refArg ref) tc
          -- If the ref is reduced to another mutable tree, we further reduce it.
          maybe
            (return Nothing)
            (\r -> reduceUnifyConj (r `Cursor.setTCFocus` tc))
            rM
      | VT.DisjOp disjOp <- mut -> Mutate.mutateDisjOp True disjOp tc
    _ -> return $ Just $ Cursor.tcFocus tc