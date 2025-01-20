{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module TMonad where

import Class
import Control.Monad (when)
import Control.Monad.Except (throwError)
import Control.Monad.State.Strict (MonadState, gets, modify)
import Cursor
import Env
import Error
import GHC.Stack (HasCallStack)
import Path
import Util

type TMonad s m t =
  ( TreeOp t
  , Env m
  , MonadState s m
  , HasCtxVal s t t
  , HasTrace s
  , HasCallStack
  )

getTMAbsAddr :: (TMonad s m t) => m TreeAddr
getTMAbsAddr = gets (cvTreeAddr . getCtxVal)

getTMContext :: (TMonad s m t) => m (Context t)
getTMContext = gets (cvCtx . getCtxVal)

putTMContext :: (TMonad s m t) => Context t -> m ()
putTMContext ctx = modify $ \s ->
  let ct = getCtxVal s
   in setCtxVal s (ct{cvCtx = ctx})

modifyTMContext :: (TMonad s m t) => (Context t -> Context t) -> m ()
modifyTMContext f = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvCtx = f ctx})

getTMCrumbs :: (TMonad s m t) => m [TreeCrumb t]
getTMCrumbs = ctxCrumbs <$> getTMContext

putTMCrumbs :: (TMonad s m t) => [TreeCrumb t] -> m ()
putTMCrumbs crumbs = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvCtx = ctx{ctxCrumbs = crumbs}})

getTMTree :: (TMonad s m t) => m t
getTMTree = gets (cvVal . getCtxVal)

putTMTree :: (TMonad s m t) => t -> m ()
putTMTree t = modify $ \s -> setCtxVal s (t <$ getCtxVal s)

getTMCursor :: (TMonad s m t) => m (TreeCursor t)
getTMCursor = gets (getCVCursor . getCtxVal)

putTMCursor :: (TMonad s m t) => TreeCursor t -> m ()
putTMCursor tc = putTMCrumbs (vcCrumbs tc) >> putTMTree (vcFocus tc)

getTMTASeg :: (TMonad s m t) => m TASeg
getTMTASeg = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwErrSt "no segment"
    (seg, _) : _ -> return seg

-- Propagate the value up until the lowest segment is passed.
propUpTMSeg :: (TMonad s m t) => TASeg -> m ()
propUpTMSeg seg = getTMCursor >>= go >>= putTMCursor
 where
  go :: (Env m, TreeOp t) => TreeCursor t -> m (TreeCursor t)
  go (ValCursor _ []) = throwErrSt "propUpTMSeg: already at the top"
  go tc@(ValCursor _ ((s, _) : _)) = do
    if s == seg
      then propValUp tc
      else propValUp tc >>= go

-- Propagate the value up until the lowest segment is matched.
propUpTMUntilSeg :: (TMonad s m t) => TASeg -> m ()
propUpTMUntilSeg seg = getTMCursor >>= propUpTCUntil seg >>= putTMCursor

propUpTM :: (TMonad s m t) => m ()
propUpTM = getTMCursor >>= propValUp >>= putTMCursor

withTree :: (TMonad s m t) => (t -> m a) -> m a
withTree f = getTMTree >>= f

withContext :: (TMonad s m t) => (Context t -> m a) -> m a
withContext f = getTMContext >>= f

withCtxTree :: (TMonad s m t) => (CtxTree t -> m a) -> m a
withCtxTree f = gets getCtxVal >>= f

withAddrAndFocus :: (TMonad s m t) => (TreeAddr -> t -> m a) -> m a
withAddrAndFocus f = do
  addr <- getTMAbsAddr
  withTree (f addr)

pushTMSub :: (TMonad s m t) => TASeg -> t -> m ()
pushTMSub seg tip = do
  t <- getTMTree
  crumbs <- getTMCrumbs
  putTMCrumbs ((seg, t) : crumbs)
  putTMTree tip

inSubTM :: (TMonad s m t) => TASeg -> t -> m a -> m a
inSubTM seg t f = do
  pushTMSub seg t
  r <- f
  propUpTMSeg seg
  return r

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getTMParent :: (TMonad s m t) => m t
getTMParent = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwErrSt "already at the top"
    (_, t) : _ -> return t

descendTM :: (TMonad s m t) => TreeAddr -> m Bool
descendTM dst = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCAddr dst tc)

descendTMSeg :: (TMonad s m t) => TASeg -> m Bool
descendTMSeg seg = descendTM (TreeAddr [seg])

-- | discard the current focus, pop up and put the new focus.
discardTMAndPut :: (TMonad s m t) => t -> m ()
discardTMAndPut new = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvVal = new, cvCtx = ctx{ctxCrumbs = tail (ctxCrumbs ctx)}})

-- | discard the current focus, pop up and put the original focus in the crumbs back.
discardTMAndPop :: (TMonad s m t) => m ()
discardTMAndPop = do
  ctx <- getTMContext
  let
    crumbs = ctxCrumbs ctx
    t = head crumbs
  putTMContext ctx{ctxCrumbs = tail crumbs}
  putTMTree (snd t)

inDiscardSubTM :: (TMonad s m t) => TASeg -> t -> m a -> m a
inDiscardSubTM seg t f = do
  pushTMSub seg t
  r <- f
  discardTMAndPop
  return r

inTempSubTM :: (TMonad s m t) => t -> m a -> m a
inTempSubTM sub f = do
  pushTMSub TempTASeg sub
  r <- f
  propUpTMSeg TempTASeg
  return r

allocTMScopeID :: (TMonad s m t) => m Int
allocTMScopeID = do
  sid <- getTMScopeID
  let newSID = sid + 1
  setTMScopeID newSID
  return newSID

getTMScopeID :: (TMonad s m t) => m Int
getTMScopeID = ctxScopeID <$> getTMContext

setTMScopeID :: (TMonad s m t) => Int -> m ()
setTMScopeID newID = modifyTMContext (\ctx -> ctx{ctxScopeID = newID})

getTMNotifQ :: (TMonad s m t) => m [TreeAddr]
getTMNotifQ = ctxNotifQueue <$> getTMContext

addToTMNotifQ :: (TMonad s m t) => TreeAddr -> m ()
addToTMNotifQ addr = modifyTMContext (\ctx -> ctx{ctxNotifQueue = addr : ctxNotifQueue ctx})

popTMNotifQ :: (TMonad s m t) => m (Maybe TreeAddr)
popTMNotifQ = do
  ctx <- getTMContext
  case ctxNotifQueue ctx of
    [] -> return Nothing
    _ -> do
      -- TODO: efficiency
      let addr = last (ctxNotifQueue ctx)
      putTMContext ctx{ctxNotifQueue = init (ctxNotifQueue ctx)}
      return (Just addr)

getTMNotifEnabled :: (TMonad s m t) => m Bool
getTMNotifEnabled = ctxNotifEnabled <$> getTMContext

setTMNotifEnabled :: (TMonad s m t) => Bool -> m ()
setTMNotifEnabled b = modifyTMContext (\ctx -> ctx{ctxNotifEnabled = b})

treeDepthCheck :: (TMonad s m t) => m ()
treeDepthCheck = do
  crumbs <- getTMCrumbs
  let depth = length crumbs
  when (depth > 1000) $ throwError "tree depth exceeds 1000"
