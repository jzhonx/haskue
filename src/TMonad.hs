{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module TMonad where

import Class
import Control.Monad (unless, when)
import Control.Monad.Except (throwError)
import Control.Monad.State.Strict (MonadState, gets, modify)
import Cursor
import Data.Maybe (fromJust)
import Env
import Error
import GHC.Stack (HasCallStack)
import Path
import Text.Printf (printf)
import Util

type TMonad s m t =
  ( TreeOp t
  , Env m
  , MonadState s m
  , HasCtxVal s t t
  , HasTrace s
  , HasCallStack
  )

getTMAbsPath :: (TMonad s m t) => m Path
getTMAbsPath = gets (cvPath . getCtxVal)

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

-- Propagate the value up until the lowest selector is passed.
propUpTMSel :: (TMonad s m t) => Selector -> m ()
propUpTMSel sel = getTMCursor >>= go >>= putTMCursor
 where
  go :: (Env m, TreeOp t) => TreeCursor t -> m (TreeCursor t)
  go (ValCursor _ []) = throwErrSt "propUpTMSel: already at the top"
  go tc@(ValCursor _ ((s, _) : _)) = do
    if s == sel
      then propValUp tc
      else propValUp tc >>= go

-- Propagate the value up until the lowest selector is matched.
propUpTMUntilSel :: (TMonad s m t) => Selector -> m ()
propUpTMUntilSel sel = getTMCursor >>= propUpTCUntil sel >>= putTMCursor

propUpTM :: (TMonad s m t) => m ()
propUpTM = getTMCursor >>= propValUp >>= putTMCursor

withTree :: (TMonad s m t) => (t -> m a) -> m a
withTree f = getTMTree >>= f

withContext :: (TMonad s m t) => (Context t -> m a) -> m a
withContext f = getTMContext >>= f

withCtxTree :: (TMonad s m t) => (CtxTree t -> m a) -> m a
withCtxTree f = gets getCtxVal >>= f

withDebugInfo :: (TMonad s m t) => (Path -> t -> m a) -> m a
withDebugInfo f = do
  path <- getTMAbsPath
  withTree (f path)

pushTMSub :: (TMonad s m t) => Selector -> t -> m ()
pushTMSub sel tip = do
  t <- getTMTree
  crumbs <- getTMCrumbs
  putTMCrumbs ((sel, t) : crumbs)
  putTMTree tip

inSubTM :: (TMonad s m t) => Selector -> t -> m a -> m a
inSubTM sel t f = do
  pushTMSub sel t
  r <- f
  propUpTMSel sel
  return r

inParentTM :: (TMonad s m t) => m a -> m a
inParentTM f = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwErrSt "already at the top"
    (sel, _) : _ -> do
      propUpTM
      r <- f
      getTMCursor >>= maybe (throwErrSt "failed to go down") putTMCursor . goDownTCSel sel
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

inAbsRemoteTM :: (TMonad s m t, Show t) => Path -> m a -> m a
inAbsRemoteTM p f = do
  inAbsRemoteTMMaybe p f
    >>= maybe (throwErrSt $ printf "path %s does not exist" (show p)) return

{- | Go to the absolute path in the tree and execute the action.
If the path does not exist, return Nothing.
-}
inAbsRemoteTMMaybe :: (TMonad s m t, Show t) => Path -> m a -> m (Maybe a)
inAbsRemoteTMMaybe p f = do
  origAbsPath <- getTMAbsPath

  tarM <- whenM (goTMAbsPath p) f
  backOk <- goTMAbsPath origAbsPath
  unless backOk $
    throwErrSt $
      printf
        "failed to go back to the original path %s, dest: %s"
        (show origAbsPath)
        (show p)
  return tarM
 where
  whenM :: (TMonad s m t) => m Bool -> m a -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then Just <$> g else return Nothing

-- | Go to the absolute path in the tree. The path must exist.
goTMAbsPath :: (TMonad s m t, Show t) => Path -> m Bool
goTMAbsPath dst = do
  when (headSel dst /= Just Path.RootSelector) $
    throwErrSt (printf "the path %s should start with the root selector" (show dst))
  propUpTMUntilSel Path.RootSelector
  -- withDebugInfo $ \_ t -> logDebugStr $ printf "goTMAbsPath: %s, t: %s" (show dst) (show t)
  let dstNoRoot = fromJust $ tailPath dst
  descendTM dstNoRoot

descendTM :: (TMonad s m t) => Path -> m Bool
descendTM dst = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCPath dst tc)

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

inDiscardSubTM :: (TMonad s m t) => Selector -> t -> m a -> m a
inDiscardSubTM sel t f = do
  pushTMSub sel t
  r <- f
  discardTMAndPop
  return r

inTempSubTM :: (TMonad s m t) => t -> m a -> m a
inTempSubTM sub f = do
  pushTMSub TempSelector sub
  r <- f
  propUpTMSel TempSelector
  return r

maybeM :: (Monad m) => m b -> (a -> m b) -> m (Maybe a) -> m b
maybeM b f m = do
  ma <- m
  maybe b f ma

whenJust :: (Monad m) => Maybe a -> (a -> m (Maybe b)) -> m (Maybe b)
whenJust m = whenJustM (return m)

whenJustM :: (Monad m) => m (Maybe a) -> (a -> m (Maybe b)) -> m (Maybe b)
whenJustM m f = do
  ma <- m
  maybe (return Nothing) f ma

treeDepthCheck :: (TMonad s m t) => m ()
treeDepthCheck = do
  crumbs <- getTMCrumbs
  let depth = length crumbs
  when (depth > 1000) $ throwError "tree depth exceeds 1000"
