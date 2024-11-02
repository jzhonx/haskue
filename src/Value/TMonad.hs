{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Value.TMonad where

import Control.Monad (unless, when)
import Control.Monad.Except (throwError)
import Control.Monad.State.Strict (MonadState, gets, modify)
import Data.Maybe (fromJust)
import Path
import Text.Printf (printf)
import Value.Class
import Value.Cursor
import Value.Env

type CommonEnv m = Env m Config

type EvalEnvState s m c = (CommonEnv m, MonadState s m)

type TMonad s m t =
  ( TreeOp t
  , CommonEnv m
  , MonadState s m
  , HasCtxVal s t t
  )

data Config = Config
  { cfCreateCnstr :: Bool
  , cfMermaid :: Bool
  }

getTMAbsPath :: (TMonad s m t) => m Path
getTMAbsPath = gets (cvPath . getCtxVal)

getTMContext :: (TMonad s m t) => m (Context t)
getTMContext = gets (cvCtx . getCtxVal)

putTMContext :: (TMonad s m t) => Context t -> m ()
putTMContext ctx = modify $ \s ->
  let ct = getCtxVal s
   in setCtxVal s (ct{cvCtx = ctx})

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
  go :: (CommonEnv m, TreeOp t) => TreeCursor t -> m (TreeCursor t)
  go (ValCursor _ []) = throwError "propUpTMSel: already at the top"
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

-- withTN :: (TMonad s m t) => (t -> m a) -> m a
-- withTN f = withTree (f . treeNode)

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

inAbsRemoteTM :: (TMonad s m t) => Path -> m a -> m a
inAbsRemoteTM p f = do
  inAbsRemoteTMMaybe p (Just <$> f) >>= maybe (throwError "inAbsRemoteTM: path does not exist") return

-- | Go to the absolute path in the tree and execute the action. The path must exist.
inAbsRemoteTMMaybe :: (TMonad s m t) => Path -> m (Maybe a) -> m (Maybe a)
inAbsRemoteTMMaybe p f = do
  origAbsPath <- getTMAbsPath

  tarM <- whenM (goTMAbsPath p) f
  backM <- goTMAbsPath origAbsPath
  unless backM $ throwError "inAbsRemoteTMMaybe: failed to go back to the original path"
  return tarM
 where
  whenM :: (TMonad s m t) => m Bool -> m (Maybe a) -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then g else return Nothing

-- | Go to the absolute path in the tree. The path must exist.
goTMAbsPath :: (TMonad s m t) => Path -> m Bool
goTMAbsPath dst = do
  when (headSel dst /= Just Path.RootSelector) $
    throwError (printf "goTMAbsPath: the path %s should start with the root selector" (show dst))
  propUpTMUntilSel Path.RootSelector
  let dstNoRoot = fromJust $ tailPath dst
  descendTM dstNoRoot

-- Locate the node in the lowest ancestor tree by specified path. The path must start with a locatable var.
goLowestAncPathTM :: (TMonad s m t) => Path -> m (Maybe a) -> m (Maybe a)
goLowestAncPathTM dst f = do
  when (isPathEmpty dst) $ throwError "locate: empty path"
  let fstSel = fromJust $ headSel dst
  tc <- getTMCursor
  varTC <-
    maybeM
      (throwError $ printf "reference %s is not found" (show fstSel))
      return
      (searchTCVar fstSel tc)

  -- var must be found.
  putTMCursor varTC
  -- the selectors may not exist. And if the selectors exist, the value may not exist.
  whenJust (tailPath dst) $ \selPath -> do
    r <- descendTM selPath
    if r then f else return Nothing

descendTM :: (TMonad s m t) => Path -> m Bool
descendTM dst = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCPath dst tc)

discardTMAndPut :: (TMonad s m t) => t -> m ()
discardTMAndPut t = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvVal = t, cvCtx = ctx{ctxCrumbs = tail (ctxCrumbs ctx)}})

discardTMAndPop :: (TMonad s m t) => m ()
discardTMAndPop = do
  ctx <- getTMContext
  let
    crumbs = ctxCrumbs ctx
    t = head crumbs
  putTMContext ctx{ctxCrumbs = tail crumbs}
  putTMTree (snd t)

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
