{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TMonad where

import Config
import Control.Monad (when)
import Control.Monad.Except (throwError)
import Control.Monad.Reader (MonadReader, ask)
import Control.Monad.State.Strict (MonadState, evalState, gets, modify)
import Cursor
import Env
import Error
import GHC.Stack (HasCallStack)
import Path
import Text.Printf (printf)
import Util
import Value.Tree

-- TreeMonad stores the tree structure in its state.
type TreeMonad s m =
  ( Env m
  , MonadState s m
  , HasCtxVal s Tree Tree
  , HasTrace s
  , MonadReader (Config Tree) m
  , HasCallStack
  )

getTMAbsAddr :: (TreeMonad s m) => m TreeAddr
getTMAbsAddr = gets (cvTreeAddr . getCtxVal)

getTMContext :: (TreeMonad s m) => m (Context Tree)
getTMContext = gets (cvCtx . getCtxVal)

putTMContext :: (TreeMonad s m) => Context Tree -> m ()
putTMContext ctx = modify $ \s ->
  let ct = getCtxVal s
   in setCtxVal s (ct{cvCtx = ctx})

modifyTMContext :: (TreeMonad s m) => (Context Tree -> Context Tree) -> m ()
modifyTMContext f = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvCtx = f ctx})

getTMCrumbs :: (TreeMonad s m) => m [TreeCrumb Tree]
getTMCrumbs = ctxCrumbs <$> getTMContext

putTMCrumbs :: (TreeMonad s m) => [TreeCrumb Tree] -> m ()
putTMCrumbs crumbs = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvCtx = ctx{ctxCrumbs = crumbs}})

getTMTree :: (TreeMonad s m) => m Tree
getTMTree = gets (cvVal . getCtxVal)

putTMTree :: (TreeMonad s m) => Tree -> m ()
putTMTree t = modify $ \s -> setCtxVal s (t <$ getCtxVal s)

getTMCursor :: (TreeMonad s m) => m (TreeCursor Tree)
getTMCursor = gets (getCVCursor . getCtxVal)

putTMCursor :: (TreeMonad s m) => TreeCursor Tree -> m ()
putTMCursor tc = putTMCrumbs (vcCrumbs tc) >> putTMTree (vcFocus tc)

getTMTASeg :: (TreeMonad s m) => m TASeg
getTMTASeg = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwErrSt "no segment"
    (seg, _) : _ -> return seg

-- Propagate the value up until the lowest segment is passed.
propUpTMSeg :: (TreeMonad s m) => TASeg -> m ()
propUpTMSeg seg = getTMCursor >>= go >>= putTMCursor
 where
  go :: (Env m) => TreeCursor Tree -> m (TreeCursor Tree)
  go (ValCursor _ []) = throwErrSt "propUpTMSeg: already at the top"
  go tc@(ValCursor _ ((s, _) : _)) = do
    if s == seg
      then propValUp tc
      else propValUp tc >>= go

-- Propagate the value up until the lowest segment is matched.
propUpTMUntilSeg :: (TreeMonad s m) => TASeg -> m ()
propUpTMUntilSeg seg = getTMCursor >>= propUpTCUntil seg >>= putTMCursor

propUpTM :: (TreeMonad s m) => m ()
propUpTM = getTMCursor >>= propValUp >>= putTMCursor

withTree :: (TreeMonad s m) => (Tree -> m a) -> m a
withTree f = getTMTree >>= f

withContext :: (TreeMonad s m) => (Context Tree -> m a) -> m a
withContext f = getTMContext >>= f

withCtxTree :: (TreeMonad s m) => (CtxTree Tree -> m a) -> m a
withCtxTree f = gets getCtxVal >>= f

withAddrAndFocus :: (TreeMonad s m) => (TreeAddr -> Tree -> m a) -> m a
withAddrAndFocus f = do
  addr <- getTMAbsAddr
  withTree (f addr)

pushTMSub :: (TreeMonad s m) => TASeg -> Tree -> m ()
pushTMSub seg tip = do
  t <- getTMTree
  crumbs <- getTMCrumbs
  putTMCrumbs ((seg, t) : crumbs)
  putTMTree tip

inSubTM :: (TreeMonad s m) => TASeg -> Tree -> m a -> m a
inSubTM seg t f = do
  pushTMSub seg t
  r <- f
  propUpTMSeg seg
  return r

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getTMParent :: (TreeMonad s m) => m Tree
getTMParent = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwErrSt "already at the top"
    (_, t) : _ -> return t

descendTM :: (TreeMonad s m) => TreeAddr -> m Bool
descendTM dst = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCAddr dst tc)

descendTMSeg :: (TreeMonad s m) => TASeg -> m Bool
descendTMSeg seg = descendTM (TreeAddr [seg])

-- | discard the current focus, pop up and put the new focus.
discardTMAndPut :: (TreeMonad s m) => Tree -> m ()
discardTMAndPut new = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvVal = new, cvCtx = ctx{ctxCrumbs = tail (ctxCrumbs ctx)}})

-- | discard the current focus, pop up and put the original focus in the crumbs back.
discardTMAndPop :: (TreeMonad s m) => m ()
discardTMAndPop = do
  ctx <- getTMContext
  let
    crumbs = ctxCrumbs ctx
    t = head crumbs
  putTMContext ctx{ctxCrumbs = tail crumbs}
  putTMTree (snd t)

inDiscardSubTM :: (TreeMonad s m) => TASeg -> Tree -> m a -> m a
inDiscardSubTM seg t f = do
  pushTMSub seg t
  r <- f
  discardTMAndPop
  return r

inTempSubTM :: (TreeMonad s m) => Tree -> m a -> m a
inTempSubTM sub f = do
  pushTMSub TempTASeg sub
  r <- f
  propUpTMSeg TempTASeg
  return r

allocTMScopeID :: (TreeMonad s m) => m Int
allocTMScopeID = do
  sid <- getTMScopeID
  let newSID = sid + 1
  setTMScopeID newSID
  return newSID

getTMScopeID :: (TreeMonad s m) => m Int
getTMScopeID = ctxScopeID <$> getTMContext

setTMScopeID :: (TreeMonad s m) => Int -> m ()
setTMScopeID newID = modifyTMContext (\ctx -> ctx{ctxScopeID = newID})

getTMNotifQ :: (TreeMonad s m) => m [TreeAddr]
getTMNotifQ = ctxNotifQueue <$> getTMContext

addToTMNotifQ :: (TreeMonad s m) => TreeAddr -> m ()
addToTMNotifQ addr = modifyTMContext (\ctx -> ctx{ctxNotifQueue = addr : ctxNotifQueue ctx})

popTMNotifQ :: (TreeMonad s m) => m (Maybe TreeAddr)
popTMNotifQ = do
  ctx <- getTMContext
  case ctxNotifQueue ctx of
    [] -> return Nothing
    _ -> do
      -- TODO: efficiency
      let addr = last (ctxNotifQueue ctx)
      putTMContext ctx{ctxNotifQueue = init (ctxNotifQueue ctx)}
      return (Just addr)

getTMNotifEnabled :: (TreeMonad s m) => m Bool
getTMNotifEnabled = ctxNotifEnabled <$> getTMContext

setTMNotifEnabled :: (TreeMonad s m) => Bool -> m ()
setTMNotifEnabled b = modifyTMContext (\ctx -> ctx{ctxNotifEnabled = b})

treeDepthCheck :: (TreeMonad s m) => m ()
treeDepthCheck = do
  crumbs <- getTMCrumbs
  let depth = length crumbs
  when (depth > 1000) $ throwError "tree depth exceeds 1000"

withTN :: (TreeMonad s m) => (TreeNode Tree -> m a) -> m a
withTN f = withTree (f . treeNode)

modifyTMTN :: (TreeMonad s m) => TreeNode Tree -> m ()
modifyTMTN tn = do
  t <- getTMTree
  putTMTree $ setTN t tn

unlessFocusBottom :: (TreeMonad s m) => a -> m a -> m a
unlessFocusBottom a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    _ -> f

mustMutable :: (TreeMonad s m) => (Mutable Tree -> m a) -> m a
mustMutable f = withTree $ \t -> case treeNode t of
  TNMutable fn -> f fn
  _ -> throwErrSt $ printf "tree focus %s is not a mutator" (show t)

dumpEntireTree :: (TreeMonad s m) => String -> m ()
dumpEntireTree msg = do
  withTN $ \case
    TNAtom _ -> return ()
    TNBottom _ -> return ()
    TNTop -> return ()
    _ -> do
      Config{cfMermaid = mermaid, cfShowMutArgs = showMutArgs} <- ask
      when mermaid $ do
        logDebugStr "--- dump entire tree states: ---"
        notifiers <- ctxNotifGraph <$> getTMContext
        logDebugStr $ printf "notifiers: %s" (showNotifiers notifiers)
        tc <- getTMCursor
        rtc <- propUpTCUntil Path.RootTASeg tc

        let
          t = vcFocus rtc
          evalTreeAddr = addrFromCrumbs (vcCrumbs tc)
          s = evalState (treeToMermaid (TreeRepBuildOption{trboShowMutArgs = showMutArgs}) msg evalTreeAddr t) 0
        logDebugStr $ printf "\n```mermaid\n%s\n```" s

        logDebugStr "--- dump entire tree done ---"

-- | Traverse all the one-level sub nodes of the tree.
traverseSub :: forall s m. (TreeMonad s m) => m () -> m ()
traverseSub f = withTree $ \t -> mapM_ go (subNodes t)
 where
  go :: (TreeMonad s m) => (TASeg, Tree) -> m ()
  go (sel, sub) = unlessFocusBottom () $ do
    res <- inSubTM sel sub (f >> getTMTree)
    -- If the sub node is reduced to bottom, then the parent node should be reduced to bottom.
    t <- getTMTree
    case (treeNode t, treeNode res) of
      (TNStruct _, TNBottom _) -> putTMTree res
      _ -> return ()

{- | Traverse the leaves of the tree cursor in the following order
1. Traverse the current node.
2. Traverse the sub-tree with the segment.
-}
traverseTM :: (TreeMonad s m) => m () -> m ()
traverseTM f = f >> traverseSub (traverseTM f)
