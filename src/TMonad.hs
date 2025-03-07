{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TMonad where

import Class
import Config
import Control.Monad (unless, when)
import Control.Monad.Except (throwError)
import Control.Monad.Reader (MonadReader, ask, asks)
import Control.Monad.State.Strict (MonadState, evalState, gets, modify)
import Cursor
import Env
import Exception
import GHC.Stack (HasCallStack)
import Path
import TCursorOps
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

-- TreeAddr

getTMAbsAddr :: (TreeMonad s m) => m TreeAddr
getTMAbsAddr = gets (cvTreeAddr . getCtxVal)

getTMTASeg :: (TreeMonad s m) => m TASeg
getTMTASeg = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwErrSt "no segment"
    (seg, _) : _ -> return seg

-- Context

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

withContext :: (TreeMonad s m) => (Context Tree -> m a) -> m a
withContext f = getTMContext >>= f

withCtxTree :: (TreeMonad s m) => (CtxTree Tree -> m a) -> m a
withCtxTree f = gets getCtxVal >>= f

-- Cursor

getTMCursor :: (TreeMonad s m) => m (TreeCursor Tree)
getTMCursor = gets (getCVCursor . getCtxVal)

putTMCursor :: (TreeMonad s m) => TreeCursor Tree -> m ()
putTMCursor tc = putTMCrumbs (vcCrumbs tc) >> putTMTree (vcFocus tc)

-- Crumbs

getTMCrumbs :: (TreeMonad s m) => m [TreeCrumb Tree]
getTMCrumbs = ctxCrumbs <$> getTMContext

putTMCrumbs :: (TreeMonad s m) => [TreeCrumb Tree] -> m ()
putTMCrumbs crumbs = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvCtx = ctx{ctxCrumbs = crumbs}})

-- Tree

getTMTree :: (TreeMonad s m) => m Tree
getTMTree = gets (cvVal . getCtxVal)

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getTMParent :: (TreeMonad s m) => m Tree
getTMParent = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwErrSt "already at the top"
    (_, t) : _ -> return t

putTMTree :: (TreeMonad s m) => Tree -> m ()
putTMTree t = modify $ \s -> setCtxVal s (t <$ getCtxVal s)

withTree :: (TreeMonad s m) => (Tree -> m a) -> m a
withTree f = getTMTree >>= f

withAddrAndFocus :: (TreeMonad s m) => (TreeAddr -> Tree -> m a) -> m a
withAddrAndFocus f = do
  addr <- getTMAbsAddr
  withTree (f addr)

-- TreeNode

withTN :: (TreeMonad s m) => (TreeNode Tree -> m a) -> m a
withTN f = withTree (f . treeNode)

modifyTMTN :: (TreeMonad s m) => TreeNode Tree -> m ()
modifyTMTN tn = do
  t <- getTMTree
  putTMTree $ setTN t tn

modifyTMNodeWithTree :: (TreeMonad s m) => Tree -> m ()
modifyTMNodeWithTree t = modifyTMTN (treeNode t)

-- TreeMonad operations

-- PropUp operations

{- | Propagate the value up.

If the segment is a pending
-}
propUpTM :: (TreeMonad s m) => m ()
propUpTM = do
  tc <- getTMCursor
  seg <- focusTCSeg tc
  focus <- getTMTree
  if isTreeBottom focus && isSegStruct seg
    then do
      _discardTMAndPop
      putTMTree focus
    else do
      propUpTC tc >>= putTMCursor
      withTree $ \t -> case (seg, getStructFromTree t) of
        (StructTASeg sseg, Just struct) -> do
          Functions{fnPropUpStructPost = propUpStructPost} <- asks cfFunctions
          propUpStructPost (sseg, struct)
        -- invalid combination should have been ruled out by the propUpTC
        _ -> return ()
 where
  isSegStruct :: TASeg -> Bool
  isSegStruct (StructTASeg _) = True
  isSegStruct _ = False

-- Propagate the value up until the lowest segment is matched.
propUpTMUntilSeg :: (TreeMonad s m) => TASeg -> m ()
propUpTMUntilSeg seg = do
  tc <- getTMCursor
  unless (isMatched tc) $ do
    propUpTM
    propUpTMUntilSeg seg
 where
  isMatched :: TreeCursor Tree -> Bool
  isMatched (ValCursor _ []) = False -- propUpTM would panic.
  isMatched (ValCursor _ ((s, _) : _)) = s == seg

-- Move down operations

descendTM :: (TreeMonad s m) => TreeAddr -> m Bool
descendTM dst = go (addrToNormOrdList dst)
 where
  go :: (TreeMonad s m) => [TASeg] -> m Bool
  go [] = return True
  go (x : xs) = do
    r <- descendTMSeg x
    if r
      then go xs
      else return False

{- | Descend the tree cursor to the segment.

It closes the sub tree based on the parent tree.
-}
descendTMSeg :: (TreeMonad s m) => TASeg -> m Bool
descendTMSeg seg = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCSeg seg tc)

-- Push down operations

-- | Push down the segment with the new value.
_pushTMSub :: (TreeMonad s m) => TASeg -> Tree -> m ()
_pushTMSub seg sub = do
  (ValCursor p crumbs) <- getTMCursor
  putTMCursor $
    ValCursor
      sub
      ((seg, p) : crumbs)

-- Push and pop operations

inSubTM :: (TreeMonad s m) => TASeg -> Tree -> m a -> m a
inSubTM seg t f = do
  _pushTMSub seg t
  r <- f
  propUpTM
  return r

inDiscardSubTM :: (TreeMonad s m) => TASeg -> Tree -> m a -> m a
inDiscardSubTM seg t f = do
  _pushTMSub seg t
  r <- f
  _discardTMAndPop
  return r

-- | discard the current focus, pop up and put the original focus in the crumbs back.
_discardTMAndPop :: (TreeMonad s m) => m ()
_discardTMAndPop = do
  ctx <- getTMContext
  let
    crumbs = ctxCrumbs ctx
    headC = head crumbs
  putTMContext ctx{ctxCrumbs = tail crumbs}
  putTMTree (snd headC)

inTempSubTM :: (TreeMonad s m) => Tree -> m a -> m a
inTempSubTM sub f = do
  _pushTMSub TempTASeg sub
  r <- f
  propUpTM
  return r

-- ObjID

allocTMObjID :: (TreeMonad s m) => m Int
allocTMObjID = do
  oid <- getTMObjID
  let newOID = oid + 1
  setTMObjID newOID
  return newOID

getTMObjID :: (TreeMonad s m) => m Int
getTMObjID = ctxObjID <$> getTMContext

setTMObjID :: (TreeMonad s m) => Int -> m ()
setTMObjID newID = modifyTMContext (\ctx -> ctx{ctxObjID = newID})

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
      seg <- getTMTASeg
      Config{cfSettings = Settings{stMermaid = mermaid, stShowMutArgs = showMutArgs}} <- ask
      -- Do not dump the entire tree if the segment is TempTASeg.
      when (mermaid && seg /= TempTASeg) $ do
        logDebugStr "--- dump entire tree states: ---"
        notifiers <- ctxNotifGraph <$> getTMContext
        logDebugStr $ printf "notifiers: %s" (showNotifiers notifiers)
        tc <- getTMCursor
        rtc <- up Path.RootTASeg tc

        let
          top = vcFocus rtc
          evalTreeAddr = tcTreeAddr tc
          s = evalState (treeToMermaid (TreeRepBuildOption{trboShowMutArgs = showMutArgs}) msg evalTreeAddr top) 0
        logDebugStr $ printf "\n```mermaid\n%s\n```" s

        logDebugStr "--- dump entire tree done ---"
 where
  up :: (Env m) => TASeg -> TreeCursor Tree -> m (TreeCursor Tree)
  up seg tc =
    if isMatched tc
      then return tc
      else do
        ptc <- propUpTC tc
        up seg ptc
   where
    isMatched :: TreeCursor Tree -> Bool
    isMatched (ValCursor _ []) = False -- propUpTM would panic.
    isMatched (ValCursor _ ((s, _) : _)) = s == seg

{- | Traverse all the one-level sub nodes of the tree.

It surfaces the bottom.
-}
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

logDebugStrTM :: (TreeMonad s m) => String -> String -> m ()
logDebugStrTM hdr msg = withAddrAndFocus $ \addr _ -> logDebugStr $ printf "%s: addr: %s, %s" hdr (show addr) msg
