{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RMonad where

import Common (Env, TreeOp (isTreeBottom))
import Config (
  Config (Config, cfFunctions, cfSettings),
  Functions (Functions, fnPropUpStructPost),
  Settings (Settings, stMermaid, stShowMutArgs),
 )
import Control.Monad (unless, when)
import Control.Monad.Except (throwError)
import Control.Monad.Reader (MonadReader, ask, asks)
import Control.Monad.State.Strict (MonadState, evalState, gets, modify)
import Cursor (
  Context (
    ctxCrumbs,
    ctxRefSysEnabled,
    ctxRefSysGraph,
    ctxRefSysQueue,
    ctxObjID
  ),
  CtxTree,
  CtxVal (cvCtx, cvVal),
  HasCtxVal (..),
  TreeCrumb,
  TreeCursor,
  ValCursor (ValCursor, vcCrumbs, vcFocus),
  cvTreeAddr,
  focusTCSeg,
  getCVCursor,
  showRefSysiers,
  tcTreeAddr,
 )
import Exception (throwErrSt)
import GHC.Stack (HasCallStack)
import Path (
  TASeg (RootTASeg, StructTASeg, TempTASeg),
  TreeAddr,
  addrToNormOrdList,
 )
import TCursorOps (goDownTCSeg, propUpTC)
import Text.Printf (printf)
import Util (HasTrace, logDebugStr)
import qualified Value.Tree as VT

-- ReduceMonad stores the tree structure in its state.
type ReduceMonad s m =
  ( Env m
  , MonadState s m
  , HasCtxVal s VT.Tree VT.Tree
  , HasTrace s
  , MonadReader (Config VT.Tree) m
  , HasCallStack
  )

-- TreeAddr

getRMAbsAddr :: (ReduceMonad s m) => m TreeAddr
getRMAbsAddr = gets (cvTreeAddr . getCtxVal)

getRMTASeg :: (ReduceMonad s m) => m TASeg
getRMTASeg = do
  crumbs <- getRMCrumbs
  case crumbs of
    [] -> throwErrSt "no segment"
    (seg, _) : _ -> return seg

-- Context

getRMContext :: (ReduceMonad s m) => m (Context VT.Tree)
getRMContext = gets (cvCtx . getCtxVal)

putRMContext :: (ReduceMonad s m) => Context VT.Tree -> m ()
putRMContext ctx = modify $ \s ->
  let ct = getCtxVal s
   in setCtxVal s (ct{cvCtx = ctx})

modifyRMContext :: (ReduceMonad s m) => (Context VT.Tree -> Context VT.Tree) -> m ()
modifyRMContext f = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvCtx = f ctx})

withContext :: (ReduceMonad s m) => (Context VT.Tree -> m a) -> m a
withContext f = getRMContext >>= f

withCtxTree :: (ReduceMonad s m) => (CtxTree VT.Tree -> m a) -> m a
withCtxTree f = gets getCtxVal >>= f

-- Cursor

getRMCursor :: (ReduceMonad s m) => m (TreeCursor VT.Tree)
getRMCursor = gets (getCVCursor . getCtxVal)

putRMCursor :: (ReduceMonad s m) => TreeCursor VT.Tree -> m ()
putRMCursor tc = putRMCrumbs (vcCrumbs tc) >> putRMTree (vcFocus tc)

-- Crumbs

getRMCrumbs :: (ReduceMonad s m) => m [TreeCrumb VT.Tree]
getRMCrumbs = ctxCrumbs <$> getRMContext

putRMCrumbs :: (ReduceMonad s m) => [TreeCrumb VT.Tree] -> m ()
putRMCrumbs crumbs = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvCtx = ctx{ctxCrumbs = crumbs}})

-- VT.Tree

getRMTree :: (ReduceMonad s m) => m VT.Tree
getRMTree = gets (cvVal . getCtxVal)

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getRMParent :: (ReduceMonad s m) => m VT.Tree
getRMParent = do
  crumbs <- getRMCrumbs
  case crumbs of
    [] -> throwErrSt "already at the top"
    (_, t) : _ -> return t

putRMTree :: (ReduceMonad s m) => VT.Tree -> m ()
putRMTree t = modify $ \s -> setCtxVal s (t <$ getCtxVal s)

withTree :: (ReduceMonad s m) => (VT.Tree -> m a) -> m a
withTree f = getRMTree >>= f

withAddrAndFocus :: (ReduceMonad s m) => (TreeAddr -> VT.Tree -> m a) -> m a
withAddrAndFocus f = do
  addr <- getRMAbsAddr
  withTree (f addr)

-- VT.TreeNode

withTN :: (ReduceMonad s m) => (VT.TreeNode VT.Tree -> m a) -> m a
withTN f = withTree (f . VT.treeNode)

modifyRMTN :: (ReduceMonad s m) => VT.TreeNode VT.Tree -> m ()
modifyRMTN tn = do
  t <- getRMTree
  putRMTree $ VT.setTN t tn

modifyRMNodeWithTree :: (ReduceMonad s m) => VT.Tree -> m ()
modifyRMNodeWithTree t = modifyRMTN (VT.treeNode t)

-- ReduceMonad operations

-- PropUp operations

{- | Propagate the value up.

If the segment is a pending
-}
propUpRM :: (ReduceMonad s m) => m ()
propUpRM = do
  tc <- getRMCursor
  seg <- focusTCSeg tc
  focus <- getRMTree
  if isTreeBottom focus && isSegStruct seg
    then do
      _discardRMAndPop
      putRMTree focus
    else do
      propUpTC tc >>= putRMCursor
      withTree $ \t -> case (seg, VT.getStructFromTree t) of
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
propUpRMUntilSeg :: (ReduceMonad s m) => TASeg -> m ()
propUpRMUntilSeg seg = do
  tc <- getRMCursor
  unless (isMatched tc) $ do
    propUpRM
    propUpRMUntilSeg seg
 where
  isMatched :: TreeCursor VT.Tree -> Bool
  isMatched (ValCursor _ []) = False -- propUpRM would panic.
  isMatched (ValCursor _ ((s, _) : _)) = s == seg

-- Move down operations

descendRM :: (ReduceMonad s m) => TreeAddr -> m Bool
descendRM dst = go (addrToNormOrdList dst)
 where
  go :: (ReduceMonad s m) => [TASeg] -> m Bool
  go [] = return True
  go (x : xs) = do
    r <- descendRMSeg x
    if r
      then go xs
      else return False

{- | Descend the tree cursor to the segment.

It closes the sub tree based on the parent tree.
-}
descendRMSeg :: (ReduceMonad s m) => TASeg -> m Bool
descendRMSeg seg = do
  tc <- getRMCursor
  maybe
    (return False)
    (\r -> putRMCursor r >> return True)
    (goDownTCSeg seg tc)

-- Push down operations

-- | Push down the segment with the new value.
_pushRMSub :: (ReduceMonad s m) => TASeg -> VT.Tree -> m ()
_pushRMSub seg sub = do
  (ValCursor p crumbs) <- getRMCursor
  putRMCursor $
    ValCursor
      sub
      ((seg, p) : crumbs)

-- Push and pop operations

inSubRM :: (ReduceMonad s m) => TASeg -> VT.Tree -> m a -> m a
inSubRM seg t f = do
  _pushRMSub seg t
  r <- f
  propUpRM
  return r

inDiscardSubRM :: (ReduceMonad s m) => TASeg -> VT.Tree -> m a -> m a
inDiscardSubRM seg t f = do
  _pushRMSub seg t
  r <- f
  _discardRMAndPop
  return r

-- | discard the current focus, pop up and put the original focus in the crumbs back.
_discardRMAndPop :: (ReduceMonad s m) => m ()
_discardRMAndPop = do
  ctx <- getRMContext
  let
    crumbs = ctxCrumbs ctx
    headC = head crumbs
  putRMContext ctx{ctxCrumbs = tail crumbs}
  putRMTree (snd headC)

inTempSubRM :: (ReduceMonad s m) => VT.Tree -> m a -> m a
inTempSubRM sub f = do
  _pushRMSub TempTASeg sub
  r <- f
  propUpRM
  return r

-- * VT.Mutable Environment

{- | Go to the parent mutable and run the action in an argument environment, then come back to the mutval environment.

The mutable must see changes propagated from the argument environment.
-}
mutValToArgsRM :: (ReduceMonad s m) => Path.TASeg -> VT.Tree -> m a -> m a
mutValToArgsRM subSeg sub f = doInMutRM $ mustMutable $ \_ -> inSubRM subSeg sub f
 where
  -- Run the action in the parent tree. All changes will be propagated to the parent tree and back to the current
  -- tree.
  -- After evaluating the argument environment, the focus of the tree should still be the mutable.
  doInMutRM :: (ReduceMonad s m) => m a -> m a
  doInMutRM action = do
    seg <- getRMTASeg
    propUpRM
    r <- action
    ok <- descendRMSeg seg
    unless ok $ throwErrSt $ printf "failed to go down with seg %s" (show seg)
    return r

-- ObjID

allocRMObjID :: (ReduceMonad s m) => m Int
allocRMObjID = do
  oid <- getRMObjID
  let newOID = oid + 1
  setRMObjID newOID
  return newOID

getRMObjID :: (ReduceMonad s m) => m Int
getRMObjID = ctxObjID <$> getRMContext

setRMObjID :: (ReduceMonad s m) => Int -> m ()
setRMObjID newID = modifyRMContext (\ctx -> ctx{ctxObjID = newID})

getRMRefSysQ :: (ReduceMonad s m) => m [TreeAddr]
getRMRefSysQ = ctxRefSysQueue <$> getRMContext

addToRMRefSysQ :: (ReduceMonad s m) => TreeAddr -> m ()
addToRMRefSysQ addr = modifyRMContext (\ctx -> ctx{ctxRefSysQueue = addr : ctxRefSysQueue ctx})

popRMRefSysQ :: (ReduceMonad s m) => m (Maybe TreeAddr)
popRMRefSysQ = do
  ctx <- getRMContext
  case ctxRefSysQueue ctx of
    [] -> return Nothing
    _ -> do
      -- TODO: efficiency
      let addr = last (ctxRefSysQueue ctx)
      putRMContext ctx{ctxRefSysQueue = init (ctxRefSysQueue ctx)}
      return (Just addr)

getRMRefSysEnabled :: (ReduceMonad s m) => m Bool
getRMRefSysEnabled = ctxRefSysEnabled <$> getRMContext

setRMRefSysEnabled :: (ReduceMonad s m) => Bool -> m ()
setRMRefSysEnabled b = modifyRMContext (\ctx -> ctx{ctxRefSysEnabled = b})

treeDepthCheck :: (ReduceMonad s m) => m ()
treeDepthCheck = do
  crumbs <- getRMCrumbs
  let depth = length crumbs
  when (depth > 1000) $ throwError "tree depth exceeds 1000"

unlessFocusBottom :: (ReduceMonad s m) => a -> m a -> m a
unlessFocusBottom a f = do
  t <- getRMTree
  case VT.treeNode t of
    VT.TNBottom _ -> return a
    _ -> f

mustMutable :: (ReduceMonad s m) => (VT.Mutable VT.Tree -> m a) -> m a
mustMutable f = withTree $ \t -> case VT.treeNode t of
  VT.TNMutable fn -> f fn
  _ -> throwErrSt $ printf "tree focus %s is not a mutator" (show t)

mustStruct :: (ReduceMonad s m) => (VT.Struct VT.Tree -> m a) -> m a
mustStruct f = withTree $ \t -> case VT.treeNode t of
  VT.TNStruct struct -> f struct
  _ -> throwErrSt $ printf "%s is not a struct" (show t)


dumpEntireTree :: (ReduceMonad s m) => String -> m ()
dumpEntireTree msg = do
  withTN $ \case
    VT.TNAtom _ -> return ()
    VT.TNBottom _ -> return ()
    VT.TNTop -> return ()
    _ -> do
      seg <- getRMTASeg
      Config{cfSettings = Settings{stMermaid = mermaid, stShowMutArgs = showMutArgs}} <- ask
      -- Do not dump the entire tree if the segment is TempTASeg.
      when (mermaid && seg /= TempTASeg) $ do
        logDebugStr "--- dump entire tree states: ---"
        notifiers <- ctxRefSysGraph <$> getRMContext
        logDebugStr $ printf "notifiers: %s" (showRefSysiers notifiers)
        tc <- getRMCursor
        rtc <- up Path.RootTASeg tc

        let
          top = vcFocus rtc
          evalTreeAddr = tcTreeAddr tc
          s = evalState (VT.treeToMermaid (VT.TreeRepBuildOption{VT.trboShowMutArgs = showMutArgs}) msg evalTreeAddr top) 0
        logDebugStr $ printf "\n```mermaid\n%s\n```" s

        logDebugStr "--- dump entire tree done ---"
 where
  up :: (Env m) => TASeg -> TreeCursor VT.Tree -> m (TreeCursor VT.Tree)
  up seg tc =
    if isMatched tc
      then return tc
      else do
        ptc <- propUpTC tc
        up seg ptc
   where
    isMatched :: TreeCursor VT.Tree -> Bool
    isMatched (ValCursor _ []) = False -- propUpRM would panic.
    isMatched (ValCursor _ ((s, _) : _)) = s == seg

{- | Traverse all the one-level sub nodes of the tree.

It surfaces the bottom.
-}
traverseSub :: forall s m. (ReduceMonad s m) => m () -> m ()
traverseSub f = withTree $ \t -> mapM_ go (VT.subNodes t)
 where
  go :: (ReduceMonad s m) => (TASeg, VT.Tree) -> m ()
  go (sel, sub) = unlessFocusBottom () $ do
    res <- inSubRM sel sub (f >> getRMTree)
    -- If the sub node is reduced to bottom, then the parent node should be reduced to bottom.
    t <- getRMTree
    case (VT.treeNode t, VT.treeNode res) of
      (VT.TNStruct _, VT.TNBottom _) -> putRMTree res
      _ -> return ()

{- | Traverse the leaves of the tree cursor in the following order
1. Traverse the current node.
2. Traverse the sub-tree with the segment.
-}
traverseRM :: (ReduceMonad s m) => m () -> m ()
traverseRM f = f >> traverseSub (traverseRM f)

logDebugStrRM :: (ReduceMonad s m) => String -> String -> m ()
logDebugStrRM hdr msg = withAddrAndFocus $ \addr _ -> logDebugStr $ printf "%s: addr: %s, %s" hdr (show addr) msg
