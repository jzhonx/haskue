{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RMonad where

import qualified AST
import qualified Common
import Control.Monad (unless, when)
import Control.Monad.Except (throwError)
import Control.Monad.Reader (MonadReader, asks)
import Control.Monad.State.Strict (evalState, gets, modify, runStateT)
import qualified Cursor
import Exception (throwErrSt)
import GHC.Stack (HasCallStack)
import qualified MutEnv
import Path (
  TASeg (RootTASeg, StructTASeg, TempTASeg),
  TreeAddr,
  addrToNormOrdList,
 )
import qualified TCursorOps
import Text.Printf (printf)
import Util (HasTrace (..), Trace, debugInstant, debugSpan, logDebugStr)
import qualified Value.Tree as VT

-- ReduceMonad stores the tree structure in its state.
type ReduceMonad s r m =
  ( Common.Env r s m
  , Cursor.HasTreeCursor s VT.Tree
  , Common.HasContext s
  , MonadReader r m
  , HasCallStack
  , Common.HasConfig r
  , MutEnv.HasFuncs r VT.Tree
  , Common.IDStore s
  )

data RTCState = RTCstate
  { rtsTC :: Cursor.TreeCursor VT.Tree
  , rtsCtx :: Common.Context
  }

instance Cursor.HasTreeCursor RTCState VT.Tree where
  getTreeCursor = rtsTC
  setTreeCursor s tc = s{rtsTC = tc}

instance Common.HasContext RTCState where
  getContext = rtsCtx
  setContext s ctx = s{rtsCtx = ctx}
  modifyContext s f = s{rtsCtx = f (rtsCtx s)}

instance HasTrace RTCState where
  getTrace = Common.ctxTrace . rtsCtx
  setTrace s trace = s{rtsCtx = setTrace (rtsCtx s) trace}

instance Common.IDStore RTCState where
  getID = Common.getID . rtsCtx
  setID s newID = s{rtsCtx = Common.setID (rtsCtx s) newID}

mkRTState :: Cursor.TreeCursor VT.Tree -> Int -> Trace -> RTCState
mkRTState tc oid trace =
  RTCstate
    { rtsTC = tc
    , rtsCtx =
        Common.emptyContext
          { Common.ctxObjID = oid
          , Common.ctxTrace = trace
          }
    }

-- instance HasContext Context where
--   getContext = id
--   setContext _ newCtx = newCtx
--   modifyContext ctx f = (f ctx)

-- Context

getRMContext :: (ReduceMonad s r m) => m Common.Context
getRMContext = gets Common.getContext

putRMContext :: (ReduceMonad s r m) => Common.Context -> m ()
putRMContext ctx = modify $ \s -> Common.setContext s ctx

modifyRMContext :: (ReduceMonad s r m) => (Common.Context -> Common.Context) -> m ()
modifyRMContext f = do
  ctx <- getRMContext
  putRMContext (f ctx)

-- withContext :: (ReduceMonad s r m) => (Context VT.Tree -> m a) -> m a
-- withContext f = getRMContext >>= f

-- withCtxTree :: (ReduceMonad s r m) => (Cursor.CtxTree VT.Tree -> m a) -> m a
-- withCtxTree f = gets Cursor.getCtxVal >>= f

-- TreeAddr

getRMAbsAddr :: (ReduceMonad s r m) => m TreeAddr
getRMAbsAddr = Cursor.tcTreeAddr <$> getRMCursor

getRMTASeg :: (ReduceMonad s r m) => m TASeg
getRMTASeg = do
  tc <- getRMCursor
  TCursorOps.getTCFocusSeg tc

-- Cursor

getRMCursor :: (ReduceMonad s r m) => m (Cursor.TreeCursor VT.Tree)
getRMCursor = gets Cursor.getTreeCursor

putRMCursor :: (ReduceMonad s r m) => Cursor.TreeCursor VT.Tree -> m ()
putRMCursor tc = modify $ \s -> Cursor.setTreeCursor s tc

-- Crumbs

getRMCrumbs :: (ReduceMonad s r m) => m [Cursor.TreeCrumb VT.Tree]
getRMCrumbs = Cursor.tcCrumbs <$> getRMCursor

-- putRMCrumbs :: (ReduceMonad s r m) => [Cursor.TreeCrumb VT.Tree] -> m ()
-- putRMCrumbs crumbs = modify $ \s -> set

-- VT.Tree

getRMTree :: (ReduceMonad s r m) => m VT.Tree
getRMTree = Cursor.tcFocus <$> getRMCursor

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getRMParent :: (ReduceMonad s r m) => m VT.Tree
getRMParent = do
  crumbs <- getRMCrumbs
  case crumbs of
    [] -> throwErrSt "already at the top"
    (_, t) : _ -> return t

putRMTree :: (ReduceMonad s r m) => VT.Tree -> m ()
putRMTree t = do
  tc <- getRMCursor
  putRMCursor (t `Cursor.setTCFocus` tc)

withTree :: (ReduceMonad s r m) => (VT.Tree -> m a) -> m a
withTree f = getRMTree >>= f

withAddrAndFocus :: (ReduceMonad s r m) => (TreeAddr -> VT.Tree -> m a) -> m a
withAddrAndFocus f = do
  addr <- getRMAbsAddr
  withTree (f addr)

-- VT.TreeNode

withTN :: (ReduceMonad s r m) => (VT.TreeNode VT.Tree -> m a) -> m a
withTN f = withTree (f . VT.treeNode)

modifyRMTN :: (ReduceMonad s r m) => VT.TreeNode VT.Tree -> m ()
modifyRMTN tn = do
  t <- getRMTree
  putRMTree $ VT.setTN t tn

modifyRMNodeWithTree :: (ReduceMonad s r m) => VT.Tree -> m ()
modifyRMNodeWithTree t = modifyRMTN (VT.treeNode t)

-- ReduceMonad operations

-- PropUp operations

{- | Propagate the value up.

It surfaces the bottom if the focus is a bottom and the parent is a struct.
-}
propUpRM :: (ReduceMonad s r m) => m ()
propUpRM = do
  tc <- getRMCursor
  seg <- Cursor.focusTCSeg tc
  focus <- getRMTree
  p <- getRMParent
  debugSpanArgsRM "propUpRM" (printf "bpar: %s" (show p)) $
    -- If the focus is a bottom and the parent is a struct, overwrite the parent with the bottom.
    if Common.isTreeBottom focus && isSegStruct seg
      then do
        _discardRMAndPop
        putRMTree focus
      else do
        TCursorOps.propUpTC tc >>= putRMCursor

        withTree $ \t -> case (seg, VT.getStructFromTree t) of
          (StructTASeg sseg, Just struct) -> do
            MutEnv.Functions{MutEnv.fnPropUpStructPost = propUpStructPost} <- asks MutEnv.getFuncs
            propUpStructPost (sseg, struct)
          -- invalid combination should have been ruled out by the propUpTC
          _ -> return ()
 where
  isSegStruct :: TASeg -> Bool
  isSegStruct (StructTASeg _) = True
  isSegStruct _ = False

-- Propagate the value up until the lowest segment is matched.
propUpRMUntilSeg :: (ReduceMonad s r m) => TASeg -> m ()
propUpRMUntilSeg seg = do
  tc <- getRMCursor
  unless (isMatched tc) $ do
    propUpRM
    propUpRMUntilSeg seg
 where
  isMatched :: Cursor.TreeCursor VT.Tree -> Bool
  isMatched (Cursor.TreeCursor _ []) = False -- propUpRM would panic.
  isMatched (Cursor.TreeCursor _ ((s, _) : _)) = s == seg

-- Move down operations

descendRM :: (ReduceMonad s r m) => TreeAddr -> m Bool
descendRM dst = go (addrToNormOrdList dst)
 where
  go :: (ReduceMonad s r m) => [TASeg] -> m Bool
  go [] = return True
  go (x : xs) = do
    r <- descendRMSeg x
    if r
      then go xs
      else return False

{- | Descend the tree cursor to the segment.

It closes the sub tree based on the parent tree.
-}
descendRMSeg :: (ReduceMonad s r m) => TASeg -> m Bool
descendRMSeg seg = do
  tc <- getRMCursor
  maybe
    (return False)
    (\r -> putRMCursor r >> return True)
    (TCursorOps.goDownTCSeg seg tc)

-- Push down operations

-- | Push down the segment with the new value.
_pushRMSub :: (ReduceMonad s r m) => TASeg -> VT.Tree -> m ()
_pushRMSub seg sub = do
  (Cursor.TreeCursor p crumbs) <- getRMCursor
  putRMCursor $
    Cursor.TreeCursor
      sub
      ((seg, p) : crumbs)

-- Push and pop operations

inSubRM :: (ReduceMonad s r m) => TASeg -> VT.Tree -> m a -> m a
inSubRM seg t f = do
  _pushRMSub seg t
  r <- f
  propUpRM
  return r

inDiscardSubRM :: (ReduceMonad s r m) => TASeg -> VT.Tree -> m a -> m a
inDiscardSubRM seg t f = do
  _pushRMSub seg t
  r <- f
  _discardRMAndPop
  return r

-- | discard the current focus, pop up and put the original focus in the crumbs back.
_discardRMAndPop :: (ReduceMonad s r m) => m ()
_discardRMAndPop = do
  tc <- getRMCursor
  let
    crumbs = Cursor.tcCrumbs tc
    headC = head crumbs
  putRMCursor (Cursor.TreeCursor (snd headC) (tail crumbs))

-- putRMContext ctx{Cursor.ctxCrumbs = tail crumbs}
-- putRMTree (snd headC)

inTempSubRM :: (ReduceMonad s r m) => VT.Tree -> m a -> m a
inTempSubRM sub f = do
  _pushRMSub TempTASeg sub
  r <- f
  propUpRM
  return r

-- ObjID

allocRMObjID :: (ReduceMonad s r m) => m Int
allocRMObjID = do
  oid <- getRMObjID
  let newOID = oid + 1
  setRMObjID newOID
  return newOID

getRMObjID :: (ReduceMonad s r m) => m Int
getRMObjID = Common.getID <$> getRMContext

setRMObjID :: (ReduceMonad s r m) => Int -> m ()
setRMObjID newID = modifyRMContext (\ctx -> Common.setID ctx newID)

-- Trace

getRMTrace :: (ReduceMonad s r m) => m Trace
getRMTrace = getTrace <$> getRMContext

setRMTrace :: (ReduceMonad s r m) => Trace -> m ()
setRMTrace trace = modifyRMContext (\ctx -> setTrace ctx trace)

-- RefSys

getRMRefSysQ :: (ReduceMonad s r m) => m [TreeAddr]
getRMRefSysQ = Common.ctxRefSysQueue <$> getRMContext

addToRMRefSysQ :: (ReduceMonad s r m) => TreeAddr -> m ()
addToRMRefSysQ addr = modifyRMContext (\ctx -> ctx{Common.ctxRefSysQueue = addr : Common.ctxRefSysQueue ctx})

popRMRefSysQ :: (ReduceMonad s r m) => m (Maybe TreeAddr)
popRMRefSysQ = do
  ctx <- getRMContext
  case Common.ctxRefSysQueue ctx of
    [] -> return Nothing
    _ -> do
      -- TODO: efficiency
      let addr = last (Common.ctxRefSysQueue ctx)
      putRMContext ctx{Common.ctxRefSysQueue = init (Common.ctxRefSysQueue ctx)}
      return (Just addr)

getRMRefSysEnabled :: (ReduceMonad s r m) => m Bool
getRMRefSysEnabled = Common.ctxRefSysEnabled <$> getRMContext

setRMRefSysEnabled :: (ReduceMonad s r m) => Bool -> m ()
setRMRefSysEnabled b = modifyRMContext (\ctx -> ctx{Common.ctxRefSysEnabled = b})

treeDepthCheck :: (ReduceMonad s r m) => m ()
treeDepthCheck = do
  crumbs <- getRMCrumbs
  let depth = length crumbs
  Common.Config
    { Common.cfSettings = Common.Settings{Common.stMaxTreeDepth = maxDepth}
    } <-
    asks Common.getConfig
  let maxDepthVal = if maxDepth <= 0 then 1000 else maxDepth
  when (depth > maxDepthVal) $ throwError $ printf "tree depth exceeds max depth (%d)" maxDepthVal

unlessFocusBottom :: (ReduceMonad s r m) => a -> m a -> m a
unlessFocusBottom a f = do
  t <- getRMTree
  case VT.treeNode t of
    VT.TNBottom _ -> return a
    _ -> f

mustMutable :: (ReduceMonad s r m) => (VT.Mutable VT.Tree -> m a) -> m a
mustMutable f = withTree $ \t -> case VT.treeNode t of
  VT.TNMutable fn -> f fn
  _ -> throwErrSt $ printf "tree focus %s is not a mutator" (show t)

mustStruct :: (ReduceMonad s r m) => (VT.Struct VT.Tree -> m a) -> m a
mustStruct f = withTree $ \t -> case VT.treeNode t of
  VT.TNStruct struct -> f struct
  _ -> throwErrSt $ printf "%s is not a struct" (show t)

-- dumpEntireTree :: (ReduceMonad s r m) => String -> m ()
-- dumpEntireTree msg = do
--   withTN $ \case
--     VT.TNAtom _ -> return ()
--     VT.TNBottom _ -> return ()
--     VT.TNTop -> return ()
--     _ -> do
--       seg <- getRMTASeg
--       Common.Config
--         { Common.cfSettings =
--           Common.Settings
--             { Common.stMermaid = mermaid
--             , Common.stShowMutArgs = showMutArgs
--             }
--         } <-
--         asks Common.getConfig
--       -- Do not dump the entire tree if the segment is TempTASeg.
--       when (mermaid && seg /= TempTASeg) $ do
--         logDebugStr "--- dump entire tree states: ---"
--         notifiers <- ctxRefSysGraph <$> getRMContext
--         logDebugStr $ printf "notifiers: %s" (Cursor.showRefSysiers notifiers)
--         tc <- getRMCursor
--         rtc <- up Path.RootTASeg tc

--         let
--           top = Cursor.tcFocus rtc
--           evalTreeAddr = Cursor.tcTreeAddr tc
--           s = evalState (VT.treeToMermaid (VT.TreeRepBuildOption{VT.trboShowMutArgs = showMutArgs}) msg evalTreeAddr top) 0
--         logDebugStr $ printf "\n```mermaid\n%s\n```" s

--         logDebugStr "--- dump entire tree done ---"
--  where
--   up :: (Common.Env r s m) => TASeg -> Cursor.TreeCursor VT.Tree -> m (Cursor.TreeCursor VT.Tree)
--   up seg tc =
--     if isMatched tc
--       then return tc
--       else do
--         ptc <- TCursorOps.propUpTC tc
--         up seg ptc
--    where
--     isMatched :: Cursor.TreeCursor VT.Tree -> Bool
--     isMatched (Cursor.TreeCursor _ []) = False -- propUpRM would panic.
--     isMatched (Cursor.TreeCursor _ ((s, _) : _)) = s == seg

{- | Traverse all the one-level sub nodes of the tree.

It surfaces the bottom.
-}
traverseSub :: forall s r m. (ReduceMonad s r m) => m () -> m ()
traverseSub f = withTree $ \t -> mapM_ go (VT.subNodes t)
 where
  go :: (ReduceMonad s r m) => (TASeg, VT.Tree) -> m ()
  go (sel, sub) = unlessFocusBottom () $ do
    res <- inSubRM sel sub (f >> getRMTree)
    -- If the sub node is reduced to bottom, then the parent struct node should be reduced to bottom.
    t <- getRMTree
    case (VT.treeNode t, VT.treeNode res) of
      (VT.TNStruct _, VT.TNBottom _) -> putRMTree res
      _ -> return ()

{- | Traverse the leaves of the tree cursor in the following order
1. Traverse the current node.
2. Traverse the sub-tree with the segment.
-}
traverseRM :: (ReduceMonad s r m) => m () -> m ()
traverseRM f = f >> traverseSub (traverseRM f)

evalExprRM :: (ReduceMonad s r m) => AST.Expression -> m VT.Tree
evalExprRM e = do
  MutEnv.Functions{MutEnv.fnEvalExpr = evalExpr} <- asks MutEnv.getFuncs
  curSID <- getRMObjID
  trace <- getRMTrace
  (rawT, newEEState) <- runStateT (evalExpr e) (Common.EEState curSID trace)
  setRMObjID (Common.eesObjID newEEState)
  setRMTrace (Common.eesTrace newEEState)
  return rawT

logDebugStrRM :: (ReduceMonad s r m) => String -> String -> m ()
logDebugStrRM hdr msg = withAddrAndFocus $ \addr _ -> logDebugStr $ printf "%s: addr: %s, %s" hdr (show addr) msg

data ShowTree = ShowFullTree VT.Tree | ShowTree VT.Tree

instance Show ShowTree where
  show (ShowFullTree t) = VT.treeFullStr 0 t
  show (ShowTree t) = VT.treeToSubStr 0 True t

debugSpanRM :: (ReduceMonad s r m, Show a) => String -> m a -> m a
debugSpanRM name = _traceActionRM name Nothing

debugSpanArgsRM :: (ReduceMonad s r m, Show a) => String -> String -> m a -> m a
debugSpanArgsRM name args = _traceActionRM name (Just args)

_traceActionRM :: (ReduceMonad s r m, Show a) => String -> Maybe String -> m a -> m a
_traceActionRM name argsM f = withAddrAndFocus $ \addr _ -> do
  seg <- getRMTASeg
  bfocus <- getRMTree
  -- res <- f
  -- focus <- getRMTree
  let bTraced = if seg == RootTASeg then ShowFullTree bfocus else ShowTree bfocus
  debugSpan name (show addr) argsM bTraced $ do
    res <- f
    focus <- getRMTree
    let traced = if seg == RootTASeg then ShowFullTree focus else ShowTree focus
    return (res, traced)

debugInstantRM :: (ReduceMonad s r m) => String -> String -> m ()
debugInstantRM name args = withAddrAndFocus $ \addr _ -> debugInstant name (show addr) (Just args)