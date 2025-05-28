{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RMonad where

import qualified AST
import qualified Common
import Control.Monad (unless, when)
import Control.Monad.Except (throwError)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (gets, modify, runStateT)
import qualified Cursor
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified TCOps
import Text.Printf (printf)
import Util (HasTrace (..), Trace, debugInstant, debugSpan, logDebugStr)
import qualified Value.Tree as VT

-- ReduceMonad is the environment for reducing the tree.
type ReduceMonad r s m =
  ( Common.Env r s m
  , Common.HasContext s
  , MutEnv.HasFuncs r VT.Tree
  )

-- | ReduceTCMonad is the environment for reducing the tree with tree cursor stored.
type ReduceTCMonad r s m =
  ( ReduceMonad r s m
  , Cursor.HasTreeCursor s VT.Tree
  )

data RTCState t = RTCstate
  { rtsTC :: Cursor.TreeCursor t
  , rtsCtx :: Common.Context
  }

instance Cursor.HasTreeCursor (RTCState t) t where
  getTreeCursor = rtsTC
  setTreeCursor s tc = s{rtsTC = tc}

instance Common.HasContext (RTCState t) where
  getContext = rtsCtx
  setContext s ctx = s{rtsCtx = ctx}
  modifyContext s f = s{rtsCtx = f (rtsCtx s)}

instance HasTrace (RTCState t) where
  getTrace = Common.ctxTrace . rtsCtx
  setTrace s trace = s{rtsCtx = setTrace (rtsCtx s) trace}

instance Common.IDStore (RTCState t) where
  getID = Common.getID . rtsCtx
  setID s newID = s{rtsCtx = Common.setID (rtsCtx s) newID}

mkRTState :: Cursor.TreeCursor t -> Int -> Trace -> RTCState t
mkRTState tc oid trace =
  RTCstate
    { rtsTC = tc
    , rtsCtx =
        Common.emptyContext
          { Common.ctxObjID = oid
          , Common.ctxTrace = trace
          }
    }

-- Context

getRMContext :: (ReduceMonad r s m) => m Common.Context
getRMContext = gets Common.getContext

putRMContext :: (ReduceMonad r s m) => Common.Context -> m ()
putRMContext ctx = modify $ \s -> Common.setContext s ctx

modifyRMContext :: (ReduceMonad r s m) => (Common.Context -> Common.Context) -> m ()
modifyRMContext f = do
  ctx <- getRMContext
  putRMContext (f ctx)

-- ObjID

allocRMObjID :: (ReduceMonad r s m) => m Int
allocRMObjID = do
  oid <- getRMObjID
  let newOID = oid + 1
  setRMObjID newOID
  return newOID

getRMObjID :: (ReduceMonad r s m) => m Int
getRMObjID = Common.getID <$> getRMContext

setRMObjID :: (ReduceMonad r s m) => Int -> m ()
setRMObjID newID = modifyRMContext (\ctx -> Common.setID ctx newID)

-- Trace

getRMTrace :: (ReduceMonad r s m) => m Trace
getRMTrace = getTrace <$> getRMContext

setRMTrace :: (ReduceMonad r s m) => Trace -> m ()
setRMTrace trace = modifyRMContext (\ctx -> setTrace ctx trace)

-- Notif

getRMNotifQ :: (ReduceMonad r s m) => m [Path.TreeAddr]
getRMNotifQ = Common.ctxNotifQueue <$> getRMContext

addToRMNotifQ :: (ReduceMonad r s m) => Path.TreeAddr -> m ()
addToRMNotifQ addr = modifyRMContext (\ctx -> ctx{Common.ctxNotifQueue = addr : Common.ctxNotifQueue ctx})

popRMNotifQ :: (ReduceMonad r s m) => m (Maybe Path.TreeAddr)
popRMNotifQ = do
  ctx <- getRMContext
  case Common.ctxNotifQueue ctx of
    [] -> return Nothing
    _ -> do
      -- TODO: efficiency
      let addr = last (Common.ctxNotifQueue ctx)
      putRMContext ctx{Common.ctxNotifQueue = init (Common.ctxNotifQueue ctx)}
      return (Just addr)

getRMNotifEnabled :: (ReduceMonad r s m) => m Bool
getRMNotifEnabled = Common.ctxNotifEnabled <$> getRMContext

setRMNotifEnabled :: (ReduceMonad r s m) => Bool -> m ()
setRMNotifEnabled b = modifyRMContext (\ctx -> ctx{Common.ctxNotifEnabled = b})

addRMUnreferredLet :: (ReduceMonad r s m) => Path.TreeAddr -> m ()
addRMUnreferredLet addr = do
  ctx <- getRMContext
  let
    oldMap = Common.ctxLetMap ctx
    newMap = if addr `Map.member` oldMap then oldMap else Map.insert addr False oldMap
  putRMContext ctx{Common.ctxLetMap = newMap}

getRMUnreferredLets :: (ReduceMonad r s m) => m [Path.TreeAddr]
getRMUnreferredLets = do
  ctx <- getRMContext
  let letAddrs = Map.toList (Common.ctxLetMap ctx)
  return [addr | (addr, False) <- letAddrs]

markRMLetReferred :: (ReduceMonad r s m) => Path.TreeAddr -> m ()
markRMLetReferred addr = do
  ctx <- getRMContext
  let newMap = Map.insert addr True (Common.ctxLetMap ctx)
  putRMContext ctx{Common.ctxLetMap = newMap}

evalExprRM :: (ReduceMonad r s m) => AST.Expression -> m VT.Tree
evalExprRM e = do
  MutEnv.Functions{MutEnv.fnEvalExpr = evalExpr} <- asks MutEnv.getFuncs
  curSID <- getRMObjID
  trace <- getRMTrace
  (rawT, newEEState) <- runStateT (evalExpr e) (Common.EEState curSID trace)
  setRMObjID (Common.eesObjID newEEState)
  setRMTrace (Common.eesTrace newEEState)
  return rawT

{-
====== TreeAddr ======
-}

getTMAbsAddr :: (ReduceTCMonad r s m) => m Path.TreeAddr
getTMAbsAddr = Cursor.tcCanAddr <$> getTMCursor

getTMTASeg :: (ReduceTCMonad r s m) => m Path.TASeg
getTMTASeg = do
  tc <- getTMCursor
  TCOps.getTCFocusSeg tc

-- Cursor

getTMCursor :: (ReduceTCMonad r s m) => m TCOps.TrCur
getTMCursor = gets Cursor.getTreeCursor

putTMCursor :: (ReduceTCMonad r s m) => TCOps.TrCur -> m ()
putTMCursor tc = modify $ \s -> Cursor.setTreeCursor s tc

-- Crumbs

getTMCrumbs :: (ReduceTCMonad r s m) => m [Cursor.TreeCrumb VT.Tree]
getTMCrumbs = Cursor.tcCrumbs <$> getTMCursor

-- VT.Tree

getTMTree :: (ReduceTCMonad r s m) => m VT.Tree
getTMTree = Cursor.tcFocus <$> getTMCursor

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getTMParent :: (ReduceTCMonad r s m) => m VT.Tree
getTMParent = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwErrSt "already at the top"
    (_, t) : _ -> return t

putTMTree :: (ReduceTCMonad r s m) => VT.Tree -> m ()
putTMTree t = do
  tc <- getTMCursor
  putTMCursor (t `Cursor.setTCFocus` tc)

withTree :: (ReduceTCMonad r s m) => (VT.Tree -> m a) -> m a
withTree f = getTMTree >>= f

withAddrAndFocus :: (ReduceTCMonad r s m) => (Path.TreeAddr -> VT.Tree -> m a) -> m a
withAddrAndFocus f = do
  addr <- getTMAbsAddr
  withTree (f addr)

-- VT.TreeNode

withTN :: (ReduceTCMonad r s m) => (VT.TreeNode VT.Tree -> m a) -> m a
withTN f = withTree (f . VT.treeNode)

modifyTMTN :: (ReduceTCMonad r s m) => VT.TreeNode VT.Tree -> m ()
modifyTMTN tn = do
  t <- getTMTree
  putTMTree $ VT.setTN t tn

modifyTMNodeWithTree :: (ReduceTCMonad r s m) => VT.Tree -> m ()
modifyTMNodeWithTree t = modifyTMTN (VT.treeNode t)

-- ReduceTCMonad operations

-- PropUp operations

{- | Propagate the value up.

For the bottom handling:
1. It surfaces the bottom only if the bottom is in a disjunction but not a disjunct.

For example, x: (1 & 2) + 1 | 2. The bottom is in the disjunction but not a disjunct.
-}
propUpTM :: (ReduceTCMonad r s m) => m ()
propUpTM = do
  tc <- getTMCursor
  addr <- getTMAbsAddr
  seg <- getTMTASeg
  focus <- getTMTree

  -- If the focus is a bottom and the address is not an immediate disj, then we should overwrite the parent with the
  -- bottom.
  if Common.isTreeBottom focus && Path.isInDisj addr && not (Path.isSegDisj seg)
    then do
      _discardTMAndPop
      putTMTree focus
    else TCOps.propUpTC tc >>= putTMCursor

runTMTCAction :: (ReduceTCMonad r s m) => (forall n. (ReduceMonad r s n) => TCOps.TrCur -> n VT.Tree) -> m ()
runTMTCAction f = do
  tc <- getTMCursor
  r <- f tc
  putTMCursor (r `Cursor.setTCFocus` tc)

-- Propagate the value up until the lowest segment is matched.
propUpTMUntilSeg :: (ReduceTCMonad r s m) => Path.TASeg -> m ()
propUpTMUntilSeg seg = do
  tc <- getTMCursor
  unless (isMatched tc) $ do
    propUpTM
    propUpTMUntilSeg seg
 where
  isMatched :: TCOps.TrCur -> Bool
  isMatched (Cursor.TreeCursor _ []) = False -- propUpTM would panic.
  isMatched (Cursor.TreeCursor _ ((s, _) : _)) = s == seg

-- Move down operations

descendTM :: (ReduceTCMonad r s m) => Path.TreeAddr -> m Bool
descendTM dst = go (Path.addrToNormOrdList dst)
 where
  go :: (ReduceTCMonad r s m) => [Path.TASeg] -> m Bool
  go [] = return True
  go (x : xs) = do
    r <- descendTMSeg x
    if r
      then go xs
      else return False

{- | Descend the tree cursor to the segment.

It closes the sub tree based on the parent tree.
-}
descendTMSeg :: (ReduceTCMonad r s m) => Path.TASeg -> m Bool
descendTMSeg seg = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (TCOps.goDownTCSeg seg tc)

-- Push down operations

-- | Push down the segment with the new value.
_pushTMSub :: (ReduceTCMonad r s m) => Path.TASeg -> VT.Tree -> m ()
_pushTMSub seg sub = do
  (Cursor.TreeCursor p crumbs) <- getTMCursor
  putTMCursor $ Cursor.TreeCursor sub ((seg, p) : crumbs)

-- Push and pop operations

{- | Run the action in the sub tree.

The sub tree must exist.
-}
inSubTM :: (ReduceTCMonad r s m) => Path.TASeg -> m a -> m a
inSubTM seg f = do
  ok <- descendTMSeg seg
  unless ok $ throwErrSt $ printf "descend to %s failed" (show seg)
  r <- f
  propUpTM
  return r

-- | discard the current focus, pop up and put the original focus in the crumbs back.
_discardTMAndPop :: (ReduceTCMonad r s m) => m ()
_discardTMAndPop = do
  tc <- getTMCursor
  let
    crumbs = Cursor.tcCrumbs tc
    headC = head crumbs
  putTMCursor (Cursor.TreeCursor (snd headC) (tail crumbs))

treeDepthCheck :: (ReduceMonad r s m) => TCOps.TrCur -> m ()
treeDepthCheck tc = do
  let
    crumbs = Cursor.tcCrumbs tc
    depth = length crumbs
  Common.Config
    { Common.cfSettings = Common.Settings{Common.stMaxTreeDepth = maxDepth}
    } <-
    asks Common.getConfig
  let maxDepthVal = if maxDepth <= 0 then 1000 else maxDepth
  when (depth > maxDepthVal) $ throwError $ printf "tree depth exceeds max depth (%d)" maxDepthVal

unlessFocusBottom :: (ReduceTCMonad r s m) => a -> m a -> m a
unlessFocusBottom a f = do
  t <- getTMTree
  case VT.treeNode t of
    VT.TNBottom _ -> return a
    _ -> f

mustMutable :: (ReduceTCMonad r s m) => (VT.Mutable VT.Tree -> m a) -> m a
mustMutable f = withTree $ \t -> case VT.treeNode t of
  VT.TNMutable fn -> f fn
  _ -> throwErrSt $ printf "tree focus %s is not a mutator" (show t)

{- | Traverse all the one-level sub nodes of the tree.

For the bottom handling:
1. It surfaces the bottom as field value.
-}
traverseSub :: forall s r m. (ReduceTCMonad r s m) => m () -> m ()
traverseSub f = withTree $ \_t -> do
  mapM_ (\(seg, _) -> inSubTM seg f) (VT.subNodes _t)

  t <- getTMTree
  case VT.treeNode t of
    -- If the any of the sub node is reduced to bottom, then the parent struct node should be reduced to bottom.
    VT.TNBlock es@(VT.Block{VT.blkStruct = struct})
      | isNothing (VT.blkNonStructValue es) -> do
          let errM =
                foldl
                  ( \acc field ->
                      if
                        | isJust acc -> acc
                        | Common.isTreeBottom (VT.ssfValue field) -> Just (VT.ssfValue field)
                        | otherwise -> Nothing
                  )
                  Nothing
                  (VT.stcFields struct)
          maybe (return ()) putTMTree errM
    VT.TNDisj dj -> do
      newDjT <- VT.normalizeDisj VT.getDisjFromTree VT.mkDisjTree dj
      modifyTMNodeWithTree newDjT
    _ -> return ()

{- | Traverse the leaves of the tree cursor in the following order

1. Traverse the current node.
2. Traverse the sub-tree with the segment.
-}
traverseTM :: (ReduceTCMonad r s m) => m () -> m ()
traverseTM f = f >> traverseSub (traverseTM f)

logDebugStrRM :: (ReduceTCMonad r s m) => String -> String -> m ()
logDebugStrRM hdr msg = withAddrAndFocus $ \addr _ -> logDebugStr $ printf "%s: addr: %s, %s" hdr (show addr) msg

data ShowTree = ShowFullTree VT.Tree | ShowTree VT.Tree

instance Show ShowTree where
  show (ShowFullTree t) = VT.treeFullStr 0 t
  show (ShowTree t) = VT.treeToSubStr 0 True t

whenTraceEnabled :: (Common.Env r s m) => m a -> m a -> m a
whenTraceEnabled f traced = do
  Common.Config{Common.cfSettings = Common.Settings{Common.stTraceExec = traceExec}} <- asks Common.getConfig
  if not traceExec
    then f
    else traced

canonicalizeTree :: (Common.Env r s m) => VT.Tree -> m VT.Tree
canonicalizeTree t = Cursor.tcFocus <$> TCOps.snapshotTC (Cursor.TreeCursor t [])

spanTreeMsgs :: (Common.Env r s m) => VT.Tree -> m (String, String)
spanTreeMsgs t = do
  Common.Config{Common.cfSettings = Common.Settings{Common.stTracePrintTree = tracePrintTree}} <- asks Common.getConfig
  if not tracePrintTree
    then return ("", "")
    else do
      r <- canonicalizeTree t
      e <- Common.buildASTExpr False r
      return (show r, BS.unpack $ toLazyByteString (AST.exprBld e))

debugSpanTM :: (ReduceTCMonad r s m, Show a) => String -> m a -> m a
debugSpanTM name = _traceActionTM name Nothing

debugSpanArgsTM :: (ReduceTCMonad r s m, Show a) => String -> String -> m a -> m a
debugSpanArgsTM name args = _traceActionTM name (Just args)

_traceActionTM :: (ReduceTCMonad r s m, Show a) => String -> Maybe String -> m a -> m a
_traceActionTM name argsM f = whenTraceEnabled f $ withAddrAndFocus $ \addr _ -> do
  bTraced <- getTMTree >>= spanTreeMsgs
  debugSpan name (show addr) argsM bTraced $ do
    res <- f
    traced <- getTMTree >>= spanTreeMsgs
    return (res, fst traced, snd traced)

debugInstantTM :: (ReduceTCMonad r s m) => String -> String -> m ()
debugInstantTM name args = whenTraceEnabled (return ()) $
  withAddrAndFocus $
    \addr _ -> debugInstant name (show addr) (Just args)

debugSpanRM :: (Common.Env r s m, Show a) => String -> (a -> Maybe VT.Tree) -> TCOps.TrCur -> m a -> m a
debugSpanRM name = _traceActionRM name Nothing

debugSpanArgsRM :: (Common.Env r s m, Show a) => String -> String -> (a -> Maybe VT.Tree) -> TCOps.TrCur -> m a -> m a
debugSpanArgsRM name args = _traceActionRM name (Just args)

_traceActionRM ::
  (Common.Env r s m, Show a) => String -> Maybe String -> (a -> Maybe VT.Tree) -> TCOps.TrCur -> m a -> m a
_traceActionRM name argsM g tc f = whenTraceEnabled f $ do
  let
    addr = Cursor.tcCanAddr tc
    bfocus = Cursor.tcFocus tc
  bTraced <- spanTreeMsgs bfocus
  debugSpan name (show addr) argsM bTraced $ do
    res <- f
    traced <- maybe (return ("", "")) spanTreeMsgs (g res)
    return (res, fst traced, snd traced)

-- | Trace the operation.
debugSpanOpRM :: (Common.Env r s m, Show a) => String -> Path.TreeAddr -> m a -> m a
debugSpanOpRM name = _traceOpActionRM name Nothing

-- | Trace the operation.
debugSpanArgsOpRM :: (Common.Env r s m, Show a) => String -> String -> Path.TreeAddr -> m a -> m a
debugSpanArgsOpRM name args = _traceOpActionRM name (Just args)

_traceOpActionRM :: (Common.Env r s m, Show a) => String -> Maybe String -> Path.TreeAddr -> m a -> m a
_traceOpActionRM name argsM addr f = whenTraceEnabled f $ do
  debugSpan name (show addr) argsM ("", "") $ do
    res <- f
    return (res, "", "")

debugInstantRM :: (Common.Env r s m) => String -> String -> TCOps.TrCur -> m ()
debugInstantRM name args tc = whenTraceEnabled (return ()) $ do
  let addr = Cursor.tcCanAddr tc
  debugInstant name (show addr) (Just args)

debugInstantOpRM :: (Common.Env r s m) => String -> String -> Path.TreeAddr -> m ()
debugInstantOpRM name args addr = whenTraceEnabled (return ()) $ do
  debugInstant name (show addr) (Just args)