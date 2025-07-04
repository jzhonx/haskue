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
import Control.Monad.State.Strict (get, gets, modify, runStateT)
import Cursor
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)
import qualified Data.Set as Set
import qualified EvalExpr
import Exception (throwErrSt)
import Path
import {-# SOURCE #-} Reduce.Nodes (normalizeDisj)
import Text.Printf (printf)
import Util (HasTrace (..), Trace, debugInstant, debugSpan)
import Value

-- ReduceMonad is the environment for reducing the tree.
type ReduceMonad r s m =
  ( Common.Env r s m
  , Common.HasContext s
  )

-- | ReduceTCMonad is the environment for reducing the tree with tree cursor stored.
type ReduceTCMonad r s m =
  ( ReduceMonad r s m
  , HasTreeCursor s
  )

data RTCState = RTCstate
  { rtsTC :: TrCur
  , rtsCtx :: Common.Context
  }

instance HasTreeCursor RTCState where
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

mkRTState :: TrCur -> Int -> Trace -> RTCState
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

-- Global version

getRMGlobalVers :: (ReduceMonad r s m) => m Int
getRMGlobalVers = Common.ctxGlobalVers <$> getRMContext

setRMGlobalVers :: (ReduceMonad r s m) => Int -> m ()
setRMGlobalVers newVers = modifyRMContext (\ctx -> ctx{Common.ctxGlobalVers = newVers})

increaseRMGlobalVers :: (ReduceMonad r s m) => m Int
increaseRMGlobalVers = do
  vers <- getRMGlobalVers
  setRMGlobalVers (vers + 1)
  return (vers + 1)

-- Trace

getRMTrace :: (ReduceMonad r s m) => m Trace
getRMTrace = getTrace <$> getRMContext

setRMTrace :: (ReduceMonad r s m) => Trace -> m ()
setRMTrace trace = modifyRMContext (\ctx -> setTrace ctx trace)

-- Notif

getRMReadyQ :: (ReduceMonad r s m) => m [TreeAddr]
getRMReadyQ = Common.ctxReadyQueue <$> getRMContext

addToRMReadyQ :: (ReduceMonad r s m) => TreeAddr -> m ()
addToRMReadyQ addr = modifyRMContext (\ctx -> ctx{Common.ctxReadyQueue = addr : Common.ctxReadyQueue ctx})

popRMReadyQ :: (ReduceMonad r s m) => m (Maybe TreeAddr)
popRMReadyQ = do
  ctx <- getRMContext
  case Common.ctxReadyQueue ctx of
    [] -> return Nothing
    _ -> do
      -- TODO: efficiency
      let addr = last (Common.ctxReadyQueue ctx)
      putRMContext ctx{Common.ctxReadyQueue = init (Common.ctxReadyQueue ctx)}
      return (Just addr)

getRMNotifEnabled :: (ReduceMonad r s m) => m Bool
getRMNotifEnabled = Common.ctxNotifEnabled <$> getRMContext

setRMNotifEnabled :: (ReduceMonad r s m) => Bool -> m ()
setRMNotifEnabled b = modifyRMContext (\ctx -> ctx{Common.ctxNotifEnabled = b})

{- | Delete the notification receivers that have the specified prefix.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delRefSysRecvPrefix :: (ReduceMonad s r m) => TreeAddr -> m ()
delRefSysRecvPrefix addrPrefix = do
  modifyRMContext $ \ctx -> ctx{Common.ctxNotifGraph = delEmptyElem $ del (Common.ctxNotifGraph ctx)}
 where
  delEmptyElem :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  delEmptyElem = Map.filter (not . null)

  del :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  del = Map.map (filter (\p -> not (isPrefix addrPrefix p)))

{- | Delete the notification receivers of the sub values of the mutval.

If the receiver addresss is the mutable address itself, then it should be skipped because the mutable could be a
reference.

If the receiver addresss is the mutable address plus the argument segment, then it should be skipped.
-}
delMutValRecvs :: (ReduceMonad s r m) => TreeAddr -> m ()
delMutValRecvs mutAddr = modifyRMContext $ \ctx -> ctx{Common.ctxNotifGraph = delRecvsInMap mutAddr (Common.ctxNotifGraph ctx)}

-- | Delete the receivers that have the mutable address as the prefix.
delRecvsInMap :: TreeAddr -> Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
delRecvsInMap mutAddr =
  Map.mapMaybe
    ( \l ->
        let r =
              filter
                ( \recv ->
                    let
                      mutValAddr = appendSeg mutAddr SubValTASeg
                     in
                      not $ {-# SCC "isPrefix" #-} isPrefix mutValAddr recv
                )
                l
         in if null r
              then Nothing
              else Just r
    )

addRMUnreferredLet :: (ReduceMonad r s m) => TreeAddr -> m ()
addRMUnreferredLet addr = do
  ctx <- getRMContext
  let
    oldMap = Common.ctxLetMap ctx
    newMap = if addr `Map.member` oldMap then oldMap else Map.insert addr False oldMap
  putRMContext ctx{Common.ctxLetMap = newMap}

getRMUnreferredLets :: (ReduceMonad r s m) => m [TreeAddr]
getRMUnreferredLets = do
  ctx <- getRMContext
  let letAddrs = Map.toList (Common.ctxLetMap ctx)
  return [addr | (addr, False) <- letAddrs]

markRMLetReferred :: (ReduceMonad r s m) => TreeAddr -> m ()
markRMLetReferred addr = do
  ctx <- getRMContext
  let newMap = Map.insert addr True (Common.ctxLetMap ctx)
  putRMContext ctx{Common.ctxLetMap = newMap}

evalExprRM :: (ReduceMonad r s m) => AST.Expression -> m Tree
evalExprRM e = do
  curSID <- getRMObjID
  trace <- getRMTrace
  (rawT, newEEState) <- runStateT (EvalExpr.evalExpr e) (Common.EEState curSID trace)
  setRMObjID (Common.eesObjID newEEState)
  setRMTrace (Common.eesTrace newEEState)
  return rawT

{-
====== TreeAddr ======
-}

getTMAbsAddr :: (ReduceTCMonad r s m) => m TreeAddr
getTMAbsAddr = tcCanAddr <$> getTMCursor

getTMTASeg :: (ReduceTCMonad r s m) => m TASeg
getTMTASeg = do
  tc <- getTMCursor
  getTCFocusSeg tc

-- Cursor

getTMCursor :: (ReduceTCMonad r s m) => m TrCur
getTMCursor = do
  x <- get
  return $ {-# SCC "getTreeCursor" #-} getTreeCursor x

putTMCursor :: (ReduceTCMonad r s m) => TrCur -> m ()
putTMCursor tc = modify $ \s -> setTreeCursor s tc

-- Crumbs

getTMCrumbs :: (ReduceTCMonad r s m) => m [TreeCrumb]
getTMCrumbs = tcCrumbs <$> getTMCursor

-- Tree

getTMTree :: (ReduceTCMonad r s m) => m Tree
getTMTree = tcFocus <$> getTMCursor

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getTMParent :: (ReduceTCMonad r s m) => m Tree
getTMParent = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwErrSt "already at the top"
    (_, t) : _ -> return t

putTMTree :: (ReduceTCMonad r s m) => Tree -> m ()
putTMTree t = do
  tc <- getTMCursor
  putTMCursor (t `setTCFocus` tc)

withTree :: (ReduceTCMonad r s m) => (Tree -> m a) -> m a
withTree f = getTMTree >>= f

withAddrAndFocus :: (ReduceTCMonad r s m) => (TreeAddr -> Tree -> m a) -> m a
withAddrAndFocus f = do
  addr <- getTMAbsAddr
  withTree (f addr)

-- TreeNode

withTN :: (ReduceTCMonad r s m) => (TreeNode -> m a) -> m a
withTN f = withTree (f . treeNode)

modifyTMTN :: (ReduceTCMonad r s m) => TreeNode -> m ()
modifyTMTN tn = do
  t <- getTMTree
  putTMTree $ setTN t tn

modifyTMNodeWithTree :: (ReduceTCMonad r s m) => Tree -> m ()
modifyTMNodeWithTree t = modifyTMTN (treeNode t)

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
  case focus of
    IsBottom _ | isInDisj addr && not (isSegDisj seg) -> do
      _discardTMAndPop
      putTMTree focus
    _ -> propUpTC tc >>= putTMCursor

runTMTCAction :: (ReduceTCMonad r s m) => (forall n. (ReduceMonad r s n) => TrCur -> n Tree) -> m ()
runTMTCAction f = do
  tc <- getTMCursor
  r <- f tc
  putTMCursor (r `setTCFocus` tc)

-- Propagate the value up until the lowest segment is matched.
propUpTMUntilSeg :: (ReduceTCMonad r s m) => TASeg -> m ()
propUpTMUntilSeg seg = do
  tc <- getTMCursor
  unless (isMatched tc) $ do
    propUpTM
    propUpTMUntilSeg seg
 where
  isMatched :: TrCur -> Bool
  isMatched (TrCur _ []) = False -- propUpTM would panic.
  isMatched (TrCur _ ((s, _) : _)) = s == seg

-- Move down operations

descendTM :: (ReduceTCMonad r s m) => TreeAddr -> m Bool
descendTM dst = go (addrToList dst)
 where
  go :: (ReduceTCMonad r s m) => [TASeg] -> m Bool
  go [] = return True
  go (x : xs) = do
    r <- descendTMSeg x
    if r
      then go xs
      else return False

{- | Descend the tree cursor to the segment.

It closes the sub tree based on the parent tree.
-}
descendTMSeg :: (ReduceTCMonad r s m) => TASeg -> m Bool
descendTMSeg seg = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCSeg seg tc)

-- Push down operations

-- | Push down the segment with the new value.
_pushTMSub :: (ReduceTCMonad r s m) => TASeg -> Tree -> m ()
_pushTMSub seg sub = do
  (TrCur p crumbs) <- getTMCursor
  putTMCursor $ TrCur sub ((seg, p) : crumbs)

-- Push and pop operations

{- | Run the action in the sub tree.

The sub tree must exist.
-}
inSubTM :: (ReduceTCMonad r s m) => TASeg -> m a -> m a
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
    crumbs = tcCrumbs tc
    headC = head crumbs
  putTMCursor (TrCur (snd headC) (tail crumbs))

treeDepthCheck :: (ReduceMonad r s m) => TrCur -> m ()
treeDepthCheck tc = do
  let
    crumbs = tcCrumbs tc
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
  case treeNode t of
    TNBottom _ -> return a
    _ -> f

mustMutable :: (ReduceTCMonad r s m) => (Mutable -> m a) -> m a
mustMutable f = withTree $ \t -> case treeNode t of
  TNMutable fn -> f fn
  _ -> throwErrSt $ printf "tree focus %s is not a mutator" (show t)

{- | Traverse all the one-level sub nodes of the tree.

For the bottom handling:
1. It surfaces the bottom as field value.
-}
traverseSub :: forall s r m. (ReduceTCMonad r s m) => m () -> m ()
traverseSub f = withTree $ \_t -> do
  mapM_ (\(seg, _) -> inSubTM seg f) (subNodes _t)

  t <- getTMTree
  case treeNode t of
    -- If the any of the sub node is reduced to bottom, then the parent struct node should be reduced to bottom.
    TNBlock (IsBlockStruct struct) -> do
      let errM =
            foldl
              ( \acc field ->
                  if
                    | isJust acc -> acc
                    | IsBottom _ <- (ssfValue field) -> Just (ssfValue field)
                    | otherwise -> Nothing
              )
              Nothing
              (stcFields struct)
      maybe (return ()) putTMTree errM
    TNDisj dj -> do
      newDjT <- normalizeDisj mkDisjTree dj
      modifyTMNodeWithTree newDjT
    _ -> return ()

{- | Traverse the leaves of the tree cursor in the following order

1. Traverse the current node.
2. Traverse the sub-tree with the segment.
-}
traverseTM :: (ReduceTCMonad r s m) => m () -> m ()
traverseTM f = f >> traverseSub (traverseTM f)

data ShowTree = ShowFullTree Tree | ShowTree Tree

instance Show ShowTree where
  show (ShowFullTree t) = treeFullStr 0 t
  show (ShowTree t) = treeToSubStr 0 True t

whenTraceEnabled :: (Common.Env r s m) => String -> m a -> m a -> m a
whenTraceEnabled name f traced = do
  Common.Config{Common.cfSettings = Common.Settings{Common.stTraceExec = traceExec, Common.stTraceFilter = tFilter}} <-
    asks Common.getConfig
  if traceExec && (Set.null tFilter || Set.member name tFilter)
    then traced
    else f

spanTreeMsgs :: (Common.Env r s m) => Tree -> m (String, String)
spanTreeMsgs t = do
  Common.Config{Common.cfSettings = Common.Settings{Common.stTracePrintTree = tracePrintTree}} <- asks Common.getConfig
  if not tracePrintTree
    then return ("", "")
    else do
      e <- buildASTExprDebug t
      return (show t, BS.unpack $ toLazyByteString (AST.exprBld e))

debugSpanTM :: (ReduceTCMonad r s m, Show a) => String -> m a -> m a
debugSpanTM name = _traceActionTM name Nothing

debugSpanArgsTM :: (ReduceTCMonad r s m, Show a) => String -> String -> m a -> m a
debugSpanArgsTM name args = _traceActionTM name (Just args)

_traceActionTM :: (ReduceTCMonad r s m, Show a) => String -> Maybe String -> m a -> m a
_traceActionTM name argsM f = whenTraceEnabled name f $ withAddrAndFocus $ \addr _ -> do
  bTraced <- getTMTree >>= spanTreeMsgs
  debugSpan True name (show addr) argsM bTraced $ do
    res <- f
    traced <- getTMTree >>= spanTreeMsgs
    return (res, fst traced, snd traced)

debugInstantTM :: (ReduceTCMonad r s m) => String -> String -> m ()
debugInstantTM name args = whenTraceEnabled name (return ()) $
  withAddrAndFocus $
    \addr _ -> debugInstant True name (show addr) (Just args)

debugSpanRM :: (Common.Env r s m, Show a) => String -> (a -> Maybe Tree) -> TrCur -> m a -> m a
debugSpanRM name = _traceActionRM name Nothing

debugSpanArgsRM :: (Common.Env r s m, Show a) => String -> String -> (a -> Maybe Tree) -> TrCur -> m a -> m a
debugSpanArgsRM name args = _traceActionRM name (Just args)

_traceActionRM ::
  (Common.Env r s m, Show a) => String -> Maybe String -> (a -> Maybe Tree) -> TrCur -> m a -> m a
_traceActionRM name argsM g tc f = whenTraceEnabled name f $ do
  let
    addr = tcCanAddr tc
    bfocus = tcFocus tc
  bTraced <- spanTreeMsgs bfocus
  debugSpan True name (show addr) argsM bTraced $ do
    res <- f
    traced <- maybe (return ("", "")) spanTreeMsgs (g res)
    return (res, fst traced, snd traced)

-- | Trace the operation.
debugSpanOpRM :: (Common.Env r s m, Show a) => String -> TreeAddr -> m a -> m a
debugSpanOpRM name = _traceOpActionRM name Nothing

-- | Trace the operation.
debugSpanArgsOpRM :: (Common.Env r s m, Show a) => String -> String -> TreeAddr -> m a -> m a
debugSpanArgsOpRM name args = _traceOpActionRM name (Just args)

_traceOpActionRM :: (Common.Env r s m, Show a) => String -> Maybe String -> TreeAddr -> m a -> m a
_traceOpActionRM name argsM addr f = whenTraceEnabled name f $ do
  debugSpan True name (show addr) argsM ("", "") $ do
    res <- f
    return (res, "", "")

debugInstantRM :: (Common.Env r s m) => String -> String -> TrCur -> m ()
debugInstantRM name args tc = whenTraceEnabled name (return ()) $ do
  let addr = tcCanAddr tc
  debugInstant True name (show addr) (Just args)

debugInstantOpRM :: (Common.Env r s m) => String -> String -> TreeAddr -> m ()
debugInstantOpRM name args addr = whenTraceEnabled name (return ()) $ do
  debugInstant True name (show addr) (Just args)