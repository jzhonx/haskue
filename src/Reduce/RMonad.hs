{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RMonad where

import qualified AST
import Common (
  Config (..),
  HasConfig (..),
  IDStore (..),
  emptyConfig,
 )
import Control.Monad (foldM, unless, when)
import Control.Monad.Except (ExceptT, MonadError, modifyError, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader, asks)
import Control.Monad.State.Strict (MonadState, get, gets, modify)
import Cursor
import Data.Aeson (ToJSON, Value, toJSON)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import EvalExpr (evalExpr)
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import NotifGraph
import Path
import Text.Printf (printf)
import Util (HasTrace (..), Trace, debugInstant, debugSpan, emptyTrace)
import Value
import Value.Util.TreeRep

data FetchResult = FRDirty | FRCyclic | FRSCyclic | FRNormal
  deriving (Eq, Show)

type Fetch = SuffixIrredAddr -> FetchResult

data ReduceParams = ReduceParams
  { createCnstr :: Bool
  , fetch :: Fetch
  -- ^ Custom fetch function that fetches the tree at the suffix irreducible address.
  -- If the custom value is not found, it should return 'Right Nothing'.
  }

instance Show ReduceParams where
  show c = "ReduceParams {createCnstr = " ++ show c.createCnstr ++ " }"

emptyReduceParams :: ReduceParams
emptyReduceParams =
  ReduceParams
    { createCnstr = False
    , fetch = const FRNormal
    }

class HasReduceParams s where
  getReduceParams :: s -> ReduceParams
  setReduceParams :: s -> ReduceParams -> s
  modifyReduceParams :: (ReduceParams -> ReduceParams) -> s -> s

data ReduceConfig = ReduceConfig
  { baseConfig :: Config
  , params :: ReduceParams
  }
  deriving (Show)

instance HasConfig ReduceConfig where
  getConfig = baseConfig
  setConfig r c = r{baseConfig = c}
  modifyConfig f r = r{baseConfig = f (baseConfig r)}

instance HasReduceParams ReduceConfig where
  getReduceParams = params
  setReduceParams r p = r{params = p}
  modifyReduceParams f r = r{params = f (params r)}

emptyReduceConfig :: ReduceConfig
emptyReduceConfig =
  ReduceConfig
    { baseConfig = emptyConfig
    , params = emptyReduceParams
    }

class HasContext s where
  getContext :: s -> Context
  setContext :: s -> Context -> s
  modifyContext :: s -> (Context -> Context) -> s

data Context = Context
  { ctxObjID :: !Int
  , ctxReduceStack :: [TreeAddr]
  , isRecalcing :: !Bool
  , ctxNotifGraph :: NotifGraph
  , ctxLetMap :: Map.Map TreeAddr Bool
  , rcdIsReducingRCs :: !Bool
  , ctxTrace :: Trace
  }
  deriving (Eq, Show)

instance HasTrace Context where
  getTrace = ctxTrace
  setTrace ctx t = ctx{ctxTrace = t}

instance IDStore Context where
  getID = ctxObjID
  setID ctx i = ctx{ctxObjID = i}

instance HasContext Context where
  getContext = id
  setContext _ = id
  modifyContext ctx f = f ctx

emptyContext :: Context
emptyContext =
  Context
    { ctxObjID = 0
    , ctxReduceStack = []
    , isRecalcing = False
    , ctxNotifGraph = emptyNotifGraph
    , ctxLetMap = Map.empty
    , rcdIsReducingRCs = False
    , ctxTrace = emptyTrace
    }

showRefNotifiers :: Map.Map TreeAddr [TreeAddr] -> String
showRefNotifiers notifiers =
  let s = Map.foldrWithKey go "" notifiers
   in if null s then "[]" else "[" ++ s ++ "\n]"
 where
  go :: TreeAddr -> [TreeAddr] -> String -> String
  go src deps acc = acc ++ "\n" ++ show src ++ " -> " ++ show deps

data Error
  = FatalErr String
  | DirtyDep SuffixIrredAddr

instance Show Error where
  show (FatalErr msg) = msg
  show (DirtyDep siAddr) = printf "dependency %s is dirty" (show siAddr)

throwFatal :: (MonadError Error m, HasCallStack) => String -> m a
throwFatal msg = throwError $ FatalErr $ msg ++ "\n" ++ prettyCallStack callStack

throwDirty :: (MonadError Error m) => SuffixIrredAddr -> m a
throwDirty siAddr = throwError $ DirtyDep siAddr

liftFatal :: (MonadError Error m) => ExceptT String m a -> m a
liftFatal = modifyError FatalErr

-- ResolveMonad is the environment for reducing the tree.
type ResolveMonad r s m =
  ( MonadError Error m
  , HasCallStack
  , MonadReader r m
  , HasConfig r
  , MonadState s m
  , HasTrace s
  , MonadIO m
  , HasContext s
  , HasReduceParams r
  , IDStore s
  )

-- | ReduceMonad is the environment for reducing the tree with tree cursor stored.
type ReduceMonad r s m =
  ( ResolveMonad r s m
  , HasTreeCursor s
  )

data RTCState = RTCState
  { rtsTC :: TrCur
  , rtsCtx :: Context
  }

instance HasTreeCursor RTCState where
  getTreeCursor = rtsTC
  setTreeCursor s tc = s{rtsTC = tc}

instance HasContext RTCState where
  getContext = rtsCtx
  setContext s ctx = s{rtsCtx = ctx}
  modifyContext s f = s{rtsCtx = f (rtsCtx s)}

instance HasTrace RTCState where
  getTrace = ctxTrace . rtsCtx
  setTrace s trace = s{rtsCtx = setTrace (rtsCtx s) trace}

instance IDStore RTCState where
  getID = getID . rtsCtx
  setID s newID = s{rtsCtx = setID (rtsCtx s) newID}

mkRTState :: TrCur -> Int -> Trace -> RTCState
mkRTState tc oid trace =
  RTCState
    { rtsTC = tc
    , rtsCtx =
        emptyContext
          { ctxObjID = oid
          , ctxTrace = trace
          }
    }

-- Context

getRMContext :: (ResolveMonad r s m) => m Context
getRMContext = gets getContext

putRMContext :: (ResolveMonad r s m) => Context -> m ()
putRMContext ctx = modify $ \s -> setContext s ctx

modifyRMContext :: (ResolveMonad r s m) => (Context -> Context) -> m ()
modifyRMContext f = do
  ctx <- getRMContext
  putRMContext (f ctx)

-- ObjID

allocRMObjID :: (ResolveMonad r s m) => m Int
allocRMObjID = do
  oid <- getRMObjID
  let newOID = oid + 1
  setRMObjID newOID
  return newOID

getRMObjID :: (ResolveMonad r s m) => m Int
getRMObjID = getID <$> getRMContext

setRMObjID :: (ResolveMonad r s m) => Int -> m ()
setRMObjID newID = modifyRMContext (\ctx -> setID ctx newID)

-- Trace

getRMTrace :: (ResolveMonad r s m) => m Trace
getRMTrace = getTrace <$> getRMContext

setRMTrace :: (ResolveMonad r s m) => Trace -> m ()
setRMTrace trace = modifyRMContext (\ctx -> setTrace ctx trace)

{- | Delete the notification receivers that have the specified prefix.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delTMDependentPrefix :: (ResolveMonad r s m) => TreeAddr -> m ()
delTMDependentPrefix addrPrefix = do
  modifyRMContext $ \ctx -> ctx{ctxNotifGraph = delDepPrefixFromNG addrPrefix (ctxNotifGraph ctx)}

delMutValRecvs :: (ResolveMonad r s m) => TreeAddr -> m ()
delMutValRecvs = undefined

addRMDanglingLet :: (ResolveMonad r s m) => TreeAddr -> m ()
addRMDanglingLet addr = do
  ctx <- getRMContext
  let
    oldMap = ctxLetMap ctx
    newMap = if addr `Map.member` oldMap then oldMap else Map.insert addr False oldMap
  putRMContext ctx{ctxLetMap = newMap}

getRMDanglingLets :: (ResolveMonad r s m) => m [TreeAddr]
getRMDanglingLets = do
  ctx <- getRMContext
  let letAddrs = Map.toList (ctxLetMap ctx)
  return [addr | (addr, False) <- letAddrs]

markRMLetReferred :: (ResolveMonad r s m) => TreeAddr -> m ()
markRMLetReferred addr = do
  ctx <- getRMContext
  let newMap = Map.insert addr True (ctxLetMap ctx)
  putRMContext ctx{ctxLetMap = newMap}

evalExprRM :: (ResolveMonad r s m) => AST.Expression -> m Tree
evalExprRM e = modifyError FatalErr (evalExpr e)

{-
====== TreeAddr ======
-}

getTMAbsAddr :: (ReduceMonad r s m) => m TreeAddr
getTMAbsAddr = tcAddr <$> getTMCursor

getTMTASeg :: (ReduceMonad r s m) => m TASeg
getTMTASeg = do
  tc <- getTMCursor
  modifyError FatalErr (tcFocusSegMust tc)

-- Cursor

getTMCursor :: (ReduceMonad r s m) => m TrCur
getTMCursor = do
  x <- get
  return $ {-# SCC "getTreeCursor" #-} getTreeCursor x

putTMCursor :: (ReduceMonad r s m) => TrCur -> m ()
putTMCursor tc = modify $ \s -> setTreeCursor s tc

-- Crumbs

getTMCrumbs :: (ReduceMonad r s m) => m [(TASeg, Tree)]
getTMCrumbs = tcCrumbs <$> getTMCursor

-- Tree

getTMTree :: (ReduceMonad r s m) => m Tree
getTMTree = tcFocus <$> getTMCursor

putTMTree :: (ReduceMonad r s m) => Tree -> m ()
putTMTree t = do
  tc <- getTMCursor
  putTMCursor (t `setTCFocus` tc)

modifyTMTree :: (ReduceMonad r s m) => (Tree -> Tree) -> m ()
modifyTMTree f = do
  t <- getTMTree
  putTMTree (f t)

withTree :: (ReduceMonad r s m) => (Tree -> m a) -> m a
withTree f = getTMTree >>= f

withAddrAndFocus :: (ReduceMonad r s m) => (TreeAddr -> Tree -> m a) -> m a
withAddrAndFocus f = do
  addr <- getTMAbsAddr
  withTree (f addr)

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getTMParent :: (ReduceMonad r s m) => m Tree
getTMParent = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwFatal "already at the top"
    (_, t) : _ -> return t

-- TreeNode

withTN :: (ReduceMonad r s m) => (TreeNode -> m a) -> m a
withTN f = withTree (f . treeNode)

modifyTMTN :: (ReduceMonad r s m) => TreeNode -> m ()
modifyTMTN tn = do
  t <- getTMTree
  putTMTree $ setTN t tn

modifyTMNodeWithTree :: (ReduceMonad r s m) => Tree -> m ()
modifyTMNodeWithTree t = modifyTMTN (treeNode t)

-- ReduceMonad operations

-- PropUp operations

-- | Propagate the value up.
propUpTM :: (ReduceMonad r s m) => m ()
propUpTM = do
  tc <- getTMCursor
  modifyError FatalErr (propUpTC tc) >>= putTMCursor

runTMTCAction :: (ReduceMonad r s m) => (forall n. (ResolveMonad r s n) => TrCur -> n Tree) -> m ()
runTMTCAction f = do
  tc <- getTMCursor
  r <- f tc
  putTMCursor (r `setTCFocus` tc)

-- Propagate the value up until the lowest segment is matched.
propUpTMUntilSeg :: (ReduceMonad r s m) => TASeg -> m ()
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

descendTM :: (ReduceMonad r s m) => TreeAddr -> m Bool
descendTM dst = go (addrToList dst)
 where
  go :: (ReduceMonad r s m) => [TASeg] -> m Bool
  go [] = return True
  go (x : xs) = do
    r <- descendTMSeg x
    if r
      then go xs
      else return False

{- | Descend the tree cursor to the segment.

It closes the sub tree based on the parent tree.
-}
descendTMSeg :: (ReduceMonad r s m) => TASeg -> m Bool
descendTMSeg seg = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCSeg seg tc)

-- Push down operations

-- | Push down the segment with the new value.
_pushTMSub :: (ReduceMonad r s m) => TASeg -> Tree -> m ()
_pushTMSub seg sub = do
  (TrCur p crumbs) <- getTMCursor
  putTMCursor $ TrCur sub ((seg, p) : crumbs)

-- Push and pop operations

{- | Run the action in the sub tree.

The sub tree must exist.
-}
inSubTM :: (ReduceMonad r s m) => TASeg -> m a -> m a
inSubTM seg f = do
  ok <- descendTMSeg seg
  unless ok $ do
    t <- getTMTree
    throwFatal $ printf "descend to %s failed, cur tree: %s" (show seg) (treeToRepString t)
  r <- f
  propUpTM
  return r

-- | discard the current focus, pop up and put the original focus in the crumbs back.
_discardTMAndPop :: (ReduceMonad r s m) => m ()
_discardTMAndPop = do
  tc <- getTMCursor
  let
    crumbs = tcCrumbs tc
    headC = head crumbs
  putTMCursor (TrCur (snd headC) (tail crumbs))

-- Remote operations

goTMAbsAddr :: (ReduceMonad r s m) => TreeAddr -> m Bool
goTMAbsAddr addr = do
  when (headSeg addr /= Just RootTASeg) $
    throwFatal (printf "the addr %s should start with the root segment" (show addr))
  propUpTMUntilSeg RootTASeg
  let dstWoRoot = fromJust $ tailTreeAddr addr
  rM <- goDownTCAddr dstWoRoot <$> getTMCursor
  maybe (return False) (\r -> putTMCursor r >> return True) rM

goTMAbsAddrMust :: (ReduceMonad r s m) => TreeAddr -> m ()
goTMAbsAddrMust addr = do
  origAddr <- getTMAbsAddr
  ok <- goTMAbsAddr addr
  unless ok $ throwFatal $ printf "cannot go to addr (%s) tree from %s" (show addr) (show origAddr)

-- | TODO: some functions do not require going back to the original address.
inRemoteTM :: (ReduceMonad r s m) => TreeAddr -> m a -> m a
inRemoteTM addr f = do
  origAddr <- getTMAbsAddr
  goTMAbsAddrMust addr
  r <- f
  goTMAbsAddrMust origAddr
  return r

inTempTM :: (ReduceMonad r s m) => Tree -> m a -> m a
inTempTM tmpT f = do
  modifyTMTree (\t -> t{tmpSub = Just tmpT})
  res <- inSubTM TempTASeg f
  modifyTMTree (\t -> t{tmpSub = Nothing})
  addr <- getTMAbsAddr
  let tmpAddr = appendSeg addr TempTASeg
  delTMDependentPrefix tmpAddr
  return res

-- Mutable operations

-- Locate the immediate parent mutable of a reference.
locateImMutableTM :: (ReduceMonad r s m) => m ()
locateImMutableTM = do
  addr <- getTMAbsAddr
  when (isLastSegMutableArg addr) $ do
    propUpTM
    locateImMutableTM
 where
  -- Check if the last segment is a mutable argument segment.
  isLastSegMutableArg addr
    | Just (MutArgTASeg _) <- lastSeg addr = True
    | otherwise = False

-- Ref Cycle

getIsReducingRC :: (ReduceMonad r s m) => m Bool
getIsReducingRC = rcdIsReducingRCs <$> getRMContext

setIsReducingRC :: (ReduceMonad r s m) => Bool -> m ()
setIsReducingRC b = do
  modifyRMContext $ \ctx -> ctx{rcdIsReducingRCs = b}

-- Tree depth check

treeDepthCheck :: (ResolveMonad r s m) => TrCur -> m ()
treeDepthCheck tc = do
  let
    crumbs = tcCrumbs tc
    depth = length crumbs
  Config{stMaxTreeDepth = maxDepth} <- asks getConfig
  let maxDepthVal = if maxDepth <= 0 then 1000 else maxDepth
  when (depth > maxDepthVal) $ throwFatal $ printf "tree depth exceeds max depth (%d)" maxDepthVal

unlessFocusBottom :: (ReduceMonad r s m) => a -> m a -> m a
unlessFocusBottom a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    _ -> f

withResolveMonad :: (ReduceMonad r s m) => (forall n. (ResolveMonad r s n) => TrCur -> n (TrCur, a)) -> m a
withResolveMonad f = do
  tc <- getTMCursor
  (r, a) <- f tc
  putTMCursor r
  return a

whenTraceEnabled :: (ResolveMonad r s m) => String -> m a -> m a -> m a
whenTraceEnabled name f traced = do
  Config{stTraceExec = traceExec, stTraceFilter = tFilter} <-
    asks getConfig
  if traceExec && (Set.null tFilter || Set.member name tFilter)
    then traced
    else f

spanTreeMsgs :: (ResolveMonad r s m) => Bool -> Tree -> m Value
spanTreeMsgs isTreeRoot t = do
  Config{stTracePrintTree = tracePrintTree} <- asks getConfig
  return $
    if not tracePrintTree
      then ""
      else
        let rep = buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = isTreeRoot})
         in toJSON rep

debugSpanTM :: (ReduceMonad r s m, ToJSON a) => String -> m a -> m a
debugSpanTM name = traceActionTM name Nothing toJSON

debugSpanArgsTM :: (ReduceMonad r s m, ToJSON a) => String -> String -> m a -> m a
debugSpanArgsTM name args = traceActionTM name (Just args) toJSON

debugSpanAdaptTM :: (ReduceMonad r s m) => String -> (a -> Value) -> m a -> m a
debugSpanAdaptTM name = traceActionTM name Nothing

debugSpanArgsAdaptTM :: (ReduceMonad r s m) => String -> String -> (a -> Value) -> m a -> m a
debugSpanArgsAdaptTM name args = traceActionTM name (Just args)

traceActionTM :: (ReduceMonad r s m) => String -> Maybe String -> (a -> Value) -> m a -> m a
traceActionTM name argsM jsonfy f = whenTraceEnabled name f $ withAddrAndFocus $ \addr _ -> do
  let isRoot = addr == rootTreeAddr
  bTraced <- getTMTree >>= spanTreeMsgs isRoot
  debugSpan True name (show addr) (toJSON <$> argsM) bTraced jsonfy $ do
    res <- f
    traced <- getTMTree >>= spanTreeMsgs isRoot
    return (res, traced)

debugInstantTM :: (ReduceMonad r s m) => String -> String -> m ()
debugInstantTM name args = whenTraceEnabled name (return ()) $
  withAddrAndFocus $
    \addr _ -> debugInstant True name (show addr) (Just $ toJSON args)

debugSpanSimpleRM :: (ResolveMonad r s m) => String -> TrCur -> m a -> m a
debugSpanSimpleRM name = traceActionRM name Nothing (const Nothing) (const (toJSON ()))

debugSpanArgsSimpleRM :: (ResolveMonad r s m) => String -> String -> TrCur -> m a -> m a
debugSpanArgsSimpleRM name args = traceActionRM name (Just args) (const Nothing) (const (toJSON ()))

debugSpanTreeRM :: (ResolveMonad r s m) => String -> TrCur -> m Tree -> m Tree
debugSpanTreeRM name =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name Nothing Just (const (toJSON ()))

debugSpanMTreeRM :: (ResolveMonad r s m) => String -> TrCur -> m (Maybe Tree) -> m (Maybe Tree)
debugSpanMTreeRM name =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name Nothing id (const (toJSON ()))

debugSpanTreeArgsRM :: (ResolveMonad r s m) => String -> String -> TrCur -> m Tree -> m Tree
debugSpanTreeArgsRM name args =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name (Just args) Just (const (toJSON ()))

debugSpanMTreeArgsRM :: (ResolveMonad r s m) => String -> String -> TrCur -> m (Maybe Tree) -> m (Maybe Tree)
debugSpanMTreeArgsRM name args =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name (Just args) id (const (toJSON ()))

debugSpanAdaptRM :: (ResolveMonad r s m) => String -> (a -> Maybe Tree) -> (a -> Value) -> TrCur -> m a -> m a
debugSpanAdaptRM name = traceActionRM name Nothing

debugSpanArgsAdaptRM ::
  (ResolveMonad r s m) => String -> String -> (a -> Maybe Tree) -> (a -> Value) -> TrCur -> m a -> m a
debugSpanArgsAdaptRM name args = traceActionRM name (Just args)

traceActionRM ::
  (ResolveMonad r s m) => String -> Maybe String -> (a -> Maybe Tree) -> (a -> Value) -> TrCur -> m a -> m a
traceActionRM name argsM fetchTree conv tc action = whenTraceEnabled name action $ do
  let
    addr = tcAddr tc
    bfocus = tcFocus tc
    isRoot = addr == rootTreeAddr

  bTraced <- spanTreeMsgs isRoot bfocus
  debugSpan True name (show addr) (toJSON <$> argsM) bTraced conv $ do
    res <- action
    traced <- maybe (return "") (spanTreeMsgs isRoot) (fetchTree res)
    return (res, traced)

debugInstantRM :: (ResolveMonad r s m) => String -> String -> TrCur -> m ()
debugInstantRM name args tc = whenTraceEnabled name (return ()) $ do
  let addr = tcAddr tc
  debugInstant True name (show addr) (Just $ toJSON args)

debugInstantOpRM :: (ResolveMonad r s m) => String -> String -> TreeAddr -> m ()
debugInstantOpRM name args addr = whenTraceEnabled name (return ()) $ do
  debugInstant True name (show addr) (Just $ toJSON args)

{- | Visit every node in the tree in pre-order and apply the function.

It does not re-constrain struct fields.
-}
preVisitTree ::
  (ResolveMonad r s m) =>
  (TrCur -> [SubNodeSeg]) ->
  ((TrCur, a) -> m (TrCur, a)) ->
  (TrCur, a) ->
  m (TrCur, a)
preVisitTree subs f x = do
  y <- f x
  foldM
    ( \acc subSeg -> do
        (seg, pre, post) <- case subSeg of
          SubNodeSegNormal seg -> return (seg, return, return)
          -- subTC <- modifyError FatalErr (goDownTCSegMust seg (fst acc))
          -- z <- preVisitTree subs f (subTC, snd acc)
          -- nextTC <- modifyError FatalErr (propUpTC (fst z))
          -- return (nextTC, snd z)
          SubNodeSegEmbed seg -> do
            let origSeg = fromJust $ tcFocusSeg (fst acc)
            return (seg, propUpTC, goDownTCSegMust origSeg)
        -- subTC <- modifyError FatalErr (propUpTC (fst acc) >>= goDownTCSegMust seg)
        -- z <- preVisitTree subs f (subTC, snd acc)
        -- nextTC <- modifyError FatalErr (propUpTC (fst z) >>= goDownTCSegMust origSeg)
        -- return (nextTC, snd z)
        subTC <- modifyError FatalErr (pre (fst acc) >>= goDownTCSegMust seg)
        z <- preVisitTree subs f (subTC, snd acc)
        nextTC <- modifyError FatalErr (propUpTC (fst z) >>= post)
        return (nextTC, snd z)
    )
    y
    (subs $ fst y)

-- | A simple version of the preVisitTree function that does not return a custom value.
preVisitTreeSimple ::
  (ResolveMonad r s m) =>
  (TrCur -> [SubNodeSeg]) ->
  (TrCur -> m TrCur) ->
  TrCur ->
  m TrCur
preVisitTreeSimple subs f tc = do
  (r, _) <-
    preVisitTree
      subs
      ( \(x, _) -> do
          r <- f x
          return (r, ())
      )
      (tc, ())
  return r

{- | Visit every node in the tree in post-order and apply the function.

It does not re-constrain struct fields.
-}
postVisitTree ::
  (ResolveMonad r s m) =>
  (TrCur -> [SubNodeSeg]) ->
  ((TrCur, a) -> m (TrCur, a)) ->
  (TrCur, a) ->
  m (TrCur, a)
postVisitTree subs f x = do
  y <-
    foldM
      ( \acc subSeg -> do
          (seg, pre, post) <- case subSeg of
            SubNodeSegNormal seg -> return (seg, return, return)
            SubNodeSegEmbed seg -> do
              let origSeg = fromJust $ tcFocusSeg (fst acc)
              return (seg, propUpTC, goDownTCSegMust origSeg)

          subTC <- modifyError FatalErr (pre (fst acc) >>= goDownTCSegMust seg)
          z <- postVisitTree subs f (subTC, snd acc)
          nextTC <- modifyError FatalErr (propUpTC (fst z) >>= post)
          return (nextTC, snd z)
      )
      x
      (subs $ fst x)
  f y

postVisitTreeSimple ::
  (ResolveMonad r s m) =>
  (TrCur -> [SubNodeSeg]) ->
  (TrCur -> m TrCur) ->
  TrCur ->
  m TrCur
postVisitTreeSimple subs f tc = do
  (r, _) <-
    postVisitTree
      subs
      ( \(x, _) -> do
          r <- f x
          return (r, ())
      )
      (tc, ())
  return r