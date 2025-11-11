{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RMonad where

import qualified AST
import Control.DeepSeq (NFData)
import Control.Monad (foldM, unless, when)
import Control.Monad.Except (ExceptT, MonadError, modifyError, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader, asks)
import Control.Monad.State.Strict (MonadState, get, gets, modify')
import Cursor
import Data.Aeson (ToJSON, Value, toJSON)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import qualified Data.Text as T
import Env (
  CommonState,
  Config (..),
  ErrorEnv,
  HasConfig (..),
  IDStore (..),
  eesObjID,
  eesTrace,
  emptyConfig,
  tIndexer,
 )
import EvalExpr (evalExpr)
import Feature
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import NotifGraph
import StringIndex (HasTextIndexer (..), ShowWithTextIndexer (..), TextIndexer, TextIndexerMonad, emptyTextIndexer)
import Text.Printf (printf)
import Util (HasTrace (..), Trace, TraceM, debugInstant, emptyTrace, traceSpan)
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
  , recalcRootQ :: [GrpAddr]
  , ctxNotifGraph :: NotifGraph
  , ctxLetMap :: Map.Map TreeAddr Bool
  , rcdIsReducingRCs :: !Bool
  , ctxTrace :: Trace
  , tIndexer :: TextIndexer
  }
  deriving (Eq, Show, Generic, NFData)

instance HasTrace Context where
  getTrace = ctxTrace
  setTrace ctx t = ctx{ctxTrace = t}

instance IDStore Context where
  getID = ctxObjID
  setID ctx i = ctx{ctxObjID = i}

instance HasTextIndexer Context where
  getTextIndexer = Reduce.RMonad.tIndexer
  setTextIndexer ti ctx = ctx{Reduce.RMonad.tIndexer = ti}

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
    , recalcRootQ = []
    , ctxNotifGraph = emptyNotifGraph
    , ctxLetMap = Map.empty
    , rcdIsReducingRCs = False
    , ctxTrace = emptyTrace
    , tIndexer = emptyTextIndexer
    }

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

type ErrM m = (MonadError Error m)

type TrCurStM s m =
  ( MonadState s m
  , HasTreeCursor s
  )

type TrCurStErrM s m =
  ( MonadState s m
  , HasTreeCursor s
  , ErrM m
  )

type CtxStM s m =
  ( MonadState s m
  , HasContext s
  )

type IDStoreStM s m =
  ( MonadState s m
  , IDStore s
  )

type ConfRM r m =
  ( MonadReader r m
  , HasConfig r
  , HasReduceParams r
  )

-- ResolveMonad is the environment for reducing the tree.
type ResolveMonad r s m =
  ( ErrM m
  , HasCallStack
  , ConfRM r m
  , MonadState s m
  , HasTrace s
  , HasContext s
  , IDStore s
  , TextIndexerMonad s m
  , MonadIO m
  )

-- | ReduceMonad is the environment for reducing the tree with tree cursor stored.
type ReduceMonad r s m =
  ( ResolveMonad r s m
  , HasTreeCursor s
  )

data RTCState = RTCState
  { rtsTC :: !TrCur
  , rtsCtx :: Context
  }
  deriving (Eq, Show, Generic, NFData)

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

instance HasTextIndexer RTCState where
  getTextIndexer = getTextIndexer . rtsCtx
  setTextIndexer ti s = s{rtsCtx = setTextIndexer ti (rtsCtx s)}

mkRTState :: TrCur -> CommonState -> RTCState
mkRTState tc common =
  RTCState
    { rtsTC = tc
    , rtsCtx =
        emptyContext
          { ctxObjID = common.eesObjID
          , ctxTrace = common.eesTrace
          , tIndexer = common.tIndexer
          }
    }

-- Context

{-# INLINE getRMContext #-}
getRMContext :: (CtxStM s m) => m Context
getRMContext = gets getContext

putRMContext :: (CtxStM s m) => Context -> m ()
putRMContext ctx = modify' $ \s -> setContext s ctx

modifyRMContext :: (CtxStM s m) => (Context -> Context) -> m ()
modifyRMContext f = do
  ctx <- getRMContext
  putRMContext (f ctx)

-- ObjID

allocRMObjID :: (IDStoreStM s m) => m Int
allocRMObjID = do
  oid <- getRMObjID
  let newOID = oid + 1
  setRMObjID newOID
  return newOID

getRMObjID :: (IDStoreStM s m) => m Int
getRMObjID = gets getID

setRMObjID :: (IDStoreStM s m) => Int -> m ()
setRMObjID newID = modify' (\s -> setID s newID)

-- Trace

-- getRMTrace :: (TraceStM s m) => m Trace
-- getRMTrace = gets getTrace

-- setRMTrace :: (TraceStM s m) => Trace -> m ()
-- setRMTrace trace = modify' (\s -> setTrace s trace)

{- | Delete the notification receivers that have the specified prefix.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delTMDepPrefix :: (CtxStM s m) => TreeAddr -> m ()
delTMDepPrefix addrPrefix = do
  modifyRMContext $ \ctx -> ctx{ctxNotifGraph = delNGVertexPrefix addrPrefix (ctxNotifGraph ctx)}

-- ctx <- getRMContext
-- gstr <- tshow (ctxNotifGraph ctx)
-- addPStr <- tshow addrPrefix

-- debugInstantOpRM
--   "delTMDepPrefix"
--   ( printf
--       "after deleting dependent prefix %s, notif graph is: %s"
--       (show addPStr)
--       (show gstr)
--   )
--   rootTreeAddr

delMutValRecvs :: (CtxStM s m) => TreeAddr -> m ()
delMutValRecvs = undefined

addRMDanglingLet :: (CtxStM s m) => TreeAddr -> m ()
addRMDanglingLet addr = do
  ctx <- getRMContext
  let
    oldMap = ctxLetMap ctx
    newMap = if addr `Map.member` oldMap then oldMap else Map.insert addr False oldMap
  putRMContext ctx{ctxLetMap = newMap}

getRMDanglingLets :: (CtxStM s m) => m [TreeAddr]
getRMDanglingLets = do
  ctx <- getRMContext
  let letAddrs = Map.toList (ctxLetMap ctx)
  return [addr | (addr, False) <- letAddrs]

markRMLetReferred :: (CtxStM s m) => TreeAddr -> m ()
markRMLetReferred addr = do
  ctx <- getRMContext
  let newMap = Map.insert addr True (ctxLetMap ctx)
  putRMContext ctx{ctxLetMap = newMap}

evalExprRM :: (ResolveMonad r s m) => AST.Expression -> m Tree
evalExprRM e = modifyError FatalErr (evalExpr e)

{-
====== TreeAddr ======
-}

getTMAbsAddr :: (TrCurStM s m) => m TreeAddr
getTMAbsAddr = tcAddr <$> getTMCursor

getTMTASeg :: (TrCurStErrM s m) => m Feature
getTMTASeg = do
  tc <- getTMCursor
  modifyError FatalErr (tcFocusSegMust tc)

-- Cursor

{-# INLINE getTMCursor #-}
getTMCursor :: (TrCurStM s m) => m TrCur
getTMCursor = gets getTreeCursor

putTMCursor :: (TrCurStM s m) => TrCur -> m ()
putTMCursor tc = modify' $ \s -> setTreeCursor s tc

-- Crumbs

getTMCrumbs :: (TrCurStM s m) => m [(Feature, Tree)]
getTMCrumbs = tcCrumbs <$> getTMCursor

-- Tree

{-# INLINE getTMTree #-}
getTMTree :: (TrCurStM s m) => m Tree
getTMTree = tcFocus <$> getTMCursor

putTMTree :: (TrCurStM s m) => Tree -> m ()
putTMTree t = do
  tc <- getTMCursor
  putTMCursor (t `setTCFocus` tc)

modifyTMTree :: (TrCurStM s m) => (Tree -> Tree) -> m ()
modifyTMTree f = do
  t <- getTMTree
  putTMTree (f t)

withTree :: (TrCurStM s m) => (Tree -> m a) -> m a
withTree f = getTMTree >>= f

withAddrAndFocus :: (TrCurStM s m) => (TreeAddr -> Tree -> m a) -> m a
withAddrAndFocus f = do
  addr <- getTMAbsAddr
  withTree (f addr)

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getTMParent :: (TrCurStErrM s m) => m Tree
getTMParent = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwFatal "already at the top"
    (_, t) : _ -> return t

-- TreeNode

withTN :: (TrCurStM s m) => (TreeNode -> m a) -> m a
withTN f = withTree (f . treeNode)

modifyTMTN :: (TrCurStM s m) => TreeNode -> m ()
modifyTMTN tn = do
  t <- getTMTree
  putTMTree $ setTN t tn

modifyTMNodeWithTree :: (TrCurStM s m) => Tree -> m ()
modifyTMNodeWithTree t = modifyTMTN (treeNode t)

-- ReduceMonad operations

-- PropUp operations

-- | Propagate the value up.
propUpTM :: (TrCurStErrM s m) => m ()
propUpTM = do
  tc <- getTMCursor
  modifyError FatalErr (propUpTC tc) >>= putTMCursor

runTMTCAction :: (TrCurStM s m) => (forall n. (Monad n) => TrCur -> n Tree) -> m ()
runTMTCAction f = do
  tc <- getTMCursor
  r <- f tc
  putTMCursor (r `setTCFocus` tc)

-- Propagate the value up until the lowest segment is matched.
propUpTMUntilSeg :: (TrCurStErrM s m) => Feature -> m ()
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

descendTM :: (TrCurStM s m) => TreeAddr -> m Bool
descendTM dst = go (addrToList dst)
 where
  go :: (TrCurStM s m) => [Feature] -> m Bool
  go [] = return True
  go (x : xs) = do
    r <- descendTMSeg x
    if r
      then go xs
      else return False

{- | Descend the tree cursor to the segment.

It closes the sub tree based on the parent tree.
-}
descendTMSeg :: (TrCurStM s m) => Feature -> m Bool
descendTMSeg seg = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCSeg seg tc)

descendTMSegMust :: (TrCurStErrM s m) => Feature -> m ()
descendTMSegMust seg = do
  ok <- descendTMSeg seg
  unless ok $ do
    t <- getTMTree
    throwFatal $ printf "descend to %s failed, cur tree: %s" (show seg) (treeToRepString t)

-- Push down operations

-- | Push down the segment with the new value.
_pushTMSub :: (TrCurStM s m) => Feature -> Tree -> m ()
_pushTMSub seg sub = do
  (TrCur p crumbs) <- getTMCursor
  putTMCursor $ TrCur sub ((seg, p) : crumbs)

-- Push and pop operations

{- | Run the action in the sub tree.

The sub tree must exist.
-}
inSubTM :: (TrCurStErrM s m) => Feature -> m a -> m a
inSubTM seg f = do
  ok <- descendTMSeg seg
  unless ok $ do
    t <- getTMTree
    throwFatal $ printf "descend to %s failed, cur tree: %s" (show seg) (treeToRepString t)
  r <- f
  propUpTM
  return r

-- | discard the current focus, pop up and put the original focus in the crumbs back.
_discardTMAndPop :: (TrCurStM s m) => m ()
_discardTMAndPop = do
  tc <- getTMCursor
  let
    crumbs = tcCrumbs tc
    headC = head crumbs
  putTMCursor (TrCur (snd headC) (tail crumbs))

-- Remote operations

goTMAbsAddr :: (TrCurStErrM s m, TextIndexerMonad s m) => TreeAddr -> m Bool
goTMAbsAddr addr = do
  when (headSeg addr /= Just rootFeature) $ do
    addrStr <- tshow addr
    throwFatal (printf "the addr %s should start with the root segment" (show addrStr))
  propUpTMUntilSeg rootFeature
  let dstWoRoot = fromJust $ tailTreeAddr addr
  rM <- goDownTCAddr dstWoRoot <$> getTMCursor
  maybe (return False) (\r -> putTMCursor r >> return True) rM

goTMAbsAddrMust :: (TrCurStErrM s m, TextIndexerMonad s m) => TreeAddr -> m ()
goTMAbsAddrMust addr = do
  origAddr <- getTMAbsAddr
  ok <- goTMAbsAddr addr
  unless ok $ do
    addrStr <- tshow addr
    origAddrStr <- tshow origAddr
    throwFatal $ printf "cannot go to addr (%s) tree from %s" (show addrStr) (show origAddrStr)

-- | TODO: some functions do not require going back to the original address.
inRemoteTM :: (TrCurStErrM s m, TextIndexerMonad s m) => TreeAddr -> m a -> m a
inRemoteTM addr f = do
  origAddr <- getTMAbsAddr
  goTMAbsAddrMust addr
  r <- f
  goTMAbsAddrMust origAddr
  return r

inTempTM :: (TrCurStErrM s m, CtxStM s m) => Tree -> m a -> m a
inTempTM tmpT f = do
  modifyTMTree (\t -> t{tmpSub = Just tmpT})
  res <- inSubTM tempFeature f
  modifyTMTree (\t -> t{tmpSub = Nothing})
  addr <- getTMAbsAddr
  let tmpAddr = appendSeg addr tempFeature
  delTMDepPrefix tmpAddr
  return res

-- Mutable operations

-- Locate the immediate parent mutable of a reference.
locateImMutableTM :: (TrCurStErrM s m) => m ()
locateImMutableTM = do
  addr <- getTMAbsAddr
  when (isLastSegMutableArg addr) $ do
    propUpTM
    locateImMutableTM
 where
  -- Check if the last segment is a mutable argument segment.
  isLastSegMutableArg addr
    | Just (FeatureType MutArgLabelType) <- lastSeg addr = True
    | otherwise = False

-- Ref Cycle

getIsReducingRC :: (CtxStM s m) => m Bool
getIsReducingRC = rcdIsReducingRCs <$> getRMContext

setIsReducingRC :: (CtxStM s m) => Bool -> m ()
setIsReducingRC b = do
  modifyRMContext $ \ctx -> ctx{rcdIsReducingRCs = b}

-- Q

getRecalcRootQ :: (CtxStM s m) => m [GrpAddr]
getRecalcRootQ = recalcRootQ <$> getRMContext

pushRecalcRootQ :: (CtxStM s m) => GrpAddr -> m ()
pushRecalcRootQ gAddr = do
  -- debugInstantTM
  --   "pushRecalcRootQ"
  --   (printf "pushing gAddr %s to recalcRootQ" (show gAddr))
  modifyRMContext $ \ctx -> ctx{recalcRootQ = gAddr : recalcRootQ ctx}

popRecalcRootQ :: (CtxStM s m) => m (Maybe GrpAddr)
popRecalcRootQ = do
  ctx <- getRMContext
  case recalcRootQ ctx of
    [] -> return Nothing
    (x : xs) -> do
      putRMContext ctx{recalcRootQ = xs}
      return (Just x)

-- Tree depth check

treeDepthCheck :: (ConfRM r m, MonadError Error m) => TrCur -> m ()
treeDepthCheck tc = do
  let
    crumbs = tcCrumbs tc
    depth = length crumbs
  Config{stMaxTreeDepth = maxDepth} <- asks getConfig
  let maxDepthVal = if maxDepth <= 0 then 1000 else maxDepth
  when (depth > maxDepthVal) $ throwFatal $ printf "tree depth exceeds max depth (%d)" maxDepthVal

unlessFocusBottom :: (TrCurStM s m) => a -> m a -> m a
unlessFocusBottom a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    _ -> f

withResolveMonad :: (TrCurStM s m) => (forall n. (Monad n) => TrCur -> n (TrCur, a)) -> m a
withResolveMonad f = do
  tc <- getTMCursor
  (r, a) <- f tc
  putTMCursor r
  return a

whenTraceEnabled :: (ConfRM r m) => String -> m a -> m a -> m a
whenTraceEnabled name f traced = do
  Config{stTraceEnable = traceEnable, stTraceFilter = tFilter} <-
    asks getConfig
  if traceEnable && (Set.null tFilter || Set.member name tFilter)
    then traced
    else f

spanTreeMsgs :: (ConfRM r m) => Bool -> Tree -> m Value
spanTreeMsgs isTreeRoot t = do
  Config{stTracePrintTree = tracePrintTree} <- asks getConfig
  return $
    if not tracePrintTree
      then ""
      else
        let rep = buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = isTreeRoot})
         in toJSON rep

type TraceConfM r s m =
  ( TraceM s m
  , TextIndexerMonad s m
  , ConfRM r m
  )

traceSpanTM :: (TraceConfM r s m, HasTreeCursor s, ToJSON a) => String -> m a -> m a
traceSpanTM name = traceActionTM name Nothing (return . toJSON)

traceSpanArgsTM :: (TraceConfM r s m, HasTreeCursor s, ToJSON a) => String -> String -> m a -> m a
traceSpanArgsTM name args = traceActionTM name (Just args) (return . toJSON)

traceSpanAdaptTM :: (TraceConfM r s m, HasTreeCursor s) => String -> (a -> m Value) -> m a -> m a
traceSpanAdaptTM name = traceActionTM name Nothing

traceSpanArgsAdaptTM :: (TraceConfM r s m, HasTreeCursor s) => String -> String -> (a -> m Value) -> m a -> m a
traceSpanArgsAdaptTM name args = traceActionTM name (Just args)

traceActionTM :: (TraceConfM r s m, HasTreeCursor s) => String -> Maybe String -> (a -> m Value) -> m a -> m a
traceActionTM name argsM jsonfy f = whenTraceEnabled name f $ withAddrAndFocus $ \addr _ -> do
  let isRoot = addr == rootTreeAddr
  bTraced <- getTMTree >>= spanTreeMsgs isRoot
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . getConfig)
  traceSpan (True, extraInfo) (T.pack name) addrS (toJSON <$> argsM) bTraced jsonfy $ do
    res <- f
    traced <- getTMTree >>= spanTreeMsgs isRoot
    return (res, traced)

debugInstantTM :: (TraceConfM r s m, HasTreeCursor s) => String -> String -> m ()
debugInstantTM name args = whenTraceEnabled name (return ()) $
  withAddrAndFocus $
    \addr _ -> do
      addrS <- tshow addr
      extraInfo <- asks (stTraceExtraInfo . getConfig)
      debugInstant (True, extraInfo) (T.pack name) addrS (Just $ toJSON args)

onelinerTree :: (TextIndexerMonad s m) => Tree -> m Value
onelinerTree t = do
  r <- oneLinerStringOfTree t
  return $ toJSON r

traceSpanSimpleRM :: (TraceConfM r s m) => String -> TrCur -> m a -> m a
traceSpanSimpleRM name = traceActionRM name Nothing (const Nothing) (const (return $ toJSON ()))

traceSpanArgsSimpleRM :: (TraceConfM r s m) => String -> String -> TrCur -> m a -> m a
traceSpanArgsSimpleRM name args = traceActionRM name (Just args) (const Nothing) (const (return $ toJSON ()))

traceSpanTreeRM :: (TraceConfM r s m) => String -> TrCur -> m Tree -> m Tree
traceSpanTreeRM name =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name Nothing Just onelinerTree

traceSpanMTreeRM :: (TraceConfM r s m) => String -> TrCur -> m (Maybe Tree) -> m (Maybe Tree)
traceSpanMTreeRM name =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name Nothing id (const (return $ toJSON ()))

traceSpanTreeArgsRM :: (TraceConfM r s m) => String -> String -> TrCur -> m Tree -> m Tree
traceSpanTreeArgsRM name args =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name (Just args) Just onelinerTree

traceSpanMTreeArgsRM :: (TraceConfM r s m) => String -> String -> TrCur -> m (Maybe Tree) -> m (Maybe Tree)
traceSpanMTreeArgsRM name args =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name (Just args) id (const (return $ toJSON ()))

traceSpanAdaptRM :: (TraceConfM r s m) => String -> (a -> Maybe Tree) -> (a -> m Value) -> TrCur -> m a -> m a
traceSpanAdaptRM name = traceActionRM name Nothing

traceSpanArgsAdaptRM ::
  (TraceConfM r s m) => String -> String -> (a -> Maybe Tree) -> (a -> m Value) -> TrCur -> m a -> m a
traceSpanArgsAdaptRM name args = traceActionRM name (Just args)

traceActionRM ::
  (TraceConfM r s m) => String -> Maybe String -> (a -> Maybe Tree) -> (a -> m Value) -> TrCur -> m a -> m a
traceActionRM name argsM fetchTree resFetch tc action = whenTraceEnabled name action $ do
  let
    addr = tcAddr tc
    bfocus = tcFocus tc
    isRoot = addr == rootTreeAddr

  bTraced <- spanTreeMsgs isRoot bfocus
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . getConfig)
  traceSpan (True, extraInfo) (T.pack name) addrS (toJSON <$> argsM) bTraced resFetch $ do
    res <- action
    traced <- maybe (return "") (spanTreeMsgs isRoot) (fetchTree res)
    return (res, traced)

debugInstantRM :: (TraceConfM r s m) => String -> String -> TrCur -> m ()
debugInstantRM name args tc = whenTraceEnabled name (return ()) $ do
  let addr = tcAddr tc
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . getConfig)
  debugInstant (True, extraInfo) (T.pack name) addrS (Just $ toJSON args)

debugInstantOpRM :: (TraceConfM r s m) => String -> String -> TreeAddr -> m ()
debugInstantOpRM name args addr = whenTraceEnabled name (return ()) $ do
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . getConfig)
  debugInstant (True, extraInfo) (T.pack name) addrS (Just $ toJSON args)

emptySpanValue :: (ConfRM r m) => a -> m Value
emptySpanValue _ = return $ toJSON ()

{- | Visit every node in the tree in pre-order and apply the function.

It does not re-constrain struct fields.
-}
preVisitTree ::
  (ErrM m) =>
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
          SubNodeSegEmbed seg -> do
            let origSeg = fromJust $ tcFocusSeg (fst acc)
            return (seg, propUpTC, goDownTCSegMust origSeg)
        subTC <- modifyError FatalErr (pre (fst acc) >>= goDownTCSegMust seg)
        z <- preVisitTree subs f (subTC, snd acc)
        nextTC <- modifyError FatalErr (propUpTC (fst z) >>= post)
        return (nextTC, snd z)
    )
    y
    (subs $ fst y)

-- | A simple version of the preVisitTree function that does not return a custom value.
preVisitTreeSimple ::
  (ErrM m) =>
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
  (ErrM m) =>
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
  (ErrM m) =>
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