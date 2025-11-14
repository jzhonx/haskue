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

import Control.DeepSeq (NFData)
import Control.Monad (foldM, unless, when)
import Control.Monad.Except (ExceptT (..), MonadError, modifyError, throwError)
import Control.Monad.RWS.Strict (RWST, lift)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (gets, modify')
import Cursor
import Data.Aeson (ToJSON, Value, toJSON)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import qualified Data.Text as T
import Env (
  CommonState,
  Config (..),
  eesObjID,
  eesTrace,
  emptyConfig,
  tIndexer,
 )
import Feature
import GHC.Generics (Generic)
import GHC.Stack (callStack, prettyCallStack)
import NotifGraph
import StringIndex (HasTextIndexer (..), ShowWithTextIndexer (..), TextIndexer, emptyTextIndexer)
import Text.Printf (printf)
import Util (HasTrace (..), Trace, debugInstant, emptyTrace, traceSpan)
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

type RM = RWST ReduceConfig () RTCState (ExceptT Error IO)

-- class HasReduceParams s where
--   getReduceParams :: s -> ReduceParams
--   setReduceParams :: s -> ReduceParams -> s
--   modifyReduceParams :: (ReduceParams -> ReduceParams) -> s -> s

data ReduceConfig = ReduceConfig
  { baseConfig :: Config
  , params :: ReduceParams
  }
  deriving (Show)

-- instance HasConfig ReduceConfig where
--   getConfig = baseConfig
--   setConfig r c = r{baseConfig = c}
--   modifyConfig f r = r{baseConfig = f (baseConfig r)}

-- instance HasReduceParams ReduceConfig where
--   getReduceParams = params
--   setReduceParams r p = r{params = p}
--   modifyReduceParams f r = r{params = f (params r)}

mapParams :: (ReduceParams -> ReduceParams) -> ReduceConfig -> ReduceConfig
mapParams f r = r{params = f (params r)}

emptyReduceConfig :: ReduceConfig
emptyReduceConfig =
  ReduceConfig
    { baseConfig = emptyConfig
    , params = emptyReduceParams
    }

-- class HasContext s where
--   getContext :: s -> Context
--   setContext :: s -> Context -> s
--   modifyContext :: s -> (Context -> Context) -> s

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

-- instance IDStore Context where
--   getID = ctxObjID
--   setID ctx i = ctx{ctxObjID = i}

instance HasTextIndexer Context where
  getTextIndexer = Reduce.RMonad.tIndexer
  setTextIndexer ti ctx = ctx{Reduce.RMonad.tIndexer = ti}

-- instance HasContext Context where
--   getContext = id
--   setContext _ = id
--   modifyContext ctx f = f ctx

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

liftEitherRM :: Either String a -> RM a
liftEitherRM e = lift $ ExceptT $ return $ case e of
  Left msg -> Left $ FatalErr msg
  Right r -> Right r

throwFatal :: String -> RM a
throwFatal msg = throwError $ FatalErr $ msg ++ "\n" ++ prettyCallStack callStack

throwDirty :: (MonadError Error m) => SuffixIrredAddr -> m a
throwDirty siAddr = throwError $ DirtyDep siAddr

-- liftFatal :: (MonadError Error m) => ExceptT String m a -> m a
-- liftFatal = modifyError FatalErr

-- type ErrM m = (MonadError Error m)

-- type TrCurStM s m =
--   ( MonadState s m
--   , HasTreeCursor s
--   )

-- type TrCurStErrM s m =
--   ( MonadState s m
--   , HasTreeCursor s
--   , ErrM m
--   )

-- type CtxStM s m =
--   ( MonadState s m
--   , HasContext s
--   )

-- type IDStoreStM s m =
--   ( MonadState s m
--   , IDStore s
--   )

-- type ConfRM r m =
--   ( MonadReader r m
--   , HasConfig r
--   , HasReduceParams r
--   )

-- -- ResolveMonad is the environment for reducing the tree.
-- type ResolveMonad r s m =
--   ( ErrM m
--   , HasCallStack
--   , ConfRM r m
--   , MonadState s m
--   , HasTrace s
--   , HasContext s
--   , IDStore s
--   , TextIndexerMonad s m
--   , MonadIO m
--   )

-- -- | ReduceMonad is the environment for reducing the tree with tree cursor stored.
-- type ReduceMonad r s m =
--   ( ResolveMonad r s m
--   , HasTreeCursor s
--   )

data RTCState = RTCState
  { rtsTC :: !TrCur
  , rtsCtx :: Context
  }
  deriving (Eq, Show, Generic, NFData)

mapTC :: (TrCur -> TrCur) -> RTCState -> RTCState
mapTC f s = s{rtsTC = f (rtsTC s)}

mapCtx :: (Context -> Context) -> RTCState -> RTCState
mapCtx f s = s{rtsCtx = f (rtsCtx s)}

-- instance HasTreeCursor RTCState where
--   getTreeCursor = rtsTC
--   setTreeCursor s tc = s{rtsTC = tc}

-- instance HasContext RTCState where
--   getContext = rtsCtx
--   setContext s ctx = s{rtsCtx = ctx}
--   modifyContext s f = s{rtsCtx = f (rtsCtx s)}

instance HasTrace RTCState where
  getTrace = ctxTrace . rtsCtx
  setTrace s trace = s{rtsCtx = setTrace (rtsCtx s) trace}

-- instance IDStore RTCState where
--   getID = getID . rtsCtx
--   setID s newID = s{rtsCtx = setID (rtsCtx s) newID}

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
getRMContext :: RM Context
getRMContext = gets rtsCtx

putRMContext :: Context -> RM ()
putRMContext ctx = modify' $ \s -> s{rtsCtx = ctx}

modifyRMContext :: (Context -> Context) -> RM ()
modifyRMContext f = modify' $ \s -> s{rtsCtx = f (rtsCtx s)}

-- ObjID

allocRMObjID :: RM Int
allocRMObjID = do
  oid <- getRMObjID
  let newOID = oid + 1
  setRMObjID newOID
  return newOID

getRMObjID :: RM Int
getRMObjID = gets (ctxObjID . rtsCtx)

setRMObjID :: Int -> RM ()
setRMObjID newID = modify' $ mapCtx $ \ctx -> ctx{ctxObjID = newID}

{- | Delete the notification receivers that have the specified prefix.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delTMDepPrefix :: TreeAddr -> RM ()
delTMDepPrefix addrPrefix =
  modifyRMContext $ \ctx -> ctx{ctxNotifGraph = delNGVertexPrefix addrPrefix (ctxNotifGraph ctx)}

delMutValRecvs :: TreeAddr -> RM ()
delMutValRecvs = undefined

addRMDanglingLet :: TreeAddr -> RM ()
addRMDanglingLet addr = modifyRMContext $ \ctx ->
  let
    oldMap = ctxLetMap ctx
    newMap = if addr `Map.member` oldMap then oldMap else Map.insert addr False oldMap
   in
    ctx{ctxLetMap = newMap}

getRMDanglingLets :: RM [TreeAddr]
getRMDanglingLets = do
  ctx <- getRMContext
  let letAddrs = Map.toList (ctxLetMap ctx)
  return [addr | (addr, False) <- letAddrs]

markRMLetReferred :: TreeAddr -> RM ()
markRMLetReferred addr = modifyRMContext $ \ctx ->
  let newMap = Map.insert addr True (ctxLetMap ctx)
   in ctx{ctxLetMap = newMap}

-- evalExprRM :: (ResolveMonad r s m) => AST.Expression -> m Tree
-- evalExprRM e = modifyError FatalErr (evalExpr e)

-- Cursor

{-# INLINE getTMCursor #-}
getTMCursor :: RM TrCur
getTMCursor = gets rtsTC

modifyTMCursor :: (TrCur -> TrCur) -> RM ()
modifyTMCursor f = modify' $ \s -> s{rtsTC = f (rtsTC s)}

putTMCursor :: TrCur -> RM ()
putTMCursor tc = modifyTMCursor $ const tc

{-
====== TreeAddr ======
-}

getTMAbsAddr :: RM TreeAddr
getTMAbsAddr = tcAddr <$> getTMCursor

getTMTASeg :: RM Feature
getTMTASeg = do
  tc <- getTMCursor
  modifyError FatalErr (tcFocusSegMust tc)

-- Crumbs

getTMCrumbs :: RM [(Feature, Tree)]
getTMCrumbs = tcCrumbs <$> getTMCursor

-- Tree

{-# INLINE getTMTree #-}
getTMTree :: RM Tree
getTMTree = tcFocus <$> getTMCursor

modifyTMTree :: (Tree -> Tree) -> RM ()
modifyTMTree f = modifyTMCursor $ \tc -> f (tcFocus tc) `setTCFocus` tc

putTMTree :: Tree -> RM ()
putTMTree t = modifyTMTree $ const t

withTree :: (Tree -> RM a) -> RM a
withTree f = getTMTree >>= f

withAddrAndFocus :: (TreeAddr -> Tree -> RM a) -> RM a
withAddrAndFocus f = do
  addr <- getTMAbsAddr
  withTree (f addr)

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getTMParent :: RM Tree
getTMParent = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwFatal "already at the top"
    (_, t) : _ -> return t

-- TreeNode

withTN :: (TreeNode -> RM a) -> RM a
withTN f = withTree (f . treeNode)

modifyTMTN :: TreeNode -> RM ()
modifyTMTN tn = modifyTMTree $ \t -> setTN t tn

modifyTMNodeWithTree :: Tree -> RM ()
modifyTMNodeWithTree t = modifyTMTN (treeNode t)

-- ReduceMonad operations

-- PropUp operations

-- | Propagate the value up.
propUpTM :: RM ()
propUpTM = do
  tc <- getTMCursor
  liftEitherRM (propUpTC tc) >>= putTMCursor

runTMTCAction :: (forall n. (Monad n) => TrCur -> n Tree) -> RM ()
runTMTCAction f = do
  tc <- getTMCursor
  r <- f tc
  putTMCursor (r `setTCFocus` tc)

-- Propagate the value up until the lowest segment is matched.
propUpTMUntilSeg :: Feature -> RM ()
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

descendTM :: TreeAddr -> RM Bool
descendTM dst = go (addrToList dst)
 where
  go :: [Feature] -> RM Bool
  go [] = return True
  go (x : xs) = do
    r <- descendTMSeg x
    if r
      then go xs
      else return False

{- | Descend the tree cursor to the segment.

It closes the sub tree based on the parent tree.
-}
descendTMSeg :: Feature -> RM Bool
descendTMSeg seg = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCSeg seg tc)

descendTMSegMust :: Feature -> RM ()
descendTMSegMust seg = do
  ok <- descendTMSeg seg
  unless ok $ do
    t <- getTMTree
    throwFatal $ printf "descend to %s failed, cur tree: %s" (show seg) (treeToRepString t)

-- Push down operations

-- | Push down the segment with the new value.
_pushTMSub :: Feature -> Tree -> RM ()
_pushTMSub seg sub = do
  (TrCur p crumbs) <- getTMCursor
  putTMCursor $ TrCur sub ((seg, p) : crumbs)

-- Push and pop operations

{- | Run the action in the sub tree.

The sub tree must exist.
-}
inSubTM :: Feature -> RM a -> RM a
inSubTM seg f = do
  ok <- descendTMSeg seg
  unless ok $ do
    t <- getTMTree
    throwFatal $ printf "descend to %s failed, cur tree: %s" (show seg) (treeToRepString t)
  r <- f
  propUpTM
  return r

-- | discard the current focus, pop up and put the original focus in the crumbs back.
_discardTMAndPop :: RM ()
_discardTMAndPop = do
  tc <- getTMCursor
  let
    crumbs = tcCrumbs tc
    headC = head crumbs
  putTMCursor (TrCur (snd headC) (tail crumbs))

-- Remote operations

goTMAbsAddr :: TreeAddr -> RM Bool
goTMAbsAddr addr = do
  when (headSeg addr /= Just rootFeature) $ do
    addrStr <- tshow addr
    throwFatal (printf "the addr %s should start with the root segment" (show addrStr))
  propUpTMUntilSeg rootFeature
  let dstWoRoot = fromJust $ tailTreeAddr addr
  rM <- goDownTCAddr dstWoRoot <$> getTMCursor
  maybe (return False) (\r -> putTMCursor r >> return True) rM

goTMAbsAddrMust :: TreeAddr -> RM ()
goTMAbsAddrMust addr = do
  origAddr <- getTMAbsAddr
  ok <- goTMAbsAddr addr
  unless ok $ do
    addrStr <- tshow addr
    origAddrStr <- tshow origAddr
    throwFatal $ printf "cannot go to addr (%s) tree from %s" (show addrStr) (show origAddrStr)

-- | TODO: some functions do not require going back to the original address.
inRemoteTM :: TreeAddr -> RM a -> RM a
inRemoteTM addr f = do
  origAddr <- getTMAbsAddr
  goTMAbsAddrMust addr
  r <- f
  goTMAbsAddrMust origAddr
  return r

inTempTM :: Tree -> RM a -> RM a
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
locateImMutableTM :: RM ()
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

getIsReducingRC :: RM Bool
getIsReducingRC = rcdIsReducingRCs <$> getRMContext

setIsReducingRC :: Bool -> RM ()
setIsReducingRC b = do
  modifyRMContext $ \ctx -> ctx{rcdIsReducingRCs = b}

-- Q

getRecalcRootQ :: RM [GrpAddr]
getRecalcRootQ = recalcRootQ <$> getRMContext

pushRecalcRootQ :: GrpAddr -> RM ()
pushRecalcRootQ gAddr =
  modifyRMContext $ \ctx -> ctx{recalcRootQ = gAddr : recalcRootQ ctx}

popRecalcRootQ :: RM (Maybe GrpAddr)
popRecalcRootQ = do
  ctx <- getRMContext
  case recalcRootQ ctx of
    [] -> return Nothing
    (x : xs) -> do
      putRMContext ctx{recalcRootQ = xs}
      return (Just x)

-- Tree depth check

treeDepthCheck :: TrCur -> RM ()
treeDepthCheck tc = do
  let
    crumbs = tcCrumbs tc
    depth = length crumbs
  Config{stMaxTreeDepth = maxDepth} <- asks baseConfig
  let maxDepthVal = if maxDepth <= 0 then 1000 else maxDepth
  when (depth > maxDepthVal) $ throwFatal $ printf "tree depth exceeds max depth (%d)" maxDepthVal

unlessFocusBottom :: a -> RM a -> RM a
unlessFocusBottom a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    _ -> f

-- withResolveMonad :: (forall n. (Monad n) => TrCur -> n (TrCur, a)) -> m a
-- withResolveMonad f = do
--   tc <- getTMCursor
--   (r, a) <- f tc
--   putTMCursor r
--   return a

whenTraceEnabled :: String -> RM a -> RM a -> RM a
whenTraceEnabled name f traced = do
  Config{stTraceEnable = traceEnable, stTraceFilter = tFilter} <-
    asks baseConfig
  if traceEnable && (Set.null tFilter || Set.member name tFilter)
    then traced
    else f

spanTreeMsgs :: Bool -> Tree -> RM Value
spanTreeMsgs isTreeRoot t = do
  Config{stTracePrintTree = tracePrintTree} <- asks baseConfig
  return $
    if not tracePrintTree
      then ""
      else
        let rep = buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = isTreeRoot})
         in toJSON rep

-- type TraceConfM r s m =
--   ( TraceM s m
--   , TextIndexerMonad s m
--   , ConfRM r m
--   )

traceSpanTM :: (ToJSON a) => String -> RM a -> RM a
traceSpanTM name = traceActionTM name Nothing (return . toJSON)

traceSpanArgsTM :: (ToJSON a) => String -> String -> RM a -> RM a
traceSpanArgsTM name args = traceActionTM name (Just args) (return . toJSON)

traceSpanAdaptTM :: String -> (a -> RM Value) -> RM a -> RM a
traceSpanAdaptTM name = traceActionTM name Nothing

traceSpanArgsAdaptTM :: String -> String -> (a -> RM Value) -> RM a -> RM a
traceSpanArgsAdaptTM name args = traceActionTM name (Just args)

traceActionTM :: String -> Maybe String -> (a -> RM Value) -> RM a -> RM a
traceActionTM name argsM jsonfy f = whenTraceEnabled name f $ withAddrAndFocus $ \addr _ -> do
  let isRoot = addr == rootTreeAddr
  bTraced <- getTMTree >>= spanTreeMsgs isRoot
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  traceSpan (True, extraInfo) (T.pack name) addrS (toJSON <$> argsM) bTraced jsonfy $ do
    res <- f
    traced <- getTMTree >>= spanTreeMsgs isRoot
    return (res, traced)

debugInstantTM :: String -> String -> RM ()
debugInstantTM name args = whenTraceEnabled name (return ()) $
  withAddrAndFocus $
    \addr _ -> do
      addrS <- tshow addr
      extraInfo <- asks (stTraceExtraInfo . baseConfig)
      debugInstant (True, extraInfo) (T.pack name) addrS (Just $ toJSON args)

onelinerTree :: Tree -> RM Value
onelinerTree t = do
  r <- oneLinerStringOfTree t
  return $ toJSON r

traceSpanSimpleRM :: String -> TrCur -> RM a -> RM a
traceSpanSimpleRM name = traceActionRM name Nothing (const Nothing) (const (return $ toJSON ()))

traceSpanArgsSimpleRM :: String -> String -> TrCur -> RM a -> RM a
traceSpanArgsSimpleRM name args = traceActionRM name (Just args) (const Nothing) (const (return $ toJSON ()))

traceSpanTreeRM :: String -> TrCur -> RM Tree -> RM Tree
traceSpanTreeRM name =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name Nothing Just onelinerTree

traceSpanMTreeRM :: String -> TrCur -> RM (Maybe Tree) -> RM (Maybe Tree)
traceSpanMTreeRM name =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name Nothing id (const (return $ toJSON ()))

traceSpanTreeArgsRM :: String -> String -> TrCur -> RM Tree -> RM Tree
traceSpanTreeArgsRM name args =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name (Just args) Just onelinerTree

traceSpanMTreeArgsRM :: String -> String -> TrCur -> RM (Maybe Tree) -> RM (Maybe Tree)
traceSpanMTreeArgsRM name args =
  -- The result is a tree, so there is no need to adapt the result as the tree will be printed.
  traceActionRM name (Just args) id (const (return $ toJSON ()))

traceSpanAdaptRM :: String -> (a -> Maybe Tree) -> (a -> RM Value) -> TrCur -> RM a -> RM a
traceSpanAdaptRM name = traceActionRM name Nothing

traceSpanArgsAdaptRM ::
  String -> String -> (a -> Maybe Tree) -> (a -> RM Value) -> TrCur -> RM a -> RM a
traceSpanArgsAdaptRM name args = traceActionRM name (Just args)

traceActionRM ::
  String -> Maybe String -> (a -> Maybe Tree) -> (a -> RM Value) -> TrCur -> RM a -> RM a
traceActionRM name argsM fetchTree resFetch tc action = whenTraceEnabled name action $ do
  let
    addr = tcAddr tc
    bfocus = tcFocus tc
    isRoot = addr == rootTreeAddr

  bTraced <- spanTreeMsgs isRoot bfocus
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  traceSpan (True, extraInfo) (T.pack name) addrS (toJSON <$> argsM) bTraced resFetch $ do
    res <- action
    traced <- maybe (return "") (spanTreeMsgs isRoot) (fetchTree res)
    return (res, traced)

debugInstantRM :: String -> String -> TrCur -> RM ()
debugInstantRM name args tc = whenTraceEnabled name (return ()) $ do
  let addr = tcAddr tc
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  debugInstant (True, extraInfo) (T.pack name) addrS (Just $ toJSON args)

debugInstantOpRM :: String -> String -> TreeAddr -> RM ()
debugInstantOpRM name args addr = whenTraceEnabled name (return ()) $ do
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  debugInstant (True, extraInfo) (T.pack name) addrS (Just $ toJSON args)

emptySpanValue :: a -> RM Value
emptySpanValue _ = return $ toJSON ()

{- | Visit every node in the tree in pre-order and apply the function.

It does not re-constrain struct fields.
-}
preVisitTree ::
  (TrCur -> [SubNodeSeg]) ->
  ((TrCur, a) -> RM (TrCur, a)) ->
  (TrCur, a) ->
  RM (TrCur, a)
preVisitTree subs f x = do
  y <- f x
  foldM
    ( \acc subSeg -> do
        (seg, pre, post) <- case subSeg of
          SubNodeSegNormal seg -> return (seg, return, return)
          SubNodeSegEmbed seg -> do
            let origSeg = fromJust $ tcFocusSeg (fst acc)
            return (seg, propUpTC, goDownTCSegMust origSeg)
        subTC <- liftEitherRM (pre (fst acc) >>= goDownTCSegMust seg)
        z <- preVisitTree subs f (subTC, snd acc)
        nextTC <- liftEitherRM (propUpTC (fst z) >>= post)
        return (nextTC, snd z)
    )
    y
    (subs $ fst y)

-- | A simple version of the preVisitTree function that does not return a custom value.
preVisitTreeSimple ::
  (TrCur -> [SubNodeSeg]) ->
  (TrCur -> RM TrCur) ->
  TrCur ->
  RM TrCur
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
  (TrCur -> [SubNodeSeg]) ->
  ((TrCur, a) -> RM (TrCur, a)) ->
  (TrCur, a) ->
  RM (TrCur, a)
postVisitTree subs f x = do
  y <-
    foldM
      ( \acc subSeg -> do
          (seg, pre, post) <- case subSeg of
            SubNodeSegNormal seg -> return (seg, return, return)
            SubNodeSegEmbed seg -> do
              let origSeg = fromJust $ tcFocusSeg (fst acc)
              return (seg, propUpTC, goDownTCSegMust origSeg)

          subTC <- liftEitherRM (pre (fst acc) >>= goDownTCSegMust seg)
          z <- postVisitTree subs f (subTC, snd acc)
          nextTC <- liftEitherRM (propUpTC (fst z) >>= post)
          return (nextTC, snd z)
      )
      x
      (subs $ fst x)
  f y

postVisitTreeSimple ::
  (TrCur -> [SubNodeSeg]) ->
  (TrCur -> RM TrCur) ->
  TrCur ->
  RM TrCur
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