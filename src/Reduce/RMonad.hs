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
import Control.Monad.Except (ExceptT (..), MonadError, throwError)
import Control.Monad.RWS.Strict (RWST, lift)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (gets, modify')
import Cursor
import Data.Aeson (KeyValue (..), ToJSON, Value, toJSON)
import Data.Aeson.Types (object)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import Env (
  Config (..),
  emptyConfig,
 )
import Feature
import GHC.Generics (Generic)
import GHC.Stack (callStack, prettyCallStack)
import GHC.Stack.Types (HasCallStack)
import PropGraph
import StringIndex (HasTextIndexer (..), ShowWTIndexer (..), TextIndexer, ToJSONWTIndexer (ttoJSON), emptyTextIndexer)
import Text.Printf (printf)
import Util (HasTrace (..), Trace, debugInstant, emptyTrace, getTraceID, traceSpanExec, traceSpanStart)
import Value
import Value.Util.TreeRep

data RecalcRCResult
  = -- | During RC recalculation, RsDirty indicates that the value needs to be put into the stack.
    RsDirty
  | RsCyclic
  | RsNormal
  deriving (Eq, Show)

type RecalcRCFetch = SuffixIrredAddr -> RecalcRCResult

data ReduceParams = ReduceParams
  { createCnstr :: Bool
  , fetch :: RecalcRCFetch
  -- ^ Custom fetch function that fetches the tree at the suffix irreducible address.
  }

instance Show ReduceParams where
  show c = "ReduceParams {createCnstr = " ++ show c.createCnstr ++ " }"

emptyReduceParams :: ReduceParams
emptyReduceParams =
  ReduceParams
    { createCnstr = False
    , fetch = const RsNormal
    }

type RM = RWST ReduceConfig () RTCState (ExceptT Error IO)

data ReduceConfig = ReduceConfig
  { baseConfig :: Config
  , params :: ReduceParams
  }
  deriving (Show)

mapParams :: (ReduceParams -> ReduceParams) -> ReduceConfig -> ReduceConfig
mapParams f r = r{params = f (params r)}

emptyReduceConfig :: ReduceConfig
emptyReduceConfig =
  ReduceConfig
    { baseConfig = emptyConfig
    , params = emptyReduceParams
    }

data Context = Context
  { ctxObjID :: !Int
  , ctxReduceStack :: [TreeAddr]
  , isRecalcing :: !Bool
  , recalcRootQ :: Seq.Seq (TreeAddr, GrpAddr)
  -- ^ The recalculation root queue.
  , ctxPropGraph :: PropGraph
  , lastValueMap :: Map.Map SuffixIrredAddr Tree
  , ctxLetMap :: Map.Map TreeAddr Bool
  , rcdIsReducingRCs :: !Bool
  , noRecalc :: !Bool
  -- ^ If true, do not perform recalculation when reducing struct objects.
  , ctxTrace :: Trace
  , tIndexer :: TextIndexer
  }
  deriving (Eq, Show, Generic, NFData)

instance HasTrace Context where
  getTrace = ctxTrace
  setTrace ctx t = ctx{ctxTrace = t}

instance HasTextIndexer Context where
  getTextIndexer = Reduce.RMonad.tIndexer
  setTextIndexer ti ctx = ctx{Reduce.RMonad.tIndexer = ti}

emptyContext :: Context
emptyContext =
  Context
    { ctxObjID = 0
    , ctxReduceStack = []
    , isRecalcing = False
    , recalcRootQ = Seq.empty
    , ctxPropGraph = emptyPropGraph
    , lastValueMap = Map.empty
    , ctxLetMap = Map.empty
    , rcdIsReducingRCs = False
    , noRecalc = False
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

throwFatal :: (HasCallStack) => String -> RM a
throwFatal msg = throwError $ FatalErr $ msg ++ "\n" ++ prettyCallStack callStack

throwDirty :: (MonadError Error m) => SuffixIrredAddr -> m a
throwDirty siAddr = throwError $ DirtyDep siAddr

data RTCState = RTCState
  { rtsTC :: !TrCur
  , rtsCtx :: Context
  }
  deriving (Eq, Show, Generic, NFData)

mapTC :: (TrCur -> TrCur) -> RTCState -> RTCState
mapTC f s = s{rtsTC = f (rtsTC s)}

mapCtx :: (Context -> Context) -> RTCState -> RTCState
mapCtx f s = s{rtsCtx = f (rtsCtx s)}

instance HasTrace RTCState where
  getTrace = ctxTrace . rtsCtx
  setTrace s trace = s{rtsCtx = setTrace (rtsCtx s) trace}

instance HasTextIndexer RTCState where
  getTextIndexer = getTextIndexer . rtsCtx
  setTextIndexer ti s = s{rtsCtx = setTextIndexer ti (rtsCtx s)}

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
  modifyRMContext $ \ctx -> ctx{ctxPropGraph = delNGVertexPrefix addrPrefix (ctxPropGraph ctx)}

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
  liftEitherRM (tcFocusSegMust tc)

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

supersedeTMTN :: TreeNode -> RM ()
supersedeTMTN tn = modifyTMTree (supersedeTN tn)

unwrapTMTN :: (Tree -> TreeNode) -> RM ()
unwrapTMTN f = modifyTMTree (unwrapTN f)

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
    rep <- treeToRepString t
    throwFatal $ printf "descend to %s failed, cur tree: %s" (show seg) rep

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
    rep <- treeToRepString t
    throwFatal $ printf "descend to %s failed, cur tree: %s" (show seg) rep
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

goTMAbsAddrMust :: (HasCallStack) => TreeAddr -> RM ()
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

inTempTM :: String -> Tree -> RM a -> RM a
inTempTM name tmpT f = do
  modifyTMTree (\t -> t{tmpSub = Just tmpT})
  tf <- strToTempFeature name
  res <- inSubTM tf f
  modifyTMTree (\t -> t{tmpSub = Nothing})
  addr <- getTMAbsAddr
  let tmpAddr = appendSeg addr tf
  delTMDepPrefix tmpAddr
  return res

-- SOp operations

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

data RMStartTraceArgs = RMStartTraceArgs
  { cstaTraceID :: !Int
  , cstaAddr :: !T.Text
  , cstaBeforeFocus :: !Value
  , cstaCustomVal :: !Value
  }
  deriving (Eq, Show)

instance ToJSON RMStartTraceArgs where
  toJSON cta =
    object
      [ "traceid" .= show (cstaTraceID cta)
      , "addr" .= cstaAddr cta
      , "bfcs" .= cstaBeforeFocus cta
      , "ctm" .= cstaCustomVal cta
      ]

data RMEndTraceArgs = RMEndTraceArgs
  { cetaResVal :: !Value
  , cetaFocus :: !Value
  }
  deriving (Eq, Show)

instance ToJSON RMEndTraceArgs where
  toJSON cta =
    object
      [ "res" .= cetaResVal cta
      , "fcs" .= cetaFocus cta
      ]

data RMInstantTraceArgs = RMInstantTraceArgs
  { ctiTraceID :: !Int
  , ctiAddr :: !T.Text
  , ctiCustomVal :: !Value
  }
  deriving (Eq, Show)

instance ToJSON RMInstantTraceArgs where
  toJSON c =
    object
      [ "traceid" .= show (ctiTraceID c)
      , "addr" .= ctiAddr c
      , "ctm" .= ctiCustomVal c
      ]

whenTraceEnabled :: String -> RM a -> RM a -> RM a
whenTraceEnabled name f traced = do
  Config{stTraceEnable = traceEnable, stTraceFilter = tFilter} <-
    asks baseConfig
  if traceEnable && (Set.null tFilter || Set.member name tFilter)
    then traced
    else f

spanTreeMsgs :: Bool -> Bool -> Tree -> RM Value
spanTreeMsgs isTreeRoot ignore t = do
  Config{stTracePrintTree = tracePrintTree} <- asks baseConfig
  if not tracePrintTree || ignore
    then return $ object []
    else do
      rep <- buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = isTreeRoot})
      return $ toJSON rep

traceSpanTM :: (ToJSONWTIndexer a) => String -> RM a -> RM a
traceSpanTM name = traceActionTM name Nothing ttoJSON

traceSpanArgsTM :: (ToJSONWTIndexer a) => String -> String -> RM a -> RM a
traceSpanArgsTM name args = traceActionTM name (Just args) ttoJSON

traceSpanAdaptTM :: String -> (a -> RM Value) -> RM a -> RM a
traceSpanAdaptTM name = traceActionTM name Nothing

traceSpanArgsAdaptTM :: String -> String -> (a -> RM Value) -> RM a -> RM a
traceSpanArgsAdaptTM name args = traceActionTM name (Just args)

traceActionTM :: String -> Maybe String -> (a -> RM Value) -> RM a -> RM a
traceActionTM name argsM jsonfy f = withAddrAndFocus $ \addr _ ->
  traceAction name addr argsM jsonfy False f

traceAction :: String -> TreeAddr -> Maybe String -> (a -> RM Value) -> Bool -> RM a -> RM a
traceAction name addr argsM jsonfy ignoreFocus f = whenTraceEnabled name f do
  let isRoot = addr == rootTreeAddr
  bTraced <- getTMTree >>= spanTreeMsgs isRoot ignoreFocus
  addrS <- tshow addr
  trID <- getTraceID
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  let
    header = T.pack $ printf "%s, at:%s" name addrS

  traceSpanStart
    header
    ( toJSON $
        RMStartTraceArgs
          { cstaTraceID = trID
          , cstaAddr = addrS
          , cstaBeforeFocus = optVal extraInfo bTraced
          , cstaCustomVal = optVal extraInfo (toJSON argsM)
          }
    )

  res <- f
  resVal <- jsonfy res
  resFocus <- getTMTree >>= spanTreeMsgs isRoot ignoreFocus

  traceSpanExec
    header
    ( toJSON $
        RMEndTraceArgs
          { cetaResVal = optVal extraInfo resVal
          , cetaFocus = optVal extraInfo resFocus
          }
    )
  return res

optVal :: Bool -> Value -> Value
optVal extraInfo v = if extraInfo then v else object []

debugInstantTM :: String -> String -> RM ()
debugInstantTM name args = withAddrAndFocus $ \addr _ -> debugInst name args addr

debugInst :: String -> String -> TreeAddr -> RM ()
debugInst name args addr = whenTraceEnabled name (return ()) $ do
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  trID <- getTraceID
  debugInstant
    (T.pack name)
    ( toJSON $
        RMInstantTraceArgs
          { ctiTraceID = trID
          , ctiAddr = addrS
          , ctiCustomVal = optVal extraInfo (toJSON args)
          }
    )

traceSpanRMTC :: (ToJSONWTIndexer a) => String -> TrCur -> RM a -> RM a
traceSpanRMTC name = traceActionRM name Nothing ttoJSON

traceSpanArgsRMTC :: (ToJSONWTIndexer a) => String -> String -> TrCur -> RM a -> RM a
traceSpanArgsRMTC name args = traceActionRM name (Just args) ttoJSON

traceSpanAdaptRM :: String -> (a -> RM Value) -> TrCur -> RM a -> RM a
traceSpanAdaptRM name = traceActionRM name Nothing

traceSpanArgsAdaptRM :: String -> String -> (a -> RM Value) -> TrCur -> RM a -> RM a
traceSpanArgsAdaptRM name args = traceActionRM name (Just args)

traceActionRM :: String -> Maybe String -> (a -> RM Value) -> TrCur -> RM a -> RM a
traceActionRM name argsM resFetch tc = traceAction name (tcAddr tc) argsM resFetch True

debugInstantRM :: String -> String -> TrCur -> RM ()
debugInstantRM name args tc = debugInst name args (tcAddr tc)

debugInstantOpRM :: String -> String -> TreeAddr -> RM ()
debugInstantOpRM = debugInst

emptySpanValue :: a -> RM Value
emptySpanValue _ = return $ toJSON ()