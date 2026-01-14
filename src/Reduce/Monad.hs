{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Monad where

import Control.DeepSeq (NFData)
import Control.Monad (foldM, unless, when)
import Control.Monad.Except (ExceptT (..), MonadError, throwError)
import Control.Monad.RWS.Strict (RWST, lift)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (gets, modify')
import Cursor
import qualified Data.ByteString.Lazy as LB
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence as Seq
import DepGraph
import Env (
  Config (..),
  emptyConfig,
 )
import Feature
import GHC.Generics (Generic)
import GHC.Stack (callStack, prettyCallStack)
import GHC.Stack.Types (HasCallStack)
import StringIndex (HasTextIndexer (..), ShowWTIndexer (..), TextIndexer, emptyTextIndexer)
import Text.Printf (printf)
import Util.Trace (HasTrace (..), Trace, emptyTrace)
import Value
import Value.Export.Debug

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
  , ctxReduceStack :: [ValAddr]
  , isRecalcing :: !Bool
  , recalcRootQ :: Seq.Seq (ValAddr, GrpAddr)
  -- ^ The recalculation root queue.
  , depGraph :: DepGraph
  , lastValueMap :: Map.Map SuffixIrredAddr Val
  , ctxLetMap :: Map.Map ValAddr Bool
  , rcdIsReducingRCs :: !Bool
  , noRecalc :: !Bool
  -- ^ If true, do not perform recalculation when reducing struct objects.
  , ctxTrace :: Trace
  , tIndexer :: TextIndexer
  }
  deriving (Show, Generic, NFData)

instance HasTrace Context where
  getTrace = ctxTrace
  setTrace ctx t = ctx{ctxTrace = t}

instance HasTextIndexer Context where
  getTextIndexer = Reduce.Monad.tIndexer
  setTextIndexer ti ctx = ctx{Reduce.Monad.tIndexer = ti}

emptyContext :: (LB.ByteString -> IO ()) -> Context
emptyContext tPut =
  Context
    { ctxObjID = 0
    , ctxReduceStack = []
    , isRecalcing = False
    , recalcRootQ = Seq.empty
    , depGraph = emptyPropGraph
    , lastValueMap = Map.empty
    , ctxLetMap = Map.empty
    , rcdIsReducingRCs = False
    , noRecalc = False
    , ctxTrace = emptyTrace tPut
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
  { rtsTC :: !VCur
  , rtsCtx :: Context
  }
  deriving (Show, Generic, NFData)

mapTC :: (VCur -> VCur) -> RTCState -> RTCState
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
delTMDepPrefix :: ValAddr -> RM ()
delTMDepPrefix addrPrefix =
  modifyRMContext $ \ctx -> ctx{depGraph = delNGVertexPrefix addrPrefix (depGraph ctx)}

delMutValRecvs :: ValAddr -> RM ()
delMutValRecvs = undefined

addRMDanglingLet :: ValAddr -> RM ()
addRMDanglingLet addr = modifyRMContext $ \ctx ->
  let
    oldMap = ctxLetMap ctx
    newMap = if addr `Map.member` oldMap then oldMap else Map.insert addr False oldMap
   in
    ctx{ctxLetMap = newMap}

getRMDanglingLets :: RM [ValAddr]
getRMDanglingLets = do
  ctx <- getRMContext
  let letAddrs = Map.toList (ctxLetMap ctx)
  return [addr | (addr, False) <- letAddrs]

markRMLetReferred :: ValAddr -> RM ()
markRMLetReferred addr = modifyRMContext $ \ctx ->
  let newMap = Map.insert addr True (ctxLetMap ctx)
   in ctx{ctxLetMap = newMap}

-- Cursor

{-# INLINE getTMCursor #-}
getTMCursor :: RM VCur
getTMCursor = gets rtsTC

modifyTMCursor :: (VCur -> VCur) -> RM ()
modifyTMCursor f = modify' $ \s -> s{rtsTC = f (rtsTC s)}

putTMCursor :: VCur -> RM ()
putTMCursor vc = modifyTMCursor $ const vc

{-
====== ValAddr ======
-}

getTMAbsAddr :: RM ValAddr
getTMAbsAddr = vcAddr <$> getTMCursor

getTMTASeg :: RM Feature
getTMTASeg = do
  vc <- getTMCursor
  liftEitherRM (vcFocusSegMust vc)

-- Crumbs

getTMCrumbs :: RM [(Feature, Val)]
getTMCrumbs = crumbs <$> getTMCursor

-- Val

{-# INLINE getTMVal #-}
getTMVal :: RM Val
getTMVal = focus <$> getTMCursor

modifyTMVal :: (Val -> Val) -> RM ()
modifyTMVal f = modifyTMCursor $ \vc -> f (focus vc) `setVCFocus` vc

putTMVal :: Val -> RM ()
putTMVal t = modifyTMVal $ const t

supersedeTMVN :: ValNode -> RM ()
supersedeTMVN tn = modifyTMVal (supersedeVN tn)

unwrapTMVN :: (Val -> ValNode) -> RM ()
unwrapTMVN f = modifyTMVal (unwrapVN f)

withVal :: (Val -> RM a) -> RM a
withVal f = getTMVal >>= f

withAddrAndFocus :: (ValAddr -> Val -> RM a) -> RM a
withAddrAndFocus f = do
  addr <- getTMAbsAddr
  withVal (f addr)

{- | Get the parent of the current focus.

This does not propagate the value up.
-}
getTMParent :: RM Val
getTMParent = do
  crumbs <- getTMCrumbs
  case crumbs of
    [] -> throwFatal "already at the top"
    (_, t) : _ -> return t

-- ValNode

withVN :: (ValNode -> RM a) -> RM a
withVN f = withVal (f . valNode)

modifyTMVN :: ValNode -> RM ()
modifyTMVN vn = modifyTMVal $ \t -> setVN vn t

modifyTMNodeWithVal :: Val -> RM ()
modifyTMNodeWithVal t = modifyTMVN (valNode t)

-- ReduceMonad operations

-- PropUp operations

-- | Propagate the value up.
propUpTM :: RM ()
propUpTM = do
  vc <- getTMCursor
  liftEitherRM (propUpVC vc) >>= putTMCursor

runTMTCAction :: (forall n. (Monad n) => VCur -> n Val) -> RM ()
runTMTCAction f = do
  vc <- getTMCursor
  r <- f vc
  putTMCursor (r `setVCFocus` vc)

-- Propagate the value up until the lowest segment is matched.
propUpTMUntilSeg :: Feature -> RM ()
propUpTMUntilSeg seg = do
  vc <- getTMCursor
  unless (isMatched vc) $ do
    propUpTM
    propUpTMUntilSeg seg
 where
  isMatched :: VCur -> Bool
  isMatched (VCur _ []) = False -- propUpTM would panic.
  isMatched (VCur _ ((s, _) : _)) = s == seg

-- Move down operations

descendTM :: ValAddr -> RM Bool
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
  vc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownVCSeg seg vc)

descendTMSegMust :: Feature -> RM ()
descendTMSegMust seg = do
  ok <- descendTMSeg seg
  unless ok $ do
    t <- getTMVal
    rep <- treeToRepString t
    throwFatal $ printf "descend to %s failed, cur tree: %s" (show seg) rep

-- Push down operations

-- | Push down the segment with the new value.
_pushTMSub :: Feature -> Val -> RM ()
_pushTMSub seg sub = do
  (VCur p crumbs) <- getTMCursor
  putTMCursor $ VCur sub ((seg, p) : crumbs)

-- Push and pop operations

{- | Run the action in the sub tree.

The sub tree must exist.
-}
inSubTM :: Feature -> RM a -> RM a
inSubTM seg f = do
  ok <- descendTMSeg seg
  unless ok $ do
    t <- getTMVal
    rep <- treeToRepString t
    throwFatal $ printf "descend to %s failed, cur tree: %s" (show seg) rep
  r <- f
  propUpTM
  return r

-- Remote operations

goTMAbsAddr :: ValAddr -> RM Bool
goTMAbsAddr addr = do
  when (headSeg addr /= Just rootFeature) $ do
    addrStr <- tshow addr
    throwFatal (printf "the addr %s should start with the root segment" (show addrStr))
  propUpTMUntilSeg rootFeature
  let dstWoRoot = fromJust $ tailValAddr addr
  rM <- goDownVCAddr dstWoRoot <$> getTMCursor
  maybe (return False) (\r -> putTMCursor r >> return True) rM

goTMAbsAddrMust :: (HasCallStack) => ValAddr -> RM ()
goTMAbsAddrMust addr = do
  origAddr <- getTMAbsAddr
  ok <- goTMAbsAddr addr
  unless ok $ do
    addrStr <- tshow addr
    origAddrStr <- tshow origAddr
    throwFatal $ printf "cannot go to addr (%s) tree from %s" (show addrStr) (show origAddrStr)

-- | TODO: some functions do not require going back to the original address.
inRemoteTM :: ValAddr -> RM a -> RM a
inRemoteTM addr f = do
  origAddr <- getTMAbsAddr
  goTMAbsAddrMust addr
  r <- f
  goTMAbsAddrMust origAddr
  return r

inTempTM :: String -> Val -> RM a -> RM a
inTempTM name tmpT f = do
  modifyTMVal (\t -> t{tmpSub = Just tmpT})
  tf <- strToTempFeature name
  res <- inSubTM tf f
  modifyTMVal (\t -> t{tmpSub = Nothing})
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

-- Val depth check

treeDepthCheck :: VCur -> RM ()
treeDepthCheck vc = do
  let depth = length vc.crumbs
  Config{stMaxTreeDepth = maxDepth} <- asks baseConfig
  let maxDepthVal = if maxDepth <= 0 then 1000 else maxDepth
  when (depth > maxDepthVal) $ throwFatal $ printf "tree depth exceeds max depth (%d)" maxDepthVal

unlessFocusBottom :: a -> RM a -> RM a
unlessFocusBottom a f = do
  t <- getTMVal
  case valNode t of
    VNBottom _ -> return a
    _ -> f

{- | Visit every node in the tree in pre-order and apply the function.

It does not re-constrain struct fields.
-}
preVisitVal ::
  (VCur -> [SubNodeSeg]) ->
  ((VCur, a) -> RM (VCur, a)) ->
  (VCur, a) ->
  RM (VCur, a)
preVisitVal subs f x = do
  y <- f x
  foldM
    ( \acc subSeg -> do
        (seg, pre, post) <- case subSeg of
          SubNodeSegNormal seg -> return (seg, return, return)
          SubNodeSegEmbed seg -> do
            let origSeg = fromJust $ vcFocusSeg (fst acc)
            return (seg, propUpVC, goDownVCSegMust origSeg)
        subTC <- liftEitherRM (pre (fst acc) >>= goDownVCSegMust seg)
        z <- preVisitVal subs f (subTC, snd acc)
        nextTC <- liftEitherRM (propUpVC (fst z) >>= post)
        return (nextTC, snd z)
    )
    y
    (subs $ fst y)

-- | A simple version of the preVisitVal function that does not return a custom value.
preVisitValSimple ::
  (VCur -> [SubNodeSeg]) ->
  (VCur -> RM VCur) ->
  VCur ->
  RM VCur
preVisitValSimple subs f vc = do
  (r, _) <-
    preVisitVal
      subs
      ( \(x, _) -> do
          r <- f x
          return (r, ())
      )
      (vc, ())
  return r

{- | Visit every node in the tree in post-order and apply the function.

It does not re-constrain struct fields.
-}
postVisitVal ::
  (VCur -> [SubNodeSeg]) ->
  ((VCur, a) -> RM (VCur, a)) ->
  (VCur, a) ->
  RM (VCur, a)
postVisitVal subs f x = do
  y <-
    foldM
      ( \acc subSeg -> do
          (seg, pre, post) <- case subSeg of
            SubNodeSegNormal seg -> return (seg, return, return)
            SubNodeSegEmbed seg -> do
              let origSeg = fromJust $ vcFocusSeg (fst acc)
              return (seg, propUpVC, goDownVCSegMust origSeg)

          subTC <- liftEitherRM (pre (fst acc) >>= goDownVCSegMust seg)
          z <- postVisitVal subs f (subTC, snd acc)
          nextTC <- liftEitherRM (propUpVC (fst z) >>= post)
          return (nextTC, snd z)
      )
      x
      (subs $ fst x)
  f y

postVisitValSimple ::
  (VCur -> [SubNodeSeg]) ->
  (VCur -> RM VCur) ->
  VCur ->
  RM VCur
postVisitValSimple subs f vc = do
  (r, _) <-
    postVisitVal
      subs
      ( \(x, _) -> do
          r <- f x
          return (r, ())
      )
      (vc, ())
  return r
