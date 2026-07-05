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
import Control.Monad (when)
import Control.Monad.Except (ExceptT (..), throwError)
import Control.Monad.RWS.Strict (RWST)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (get, gets, modify')
import qualified Data.ByteString.Lazy as LB
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import DepGraph
import Feature
import GHC.Generics (Generic)
import GHC.Stack (callStack, prettyCallStack)
import GHC.Stack.Types (HasCallStack)
import StringIndex (HasTextIndexer (..), ShowWTIndexer (..), TextIndex, TextIndexer, emptyTextIndexer)
import Text.Printf (printf)
import Util.Trace (HasTrace (..), Trace, emptyTrace)
import Value

newtype ReduceParams = ReduceParams {createCnstr :: Bool}

instance Show ReduceParams where
  show c = "ReduceParams {createCnstr = " ++ show c.createCnstr ++ " }"

emptyReduceParams :: ReduceParams
emptyReduceParams = ReduceParams{createCnstr = False}

type RM = RWST ReduceConfig () Context (ExceptT String IO)

data ReduceConfig = ReduceConfig
  { traceConfig :: TraceConfig
  , debugMode :: Bool
  , maxTreeDepth :: Int
  , params :: ReduceParams
  }
  deriving (Show)

data TraceConfig = TraceConfig
  { stTraceEnable :: !Bool
  , stTraceDisableShowValue :: !Bool
  }
  deriving (Show)

emptyTraceConfig :: TraceConfig
emptyTraceConfig =
  TraceConfig
    { stTraceEnable = False
    , stTraceDisableShowValue = False
    }

mapParams :: (ReduceParams -> ReduceParams) -> ReduceConfig -> ReduceConfig
mapParams f r = r{params = f (params r)}

emptyReduceConfig :: ReduceConfig
emptyReduceConfig =
  ReduceConfig
    { traceConfig = emptyTraceConfig
    , maxTreeDepth = 0
    , debugMode = False
    , params = emptyReduceParams
    }

data RCResolver = RCResolver
  { stack :: [VertexAddr]
  -- ^ The current stack of RC addresses being recalculated.
  , doneRCAddrs :: [VertexAddr]
  , resolving :: !Bool
  }
  deriving (Show, Generic, NFData)

emptyRCResolver :: RCResolver
emptyRCResolver =
  RCResolver
    { stack = []
    , doneRCAddrs = []
    , resolving = False
    }

data Context = Context
  { ctxObjID :: !Int
  , rootRecalcQ :: Seq.Seq ReducedSignal
  -- ^ The recalculation root queue.
  , depGraph :: DepGraph
  , lastDerefs :: LastDerefed
  , vStore :: Map.Map VertexAddr VNode
  -- ^ The value store that stores the reduced values with their canonical addresses, including dynamic fields and
  -- objects.
  , comprehBindings :: Seq.Seq [(TextIndex, VNode)]
  -- ^ The comprehension bindings stack.
  , rcResolver :: !RCResolver
  , ctxTrace :: Trace
  , tIndexer :: TextIndexer
  , flowIDMap :: Map.Map (GrpAddr, Int) Int
  , flowIDCounter :: !Int
  }

instance HasTrace Context where
  getTrace = ctxTrace
  setTrace ctx t = ctx{ctxTrace = t}

instance HasTextIndexer Context where
  getTextIndexer = Reduce.Monad.tIndexer
  setTextIndexer ti ctx = ctx{Reduce.Monad.tIndexer = ti}

mapDepGraph :: (DepGraph -> DepGraph) -> Context -> Context
mapDepGraph f ctx = ctx{depGraph = f (depGraph ctx)}

data LastDerefed = LastDerefed
  { ldUseToDep :: Map.Map VertexAddr (Map.Map ReferableAddr Int)
  -- ^ It stores the last dereferenced value of the reference with the canonical address.
  -- We use the canonical address because when reducing all the mutable arguments, they are reduced at the same
  -- time, so if any of them references to the same referable address, they will have the same value.
  , ldDepToUse :: Map.Map ReferableAddr (Map.Map VertexAddr Int)
  }
  deriving (Show, Generic, NFData)

emptyLastDerefed :: LastDerefed
emptyLastDerefed = LastDerefed{ldUseToDep = Map.empty, ldDepToUse = Map.empty}

data ReducedSignal = ReducedSignal
  { addr :: ValAddr
  , rfbAddr :: ReferableAddr
  , grpAddr :: GrpAddr
  , createdWithRCResolver :: Bool
  -- ^ If true, the signal is created with an active RC resolver.
  }
  deriving (Show, Generic, NFData)

instance ShowWTIndexer ReducedSignal where
  tshow ReducedSignal{addr, grpAddr, createdWithRCResolver} = do
    addrT <- tshow addr
    grpAddrT <- tshow grpAddr
    return $
      T.pack $
        printf "ReducedSignal {addr:%s,grpAddr:%s,createdWithRCResolver:%s}" addrT grpAddrT (show createdWithRCResolver)

emptyContext :: (LB.ByteString -> IO ()) -> Context
emptyContext tPut =
  Context
    { ctxObjID = 0
    , rootRecalcQ = Seq.empty
    , depGraph = emptyPropGraph
    , lastDerefs = emptyLastDerefed
    , vStore = Map.empty
    , comprehBindings = Seq.empty
    , rcResolver = emptyRCResolver
    , ctxTrace = emptyTrace tPut
    , tIndexer = emptyTextIndexer
    , flowIDMap = Map.empty
    , flowIDCounter = 0
    }

throwFatal :: (HasCallStack) => String -> RM a
throwFatal msg = throwError $ msg ++ "\n" ++ prettyCallStack callStack

-- Context

getRMContext :: RM Context
getRMContext = get

putRMContext :: Context -> RM ()
putRMContext ctx = modifyRMContext $ const ctx

modifyRMContext :: (Context -> Context) -> RM ()
modifyRMContext f = modify' $ \s -> f s

-- DepGraph

getRMDepGraph :: RM DepGraph
getRMDepGraph = gets depGraph

-- ObjID

allocRMObjID :: RM Int
allocRMObjID = do
  oid <- getRMObjID
  let newOID = oid + 1
  setRMObjID newOID
  return newOID

getRMObjID :: RM Int
getRMObjID = gets ctxObjID

setRMObjID :: Int -> RM ()
setRMObjID newID = modify' $ \ctx -> ctx{ctxObjID = newID}

-- VNode depth check

treeDepthCheck :: ValAddr -> RM ()
treeDepthCheck vc = do
  let depth = length $ addrToList vc
  maxDepth <- asks maxTreeDepth
  let maxDepthVal = if maxDepth <= 0 then 1000 else maxDepth
  when (depth > maxDepthVal) $ throwFatal $ printf "tree depth exceeds max depth (%d)" maxDepthVal

getRCResolver :: RM RCResolver
getRCResolver = rcResolver <$> getRMContext

mapRCResolver :: (RCResolver -> RCResolver) -> RM ()
mapRCResolver f = modifyRMContext $ \ctx -> ctx{rcResolver = f (rcResolver ctx)}