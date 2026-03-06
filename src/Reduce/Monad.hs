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

newtype ReduceParams = ReduceParams {createCnstr :: Bool}

instance Show ReduceParams where
  show c = "ReduceParams {createCnstr = " ++ show c.createCnstr ++ " }"

emptyReduceParams :: ReduceParams
emptyReduceParams = ReduceParams{createCnstr = False}

type RM = RWST ReduceConfig () Context (ExceptT String IO)

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

data RCResolver = RCResolver
  { stack :: [SuffixIrredAddr]
  -- ^ The current stack of RC addresses being recalculated.
  , doneRCAddrs :: [SuffixIrredAddr]
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
  , recalcRootQ :: Seq.Seq RecalcItem
  -- ^ The recalculation root queue.
  , depGraph :: DepGraph
  , lastDerefs :: Map.Map SuffixIrredAddr (Map.Map ReferableAddr Val)
  -- ^ It stores the last dereferenced value of the reference with the suffix irreducible address.
  -- We use the suffix irreducible address because when reducing all the mutable arguments, they are reduced at the same
  -- time, so if any of them references to the same referable address, they will have the same value.
  , vStore :: Map.Map SuffixIrredAddr Val
  , rcResolver :: !RCResolver
  , noSignalReduced :: !Bool
  -- ^ If true, do not signal ready after reducing.
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

mapDepGraph :: (DepGraph -> DepGraph) -> Context -> Context
mapDepGraph f ctx = ctx{depGraph = f (depGraph ctx)}

data RecalcItem = RecalcItem
  { addr :: ValAddr
  , rfbAddr :: ReferableAddr
  , grpAddr :: GrpAddr
  , isReduced :: !Bool
  }
  deriving (Show, Generic, NFData)

instance ShowWTIndexer RecalcItem where
  tshow RecalcItem{addr, grpAddr, isReduced} = do
    addrT <- tshow addr
    grpAddrT <- tshow grpAddr
    return $ T.pack $ printf "RecalcItem {addr:%s,grpAddr:%s,isReduced:%s}" addrT grpAddrT (show isReduced)

emptyContext :: (LB.ByteString -> IO ()) -> Context
emptyContext tPut =
  Context
    { ctxObjID = 0
    , recalcRootQ = Seq.empty
    , depGraph = emptyPropGraph
    , lastDerefs = Map.empty
    , vStore = Map.empty
    , rcResolver = emptyRCResolver
    , noSignalReduced = False
    , ctxTrace = emptyTrace tPut
    , tIndexer = emptyTextIndexer
    }

throwFatal :: (HasCallStack) => String -> RM a
throwFatal msg = throwError $ msg ++ "\n" ++ prettyCallStack callStack

-- Context

{-# INLINE getRMContext #-}
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

-- Notify ready

getNoSignalReduced :: RM Bool
getNoSignalReduced = noSignalReduced <$> getRMContext

setNoSignalReduced :: Bool -> RM ()
setNoSignalReduced b = modifyRMContext $ \ctx -> ctx{noSignalReduced = b}

withNoSignalReduced :: Bool -> RM a -> RM a
withNoSignalReduced b f = do
  oldB <- getNoSignalReduced
  setNoSignalReduced b
  r <- f
  setNoSignalReduced oldB
  return r

-- Val depth check

treeDepthCheck :: ValAddr -> RM ()
treeDepthCheck vc = do
  let depth = length $ addrToList vc
  Config{stMaxTreeDepth = maxDepth} <- asks baseConfig
  let maxDepthVal = if maxDepth <= 0 then 1000 else maxDepth
  when (depth > maxDepthVal) $ throwFatal $ printf "tree depth exceeds max depth (%d)" maxDepthVal

getRCResolver :: RM RCResolver
getRCResolver = rcResolver <$> getRMContext

mapRCResolver :: (RCResolver -> RCResolver) -> RM ()
mapRCResolver f = modifyRMContext $ \ctx -> ctx{rcResolver = f (rcResolver ctx)}