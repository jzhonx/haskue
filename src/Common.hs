{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Common where

import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (MonadState)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)
import Path (TreeAddr)
import Util (HasTrace (..), Trace, emptyTrace)

type Env r s m =
  ( MonadError String m
  , HasCallStack
  , MonadReader r m
  , HasConfig r
  , MonadState s m
  , HasTrace s
  , MonadIO m
  )

class HasConfig r where
  getConfig :: r -> Config
  setConfig :: r -> Config -> r

class IDStore s where
  getID :: s -> Int
  setID :: s -> Int -> s

class HasContext s where
  getContext :: s -> Context
  setContext :: s -> Context -> s
  modifyContext :: s -> (Context -> Context) -> s

data Config = Config
  { cfSettings :: Settings
  , cfRuntimeParams :: RuntimeParams
  }
  deriving (Show)

data Settings = Settings
  { stDebugLogging :: Bool
  , stTraceExec :: Bool
  , stTracePrintTree :: Bool
  , stTraceFilter :: Set.Set String
  , stShowMutArgs :: Bool
  , stMaxTreeDepth :: Int
  }
  deriving (Show)

newtype RuntimeParams = RuntimeParams
  { rpCreateCnstr :: Bool
  }
  deriving (Show)

emptyConfig :: Config
emptyConfig =
  Config
    { cfSettings = emptySettings
    , cfRuntimeParams = emptyRuntimeParams
    }

emptySettings :: Settings
emptySettings =
  Settings
    { stDebugLogging = False
    , stTraceExec = False
    , stTracePrintTree = False
    , stTraceFilter = Set.empty
    , stShowMutArgs = False
    , stMaxTreeDepth = 0
    }

emptyRuntimeParams :: RuntimeParams
emptyRuntimeParams =
  RuntimeParams
    { rpCreateCnstr = False
    }

data EEState = EEState
  { eesObjID :: Int
  , eesTrace :: Trace
  }
  deriving (Show)

instance IDStore EEState where
  getID = eesObjID
  setID s i = s{eesObjID = i}

instance HasTrace EEState where
  getTrace = eesTrace
  setTrace s tr = s{eesTrace = tr}

emptyEEState :: EEState
emptyEEState = EEState{eesObjID = 0, eesTrace = emptyTrace}

data Context = Context
  { ctxObjID :: !Int
  , ctxGlobalVers :: !Int
  , ctxReduceStack :: [TreeAddr]
  , ctxNotifEnabled :: !Bool
  , ctxNotifGraph :: Map.Map TreeAddr [TreeAddr]
  , ctxReadyQueue :: [TreeAddr]
  -- ^ The ready queue is a queue of addresses that have been reduced and can notify their dependents.
  , ctxLetMap :: Map.Map TreeAddr Bool
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
    , ctxGlobalVers = 0
    , ctxReduceStack = []
    , ctxNotifGraph = Map.empty
    , ctxReadyQueue = []
    , ctxNotifEnabled = True
    , ctxLetMap = Map.empty
    , ctxTrace = emptyTrace
    }

{- | Add a notification pair to the context.

The first element is the source addr, which is the addr that is being watched.
The second element is the dependent addr, which is the addr that is watching the source addr.
-}
addCtxNotifPair :: Context -> (TreeAddr, TreeAddr) -> Context
addCtxNotifPair ctx (src, dep) = ctx{ctxNotifGraph = Map.insert src newDepList oldMap}
 where
  oldMap = ctxNotifGraph ctx
  depList = fromMaybe [] $ Map.lookup src oldMap
  newDepList = if dep `elem` depList then depList else dep : depList

hasCtxNotifSender :: TreeAddr -> Context -> Bool
hasCtxNotifSender addr ctx = Map.member addr (ctxNotifGraph ctx)

showRefNotifiers :: Map.Map TreeAddr [TreeAddr] -> String
showRefNotifiers notifiers =
  let s = Map.foldrWithKey go "" notifiers
   in if null s then "[]" else "[" ++ s ++ "\n]"
 where
  go :: TreeAddr -> [TreeAddr] -> String -> String
  go src deps acc = acc ++ "\n" ++ show src ++ " -> " ++ show deps