{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Common where

import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (MonadState)
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)
import Util (HasTrace (..), Trace, emptyTrace)

type EnvIO r s m =
  ( ErrorEnv m
  , MonadReader r m
  , HasConfig r
  , MonadState s m
  , HasTrace s
  , MonadIO m
  )

type ErrorEnv m =
  ( MonadError String m
  , HasCallStack
  )

class HasConfig r where
  getConfig :: r -> Config
  setConfig :: r -> Config -> r
  modifyConfig :: (Config -> Config) -> r -> r

class IDStore s where
  getID :: s -> Int
  setID :: s -> Int -> s

data Config = Config
  { stDebugLogging :: Bool
  , stTraceExec :: Bool
  , stTracePrintTree :: Bool
  , stTraceFilter :: Set.Set String
  , stShowMutArgs :: Bool
  , stMaxTreeDepth :: Int
  }
  deriving (Show)

instance HasConfig Config where
  getConfig = id
  setConfig _ c = c
  modifyConfig f = f

emptyConfig :: Config
emptyConfig =
  Config
    { stDebugLogging = False
    , stTraceExec = False
    , stTracePrintTree = False
    , stTraceFilter = Set.empty
    , stShowMutArgs = False
    , stMaxTreeDepth = 0
    }

data CommonState = CommonState
  { eesObjID :: Int
  , eesTrace :: Trace
  }
  deriving (Show)

instance IDStore CommonState where
  getID = eesObjID
  setID s i = s{eesObjID = i}

instance HasTrace CommonState where
  getTrace = eesTrace
  setTrace s tr = s{eesTrace = tr}

emptyCommonState :: CommonState
emptyCommonState = CommonState{eesObjID = 0, eesTrace = emptyTrace}
