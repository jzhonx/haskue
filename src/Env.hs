{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Env where

import Control.Monad.Except (MonadError)
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)
import StringIndex (HasTextIndexer (..), TextIndexer, emptyTextIndexer)
import Util (HasTrace (..), Trace, emptyTrace)

type ErrorEnv m =
  ( MonadError String m
  , HasCallStack
  )

data Config = Config
  { stTraceEnable :: Bool
  , stTraceExtraInfo :: Bool
  , stTracePrintTree :: Bool
  , stTraceFilter :: Set.Set String
  , stShowMutArgs :: Bool
  , stMaxTreeDepth :: Int
  }
  deriving (Show)

emptyConfig :: Config
emptyConfig =
  Config
    { stTraceEnable = False
    , stTraceExtraInfo = False
    , stTracePrintTree = False
    , stTraceFilter = Set.empty
    , stShowMutArgs = False
    , stMaxTreeDepth = 0
    }
