{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Env where

import Control.Monad.Except (MonadError)
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)

type ErrorEnv m =
  ( MonadError String m
  , HasCallStack
  )

data Config = Config
  { stTraceEnable :: Bool
  , stTraceExtraInfo :: Bool
  , stTracePrintTree :: Bool
  , stTraceFilter :: Set.Set String
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
    , stMaxTreeDepth = 0
    }
