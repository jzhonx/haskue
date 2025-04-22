{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Common where

import qualified AST
import Control.Monad.Except (MonadError)
import Control.Monad.Logger (MonadLogger)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (MonadState)
import GHC.Stack (HasCallStack)
import Path (TASeg)
import Util (HasTrace (..), Trace, emptyTrace)

type Env r s m =
  ( MonadError String m
  , MonadLogger m
  , HasCallStack
  , MonadReader r m
  , HasConfig r
  , MonadState s m
  , HasTrace s
  )

class HasConfig r where
  getConfig :: r -> Config
  setConfig :: r -> Config -> r

class IDStore s where
  getID :: s -> Int
  setID :: s -> Int -> s

class BuildASTExpr a where
  -- The first argument is a flag to indicate whether the expression is required to be concrete.
  buildASTExpr :: (Env r s m) => Bool -> a -> m AST.Expression

class TreeRepBuilder a where
  repTree :: Int -> a -> String

class TreeOp a where
  -- | step down the tree with the given segment.
  -- This should only be used by TreeCursor.
  subTree :: TASeg -> a -> Maybe a

  -- | Set the subtree to the given tree with the segment. The first argument is the segment, the second argument is the
  -- sub tree, and the third argument is the tree to be updated.
  setSubTree :: (Env r s m) => TASeg -> a -> a -> m a

  delTemp :: a -> a

  isTreeAtom :: a -> Bool
  isTreeBottom :: a -> Bool
  isTreeCnstr :: a -> Bool
  isTreeRefCycle :: a -> Bool
  isTreeMutable :: a -> Bool
  isTreeValue :: a -> Bool

  treeHasRef :: a -> Bool

  -- TODO: rename
  treeHasAtom :: a -> Bool

data Config = Config
  { cfSettings :: Settings
  , cfRuntimeParams :: RuntimeParams
  }
  deriving (Show)

data Settings = Settings
  { stMermaid :: Bool
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
    { stMermaid = False
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