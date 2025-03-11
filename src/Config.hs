{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- {-# LANGUAGE QuantifiedConstraints #-}

module Config where

import AST (Expression)
import Class (TreeOp)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State.Strict (MonadState)
import Cursor (HasCtxVal)
import Env (Env)
import Exception (throwErrSt)
import Path (Reference, StructTASeg, TreeAddr)
import Text.Printf (printf)
import Util (HasTrace)
import Value.Struct (Struct)

type EM m t = (Env m, MonadReader (Config t) m, TreeOp t, MonadState Int m)
type MM s m t = (Env m, MonadState s m, MonadReader (Config t) m, TreeOp t, HasCtxVal s t t, HasTrace s)

data Settings = Settings
  { stMermaid :: Bool
  , stShowMutArgs :: Bool
  }
  deriving (Show)

newtype RuntimeParams = RuntimeParams
  { rpCreateCnstr :: Bool
  }
  deriving (Show)

data Functions t = Functions
  { fnEvalExpr :: forall m. (EM m t) => AST.Expression -> m t
  , fnClose :: forall s m. (MM s m t) => [t] -> m ()
  , fnReduce :: forall s m. (MM s m t) => m ()
  , fnDeref :: forall s m. (MM s m t) => Reference -> Maybe (TreeAddr, TreeAddr) -> m (Maybe TreeAddr)
  , fnIndex :: forall s m. (MM s m t) => Maybe (TreeAddr, TreeAddr) -> [t] -> m ()
  , fnPropUpStructPost :: forall s m. (MM s m t) => (StructTASeg, Struct t) -> m ()
  }

data Config t = Config
  { cfSettings :: Settings
  , cfRuntimeParams :: RuntimeParams
  , cfFunctions :: Functions t
  }

instance Show (Config t) where
  show c = printf "Config{%s}" (show $ cfSettings c)

emptySettings :: Settings
emptySettings =
  Settings
    { stMermaid = False
    , stShowMutArgs = False
    }

emptyRuntimeParams :: RuntimeParams
emptyRuntimeParams =
  RuntimeParams
    { rpCreateCnstr = False
    }

emptyFunctions :: Functions t
emptyFunctions =
  Functions
    { fnEvalExpr = \_ -> throwErrSt "fnEvalExpr not set"
    , fnClose = \_ -> throwErrSt "fnClose not set"
    , fnReduce = throwErrSt "fnReduce not set"
    , fnDeref = \_ _ -> throwErrSt "fnDeref not set"
    , fnIndex = \_ _ -> throwErrSt "fnIndex not set"
    , fnPropUpStructPost = \_ -> throwErrSt "fnPropUpStructPost not set"
    }

emptyConfig :: Config t
emptyConfig =
  Config
    { cfSettings = emptySettings
    , cfRuntimeParams = emptyRuntimeParams
    , cfFunctions = emptyFunctions
    }
