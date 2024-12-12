{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- {-# LANGUAGE QuantifiedConstraints #-}

module Config where

import AST
import Class
import Control.Monad.Reader (MonadReader)
import Control.Monad.State.Strict (MonadState)
import Cursor
import Env
import Error
import Path
import Text.Printf (printf)
import Util

type EM m t = (Env m, MonadReader (Config t) m, TreeOp t, MonadState Int m)
type MM s m t = (Env m, MonadState s m, MonadReader (Config t) m, TreeOp t, HasCtxVal s t t, HasTrace s)

data Config t = Config
  { cfCreateCnstr :: Bool
  , cfMermaid :: Bool
  , cfEvalExpr :: forall m. (EM m t) => AST.Expression -> m t
  , cfClose :: forall s m. (MM s m t) => Bool -> [t] -> m ()
  , cfReduce :: forall s m. (MM s m t) => m ()
  , cfDeref :: forall s m. (MM s m t) => Reference -> m ()
  , cfIndex :: forall s m. (MM s m t) => [t] -> m ()
  }

instance Show (Config t) where
  show c = printf "Config{cfCreateCnstr: %s, cfMermaid: %s}" (show $ cfCreateCnstr c) (show $ cfMermaid c)

emptyConfig :: (Config t)
emptyConfig =
  Config
    { cfCreateCnstr = False
    , cfMermaid = False
    , cfEvalExpr = \_ -> throwErrSt "cfEvalExpr not set"
    , cfClose = \_ _ -> throwErrSt "cfClose not set"
    , cfReduce = throwErrSt "cfReduce not set"
    , cfDeref = \_ -> throwErrSt "cfDeref not set"
    , cfIndex = \_ -> throwErrSt "cfIndex not set"
    }
