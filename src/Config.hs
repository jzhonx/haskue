{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Config where

import AST
import Class
import Control.Monad.Except (throwError)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State.Strict (MonadState)
import Cursor
import Env
import Text.Printf (printf)

data Config t = Config
  { cfCreateCnstr :: Bool
  , cfMermaid :: Bool
  , cfEvalExpr :: forall m. (Env m, MonadReader (Config t) m, TreeOp t) => AST.Expression -> m t
  , cfClose ::
      forall s m.
      (Env m, MonadState s m, MonadReader (Config t) m, TreeOp t, HasCtxVal s t t) =>
      Bool ->
      [t] ->
      m Bool
  }

instance Show (Config t) where
  show c = printf "Config{cfCreateCnstr: %s, cfMermaid: %s}" (show $ cfCreateCnstr c) (show $ cfMermaid c)

emptyConfig :: (Config t)
emptyConfig =
  Config
    { cfCreateCnstr = False
    , cfMermaid = False
    , cfEvalExpr = \_ -> throwError "cfEvalExpr not set"
    , cfClose = \_ _ -> throwError "cfClose not set"
    }
