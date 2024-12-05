{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

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

data Config t = Config
  { cfCreateCnstr :: Bool
  , cfMermaid :: Bool
  , cfEvalExpr ::
      forall m.
      (Env m, MonadReader (Config t) m, TreeOp t, MonadState Int m) =>
      AST.Expression ->
      m t
  , cfClose ::
      forall s m.
      (Env m, MonadState s m, MonadReader (Config t) m, TreeOp t, HasCtxVal s t t, HasTrace s) =>
      Bool ->
      [t] ->
      m ()
  , cfReduce ::
      forall s m.
      (Env m, MonadState s m, MonadReader (Config t) m, TreeOp t, HasCtxVal s t t, HasTrace s) =>
      m ()
  , cfDeref ::
      forall s m.
      (Env m, MonadState s m, MonadReader (Config t) m, TreeOp t, HasCtxVal s t t, HasTrace s) =>
      Reference ->
      Bool ->
      m ()
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
    , cfDeref = \_ _ -> throwErrSt "cfDeref not set"
    }
