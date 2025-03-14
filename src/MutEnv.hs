{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}

module MutEnv where

import qualified AST
import Common (Env, TreeOp)
import Control.Monad.State.Strict (MonadState)
import Cursor (HasCtxVal)
import Exception (throwErrSt)
import qualified Path
import Util (HasTrace)
import Value.Reference (RefArg, Reference)
import Value.Struct (Struct)

-- This file is used to break the circular dependency on Mutable.

class HasFuncs r t | r -> t where
  getFuncs :: r -> Functions t
  setFuncs :: r -> Functions t -> r

type EvalEnv r t m =
  ( Env r m
  , TreeOp t
  , MonadState Int m
  , HasFuncs r t
  )

type MutableEnv s r t m =
  ( Env r m
  , MonadState s m
  , TreeOp t
  , HasCtxVal s t t
  , HasTrace s
  , HasFuncs r t
  )

data Functions t = Functions
  { fnEvalExpr :: forall r m. (EvalEnv r t m) => AST.Expression -> m t
  , fnClose :: forall s r m. (MutableEnv s r t m) => [t] -> m ()
  , fnReduce :: forall s r m. (MutableEnv s r t m) => m ()
  , fnIndex ::
      forall s r m.
      (MutableEnv s r t m) =>
      Maybe (Path.TreeAddr, Path.TreeAddr) ->
      RefArg t ->
      m (Either t (Maybe Path.TreeAddr))
  , fnPropUpStructPost :: forall s r m. (MutableEnv s r t m) => (Path.StructTASeg, Struct t) -> m ()
  }

emptyFunctions :: Functions t
emptyFunctions =
  Functions
    { fnEvalExpr = \_ -> throwErrSt "fnEvalExpr not set"
    , fnClose = \_ -> throwErrSt "fnClose not set"
    , fnReduce = throwErrSt "fnReduce not set"
    , fnIndex = \_ _ -> throwErrSt "fnIndex not set"
    , fnPropUpStructPost = \_ -> throwErrSt "fnPropUpStructPost not set"
    }