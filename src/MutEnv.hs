{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}

module MutEnv where

import qualified AST
import Common (Env, IDStore (..), TreeOp)
import Cursor (HasCtxVal)
import Exception (throwErrSt)
import qualified Path
import Value.Comprehension (Comprehension)
import Value.Reference (RefArg)
import Value.Struct (Struct)

-- This file is used to break the circular dependency on Mutable.

class HasFuncs r t | r -> t where
  getFuncs :: r -> Functions t
  setFuncs :: r -> Functions t -> r

type EvalEnv r s t m =
  ( Env r s m
  , TreeOp t
  , IDStore s
  )

type MutableEnv r s t m =
  ( Env r s m
  , TreeOp t
  , IDStore s
  , HasCtxVal s t t
  , HasFuncs r t
  )

data Functions t = Functions
  { fnEvalExpr :: forall r s m. (EvalEnv r s t m) => AST.Expression -> m t
  , fnClose :: forall r s m. (MutableEnv r s t m) => [t] -> m ()
  , fnReduce :: forall r s m. (MutableEnv r s t m) => m ()
  , fnIndex ::
      forall r s m.
      (MutableEnv r s t m) =>
      Maybe (Path.TreeAddr, Path.TreeAddr) ->
      RefArg t ->
      m (Either t (Maybe Path.TreeAddr))
  , fnPropUpStructPost :: forall r s m. (MutableEnv r s t m) => (Path.StructTASeg, Struct t) -> m ()
  , fnComprehend :: forall r s m. (MutableEnv r s t m) => Comprehension t -> m ()
  , fnUnifyEmbeds :: forall r s m. (MutableEnv r s t m) => t -> m ()
  }

emptyFunctions :: Functions t
emptyFunctions =
  Functions
    { fnEvalExpr = \_ -> throwErrSt "fnEvalExpr not set"
    , fnClose = \_ -> throwErrSt "fnClose not set"
    , fnReduce = throwErrSt "fnReduce not set"
    , fnIndex = \_ _ -> throwErrSt "fnIndex not set"
    , fnPropUpStructPost = \_ -> throwErrSt "fnPropUpStructPost not set"
    , fnComprehend = \_ -> throwErrSt "fnComprehend not set"
    , fnUnifyEmbeds = \_ -> throwErrSt "fnUnifyEmbeds not set"
    }