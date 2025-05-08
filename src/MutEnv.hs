{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}

module MutEnv where

import qualified AST
import Common (Env, HasContext, IDStore (..), TreeOp)
import Cursor (TreeCursor)
import Exception (throwErrSt)

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
  , -- , HasTreeCursor s t
    HasFuncs r t
  , HasContext s
  )

data Functions t = Functions
  { fnEvalExpr :: forall r s m. (EvalEnv r s t m) => AST.Expression -> m t
  , fnReduce :: forall r s m. (MutableEnv r s t m) => TreeCursor t -> m t
  , reduceUnifyConj :: forall r s m. (MutableEnv r s t m) => TreeCursor t -> m (Maybe t)
  }

emptyFunctions :: Functions t
emptyFunctions =
  Functions
    { fnEvalExpr = \_ -> throwErrSt "fnEvalExpr not set"
    , fnReduce = \_ -> throwErrSt "fnReduce not set"
    , reduceUnifyConj = \_ -> throwErrSt "fnReduceMutOnly not set"
    }