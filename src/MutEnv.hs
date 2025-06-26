{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}

module MutEnv where

import qualified AST
import Common (Env, HasContext, IDStore (..))
import Cursor (TreeCursor)
import Exception (throwErrSt)
import qualified Value.Tree as VT

-- This file is used to break the circular dependency on Mutable.

class HasFuncs r where
  getFuncs :: r -> Functions
  setFuncs :: r -> Functions -> r

type EvalEnv r s m =
  ( Env r s m
  , IDStore s
  )

type MutableEnv r s m =
  ( Env r s m
  , HasFuncs r
  , HasContext s
  )

data Functions = Functions
  { fnEvalExpr :: forall r s m. (EvalEnv r s m) => AST.Expression -> m VT.Tree
  , fnReduce :: forall r s m. (MutableEnv r s m) => TreeCursor VT.Tree -> m VT.Tree
  , reduceUnifyConj :: forall r s m. (MutableEnv r s m) => TreeCursor VT.Tree -> m (Maybe VT.Tree)
  }

emptyFunctions :: Functions
emptyFunctions =
  Functions
    { fnEvalExpr = \_ -> throwErrSt "fnEvalExpr not set"
    , fnReduce = \_ -> throwErrSt "fnReduce not set"
    , reduceUnifyConj = \_ -> throwErrSt "fnReduceMutOnly not set"
    }