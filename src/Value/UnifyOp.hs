{-# LANGUAGE DeriveGeneric #-}

module Value.UnifyOp where

import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

{- | UnifyOp is commutative, associative, and idempotent.

The op tree can be flattened to a list of conjuncts.

It is used to handle reference unifications, so that when values of references change, the new unification can be
created correctly.
-}
newtype UnifyOp = UnifyOp {ufConjuncts :: Seq.Seq Tree}
  deriving (Generic)

emptyUnifyOp :: UnifyOp
emptyUnifyOp = UnifyOp Seq.empty