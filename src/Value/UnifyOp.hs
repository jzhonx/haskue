{-# LANGUAGE DeriveGeneric #-}

module Value.UnifyOp where

import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Val

{- | UnifyOp is commutative, associative, and idempotent.

The op tree can be flattened to a list of conjuncts.

It is used to handle reference unifications, so that when values of references change, the new unification can be
created correctly.
-}
data UnifyOp = UnifyOp
  { isEmbedUnify :: Bool
  -- ^ Indicates whether this unify op is for embed unification, which means the first argument is a struct value and
  -- the rest are embeddings of the struct.
  , conjs :: Seq.Seq Val
  }
  deriving (Generic)
