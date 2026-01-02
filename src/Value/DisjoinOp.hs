{-# LANGUAGE DeriveGeneric #-}

module Value.DisjoinOp where

import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Val

{- | DisjoinOp is used to handle reference disjuncts, so that when values of references change, the new disjunction can
be created correctly.

Its value should be a Disj or other single value.
-}
newtype DisjoinOp = DisjoinOp
  { djoTerms :: Seq.Seq DisjTerm
  }
  deriving (Generic)

data DisjTerm = DisjTerm
  { dstMarked :: Bool
  , dstValue :: Val
  }
  deriving (Generic)
