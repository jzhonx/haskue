{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.DisjoinOp where

import Control.DeepSeq (NFData (..))
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)

data DisjTerm t = DisjTerm
  { dstMarked :: Bool
  , dstValue :: t
  }
  deriving (Eq, Show, Functor, Generic, NFData)

{- | DisjoinOp is used to handle reference disjuncts, so that when values of references change, the new disjunction can
be created correctly.

Its value should be a Disj or other single value.
-}
data DisjoinOp t = DisjoinOp
  { djoTerms :: Seq.Seq (DisjTerm t)
  , djoValue :: Maybe t
  }
  deriving (Eq, Show, Generic, NFData)
