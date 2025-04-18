{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.DisjoinOp where

data DisjTerm t = DisjTerm
  { dstMarked :: Bool
  , dstValue :: t
  }
  deriving (Eq, Show, Functor)

{- | DisjoinOp is used to handle reference disjuncts, so that when values of references change, the new disjunction can
be created correctly.

Its value should be a Disj or other single value.
-}
data DisjoinOp t = DisjoinOp
  { djoTerms :: [DisjTerm t]
  , djoValue :: Maybe t
  }
  deriving (Eq, Show)
