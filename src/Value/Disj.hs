{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Value.Disj where

import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

{- | Disjuntion represents the result of disjuncting values.

It is only created during reducing a disjunction operation (DisjOp).
-}
data Disj = Disj
  { dsjDefIndexes :: [Int]
  -- ^ Default disjunct indices.
  , dsjDisjuncts :: [Tree]
  -- ^ Disjuncts should not have values of type Disj or Bottom.
  -- It should have at least two disjuncts.
  -- It is a result of reducing a disjunction operation. Each time a reduction is done, a new disjunct is created. It
  -- means that the dependency should be cleared before reducing a disjunction operation.
  }
  deriving (Generic)

-- | Get the default disjuncts from the disjunction.
defDisjunctsFromDisj :: Disj -> [Tree]
defDisjunctsFromDisj (Disj{dsjDefIndexes = indexes, dsjDisjuncts = disjuncts}) = map (\i -> disjuncts !! i) indexes

emptyDisj :: Disj
emptyDisj = Disj{dsjDefIndexes = [], dsjDisjuncts = []}