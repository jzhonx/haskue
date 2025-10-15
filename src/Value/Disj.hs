{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
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
  }
  deriving (Generic)

-- | Get the default disjuncts from the disjunction.
defDisjunctsFromDisj :: Disj -> [Tree]
defDisjunctsFromDisj (Disj{dsjDefIndexes = indexes, dsjDisjuncts = disjuncts}) = map (\i -> disjuncts !! i) indexes

-- buildDefVal :: (Disj -> Tree) -> Disj -> Disj
-- buildDefVal toTree d = d{dsjDefault = defValFromDisj toTree d}

emptyDisj :: Disj
emptyDisj = Disj{dsjDefIndexes = [], dsjDisjuncts = []}