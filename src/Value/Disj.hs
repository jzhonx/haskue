{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}

module Value.Disj where

import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

-- | Disjuntion
data Disj = Disj
  { dsjDefault :: Maybe Tree
  -- ^ Default value of the disjunction.
  -- It is built from the default disjuncts.
  , dsjDefIndexes :: [Int]
  -- ^ Default disjunct indices.
  , dsjDisjuncts :: [Tree]
  -- ^ Disjuncts should not have values of type Disj or Bottom.
  -- It should have at least two disjuncts.
  }
  deriving (Generic)

-- | Get the default disjuncts from the disjunction.
defDisjunctsFromDisj :: Disj -> [Tree]
defDisjunctsFromDisj (Disj{dsjDefIndexes = indexes, dsjDisjuncts = disjuncts}) = map (\i -> disjuncts !! i) indexes

-- | Convert the default disjuncts to a tree.
defValFromDisj :: (Disj -> Tree) -> Disj -> Maybe Tree
defValFromDisj toTree d =
  let dfs = defDisjunctsFromDisj d
   in if
        | null dfs -> Nothing
        | length dfs == 1 -> Just (head dfs)
        | otherwise -> Just $ toTree $ emptyDisj{dsjDisjuncts = dfs}

buildDefVal :: (Disj -> Tree) -> Disj -> Disj
buildDefVal toTree d = d{dsjDefault = defValFromDisj toTree d}

emptyDisj :: Disj
emptyDisj = Disj{dsjDefault = Nothing, dsjDefIndexes = [], dsjDisjuncts = []}