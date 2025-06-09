{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}

module Value.Disj where

import qualified AST
import Common (
  BuildASTExpr (..),
  Env,
  TreeOp (isTreeBottom),
 )
import Control.DeepSeq (NFData (..))
import Control.Monad (foldM)
import qualified Data.Set as Set
import GHC.Generics (Generic)

-- | Disjuntion
data Disj t = Disj
  { dsjDefault :: Maybe t
  -- ^ Default value of the disjunction.
  -- It is built from the default disjuncts.
  , dsjDefIndexes :: [Int]
  -- ^ Default disjunct indices.
  , dsjDisjuncts :: [t]
  -- ^ Disjuncts should not have values of type Disj or Bottom.
  -- It should have at least two disjuncts.
  }
  deriving (Eq, Show, Generic, NFData)

-- | Get the default disjuncts from the disjunction.
defDisjunctsFromDisj :: Disj t -> [t]
defDisjunctsFromDisj (Disj{dsjDefIndexes = indexes, dsjDisjuncts = disjuncts}) = map (\i -> disjuncts !! i) indexes

disjunctsToAST :: (Env r s m, BuildASTExpr t) => Bool -> [t] -> m AST.Expression
disjunctsToAST c ds = do
  xs <- mapM (buildASTExpr c) ds
  return $
    foldr1
      (\x acc -> pure $ AST.ExprBinaryOp (pure AST.Disjoin) x acc)
      xs

instance (BuildASTExpr t) => BuildASTExpr (Disj t) where
  buildASTExpr c dj =
    if null (dsjDefault dj)
      then
        disjunctsToAST c (dsjDisjuncts dj)
      else
        disjunctsToAST c (defDisjunctsFromDisj dj)

-- | Convert the default disjuncts to a tree.
defValFromDisj :: (Disj t -> t) -> Disj t -> Maybe t
defValFromDisj toTree d =
  let dfs = defDisjunctsFromDisj d
   in if
        | null dfs -> Nothing
        | length dfs == 1 -> Just (head dfs)
        | otherwise -> Just $ toTree $ emptyDisj{dsjDisjuncts = dfs}

buildDefVal :: (Disj t -> t) -> Disj t -> Disj t
buildDefVal toTree d = d{dsjDefault = defValFromDisj toTree d}

{- | Normalize the disjunction.

1. Flatten the disjunction.
2. Deduplicate the disjuncts.
3. Remove the bottom disjuncts.
4. If the disjunct is left with only one element, return the value.
5. If the disjunct is left with no elements, return the first bottom it found.
-}
normalizeDisj :: (Env r s m, TreeOp t, Eq t, Show t) => (t -> Maybe (Disj t)) -> (Disj t -> t) -> Disj t -> m t
normalizeDisj getDisjFromTree toTree d = do
  flattened <- flattenDisjuncts getDisjFromTree d
  final <- removeUnwantedDisjuncts flattened
  let
    finalDisjs = dsjDisjuncts final
   in
    return
      if
        | null finalDisjs -> head $ filter isTreeBottom (dsjDisjuncts flattened)
        -- When there is only one disjunct and the disjunct is not default, the disjunction is converted to the disjunct.
        | length finalDisjs == 1 && null (dsjDefIndexes final) -> head finalDisjs
        | otherwise -> toTree $ buildDefVal toTree final

{- | Flatten the disjuncts.

Because disjunction operation is associative, we can flatten the disjuncts. The nested disjunctions were like
parenthesized disjunctions. For example, (a | *b) | c | (d | e) = a | *b | c | d | e.

Notice before this step, there is no marked terms in the disjunction. For example, *(a | *b) has been reduced to (a |
*b).

This handles the case where a marked term is a reference. For example the f of the *f | v1 would be <f, f> if we use the
value-default pair. When the value of the f changes to a disjunction like *1 | 2, the flattened disjuncts would be 1 and
2 with the default index of di + 0, where di is the index of the disjunct f. When the value of f changes to 1 | 2, the
flattened disjuncts would be 1 and 2 with the default indexes of di + 0 and di + 1.

It also follows the rules of disjunction operation:
D0: ⟨v1⟩ | ⟨v2⟩         => ⟨v1|v2⟩
D1: ⟨v1, d1⟩ | ⟨v2⟩     => ⟨v1|v2, d1⟩
D2: ⟨v1, d1⟩ | ⟨v2, d2⟩ => ⟨v1|v2, d1|d2⟩

TODO: more efficiency
-}
flattenDisjuncts :: (Env r s m) => (t -> Maybe (Disj t)) -> Disj t -> m (Disj t)
flattenDisjuncts getDisjFromTree (Disj{dsjDefIndexes = idxes, dsjDisjuncts = disjuncts}) = do
  -- Use foldl because the new default indexes are based on the length of the accumulated disjuncts.
  (newIndexes, newDisjs) <- foldM flatten ([], []) (zip [0 ..] disjuncts)
  return $ emptyDisj{dsjDefIndexes = newIndexes, dsjDisjuncts = newDisjs}
 where
  origDefIdxesSet = Set.fromList idxes
  -- Suppose we are processing the ith disjunct, and we have accumulated the disjuncts xs.
  -- If the ith disjunct is not a disjunction, then we can just add it to the disjuncts. We also need to add the index
  -- to the default indexes if it belongs to the default disjunction.
  flatten (accIs, accDs) (origIdx, t) =
    case getDisjFromTree t of
      Just sub -> do
        Disj{dsjDefIndexes = subDefIndexes, dsjDisjuncts = subDisjs} <- flattenDisjuncts getDisjFromTree sub
        let
          -- Add offset to the indexes of the new disjuncts. The offset is the length of the accumulated disjuncts.
          newDefIndexes =
            -- If no sub defaults found for the disjunct but the disjunct is a default disjunct, that means the
            -- disjunct has been flattened to multiple disjuncts.
            if null subDefIndexes && origIdx `Set.member` origDefIdxesSet
              then map (+ length accDs) [0 .. length subDisjs - 1]
              else map (+ length accDs) subDefIndexes
        return (accIs ++ newDefIndexes, accDs ++ subDisjs)
      _ ->
        return
          ( if origIdx `Set.member` origDefIdxesSet
              -- The index of the new disjunct is the length of the accumulated disjuncts.
              then accIs ++ [length accDs]
              else accIs
          , accDs ++ [t]
          )

{- | Remove the duplicate default disjuncts, duplicate disjuncts and bottom disjuncts.

TODO: consider make t an instance of Ord and use Set to remove duplicates.
-}
removeUnwantedDisjuncts :: (Env r s m, Eq t, TreeOp t, Show t) => Disj t -> m (Disj t)
removeUnwantedDisjuncts (Disj{dsjDefIndexes = dfIdxes, dsjDisjuncts = disjuncts}) = do
  let (newIndexes, newDisjs) = foldl go ([], []) (zip [0 ..] disjuncts)
   in return $ emptyDisj{dsjDefIndexes = newIndexes, dsjDisjuncts = newDisjs}
 where
  defValues = map (disjuncts !!) dfIdxes
  origDefIdxesSet = Set.fromList dfIdxes

  go (accIs, accXs) (idx, x) =
    let
      notAddedDisj = not (x `elem` accXs)
      -- If the disjunct is equal to the default value. Note that it does not mean the disjunct is the original default
      -- value.
      isValEqDef = x `elem` defValues
      -- The disjunct is kept if all of the following conditions are met:
      -- 1. it is not a bottom disjunct.
      -- 2. it is not added before
      -- 3. it is not a default value OR it is one of the default disjuncts and its index is in the original default
      -- indexes.
      -- The second condition makes sure the relative order of the default disjuncts is kept.
      -- For example, *b | c | a | b | *a should be reduced to <b | c | a, 0|2>.
      keepDisjunct = not (isTreeBottom x) && notAddedDisj && (not isValEqDef || idx `Set.member` origDefIdxesSet)
      -- The disjunct is default if it is one of the default disjuncts and it is not seen before.
      isDefIndex = keepDisjunct && isValEqDef
     in
      -- Add the current disjunct index to the default indexes if condition is met.
      ( if isDefIndex then accIs ++ [length accXs] else accIs
      , if keepDisjunct then accXs ++ [x] else accXs
      )

emptyDisj :: Disj t
emptyDisj = Disj{dsjDefault = Nothing, dsjDefIndexes = [], dsjDisjuncts = []}