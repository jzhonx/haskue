{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Unify (unify) where

import Control.Monad.Except (MonadError, runExceptT, throwError)
import Control.Monad.State.Strict (MonadState, gets, modify, runState)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Value (Value (..))

-- | Vertex represents a vertex in the graph. It should only be built when needed.
data Vertex = Vertex
  { getID :: Int,
    getOrigValue :: Maybe Value,
    getEdges :: Map.Map String Value
  }

data TraverseState = TraverseState
  { getVisisted :: IntMap.IntMap Bool
  }

data UnifyState = UnifyState
  { getTraverseState1 :: TraverseState,
    getTraverseState2 :: TraverseState,
    getLastID :: Int
  }

unify :: (MonadError String m) => Value -> Value -> m Value
unify val1 val2 =
  let (res, _) = runState (runExceptT (unify' val1 val2)) (UnifyState (TraverseState IntMap.empty) (TraverseState IntMap.empty) 0)
   in case res of
        Left err -> throwError err
        Right val -> return val

unify' :: (MonadState UnifyState m, MonadError String m) => Value -> Value -> m Value
unify' val1 val2 = do
  v1 <- buildVertex val1
  v2 <- buildVertex val2
  vertex <- unifyVertices v1 v2
  return $ vertexToValue vertex

-- | buildVertex builds a vertex from a value.
buildVertex :: (MonadState UnifyState m, MonadError String m) => Value -> m Vertex
buildVertex val = do
  curID <- gets getLastID
  modify (\s -> s {getLastID = curID + 1})
  case val of
    Struct xs -> return $ Vertex curID (Just val) (Map.fromList xs)
    _ -> return $ Vertex curID (Just val) Map.empty

vertexToValue :: Vertex -> Value
vertexToValue (Vertex _ (Just v) _) = v
vertexToValue (Vertex _ Nothing edges) = Struct (Map.toList edges)

unifyVertices :: (MonadState UnifyState m, MonadError String m) => Vertex -> Vertex -> m Vertex
unifyVertices root1@(Vertex _ (Just val1) edges1) root2@(Vertex _ (Just val2) edges2) =
  case (val1, val2) of
    (Bottom _, _) -> return root1
    (String x, String y) -> return $ if x == y then root1 else newBottomVertex "strings mismatch"
    (Int x, Int y) -> return $ if x == y then root1 else newBottomVertex "ints mismatch"
    (Struct _, Struct _) ->
      let labels1Set = Map.keysSet edges1
          labels2Set = Map.keysSet edges2
          interLabels = Set.intersection labels1Set labels2Set
          disjointVertices1 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) edges1
          disjointVertices2 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) edges2
       in sequence
            ( Set.foldr
                ( \key acc ->
                    let valx = edges1 Map.! key
                        valy = edges2 Map.! key
                     in fmap
                          (\vertex -> (key, vertexToValue vertex))
                          ( do
                              vx <- buildVertex valx
                              vy <- buildVertex valy
                              unifyVertices vx vy
                          )
                          : acc
                )
                []
                interLabels
            )
            >>= ( \vs -> do
                    let newEdges = Map.unions [disjointVertices1, disjointVertices2, Map.fromList vs]
                    curID <- gets getLastID
                    modify (\s -> s {getLastID = curID + 1})
                    return $ Vertex curID Nothing newEdges
                )
    (Disjunction _ disjuncts, _) -> do
      xs <- mapM (\v -> buildVertex v >>= (`unifyVertices` root2)) disjuncts
      let xs' = filter (\(Vertex _ val _) -> case val of Just (Bottom _) -> False; Nothing -> False; _ -> True) xs
      case xs' of
        [] -> return $ newBottomVertex "values mismatch"
        [x'] -> return x'
        _ -> do
          curID <- gets getLastID
          modify (\s -> s {getLastID = curID + 1})
          return $ Vertex curID (Just Disjunction {getDefault = Nothing, getDisjuncts = map vertexToValue xs'}) Map.empty
    (_, Bottom _) -> unifyVertices root2 root1
    (_, Disjunction _ _) -> unifyVertices root2 root1
    _ -> return $ newBottomVertex "values mismatch"
  where
    newBottomVertex msg = Vertex (negate 1) (Just $ Bottom msg) Map.empty
unifyVertices _ _ = throwError "unifyVertices: vertices mismatch"
