{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Unify (unify) where

import Control.Monad.Except (MonadError, runExceptT, throwError)
import Control.Monad.State.Strict (MonadState, gets, modify, runState)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Value (Value (..))

data Vertex = Vertex
  { getID :: Int,
    getOrigValue :: Maybe Value,
    getEdges :: Map.Map String Vertex
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

-- The algorithm of unification is as follows:
unify' :: (MonadState UnifyState m, MonadError String m) => Value -> Value -> m Value
unify' val1 val2 = do
  v1 <- buildVertex val1
  v2 <- buildVertex val2
  vertex <- unifyVertices v1 v2
  return $ vertexToValue vertex

buildVertex :: (MonadState UnifyState m, MonadError String m) => Value -> m Vertex
buildVertex val@(String _) = do
  curID <- gets getLastID
  modify (\s -> s {getLastID = curID + 1})
  return $ Vertex curID (Just val) Map.empty
buildVertex val@(Int _) = do
  curID <- gets getLastID
  modify (\s -> s {getLastID = curID + 1})
  return $ Vertex curID (Just val) Map.empty
buildVertex val@(Struct xs) = do
  curID <- gets getLastID
  modify (\s -> s {getLastID = curID + 1})
  edges <- sequence $ Map.fromList (map (\(label, v) -> (label, buildVertex v)) xs)
  return $ Vertex curID (Just val) edges

vertexToValue :: Vertex -> Value
vertexToValue (Vertex _ (Just v) _) = v
vertexToValue (Vertex _ Nothing edges) = Struct (map (\(label, v) -> (label, vertexToValue v)) (Map.toList edges))

unifyVertices :: (MonadState UnifyState m, MonadError String m) => Vertex -> Vertex -> m Vertex
unifyVertices root1 root2 =
  case comparePrim v1 v2 of
    Right True -> return root1
    Right False ->
      let edges1 = getEdges root1
          edges2 = getEdges root2
          labels1Set = Map.keysSet edges1
          labels2Set = Map.keysSet edges2
          interLabels = Set.intersection labels1Set labels2Set
          disjointVertices1 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) edges1
          disjointVertices2 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) edges2
       in sequence
            ( Set.foldr
                ( \key acc ->
                    let vx = edges1 Map.! key
                        vy = edges2 Map.! key
                     in fmap (key,) (unifyVertices vx vy) : acc
                )
                []
                interLabels
            )
            >>= \vs -> do
              let newEdges = Map.unions [disjointVertices1, disjointVertices2, Map.fromList vs]
              curID <- gets getLastID
              modify (\s -> s {getLastID = curID + 1})
              return $ Vertex curID Nothing newEdges
    Left err -> throwError err
  where
    v1 = getOrigValue root1
    v2 = getOrigValue root2

comparePrim :: (MonadError String m) => Maybe Value -> Maybe Value -> m Bool
comparePrim (Just v1) (Just v2) = f v1 v2
  where
    f (String s1) (String s2) =
      if s1 == s2
        then return True
        else throwError $ "strings " ++ s1 ++ " and " ++ s2 ++ " are not equal"
    f (Int x) (Int y) =
      if x == y
        then return True
        else throwError $ "integers " ++ show x ++ " and " ++ show y ++ " are not equal"
    f (Struct _) (Struct _) = return False
    f _ _ = throwError "primitive values mismatch"
comparePrim _ _ = throwError "values does not exist"
