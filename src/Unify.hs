{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
    getValue :: Value,
    getEdges :: Map.Map String Value
  }

instance Show Vertex where
  show (Vertex vid val edges) = "Vertex " ++ show vid ++ " " ++ show val ++ " " ++ show edges

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
  return $ getValue vertex

-- | buildVertex builds a vertex from a value.
buildVertex :: (MonadState UnifyState m, MonadError String m) => Value -> m Vertex
buildVertex val = do
  newID <- allocateID
  case val of
    Struct xs ->
      let m = Map.fromListWith (\x y -> do valx <- x; valy <- y; unify valx valy) (map (\(k, v) -> (k, return v)) xs)
       in do
            m' <- sequence m
            return $ Vertex newID val m'
    _ -> return $ Vertex newID val Map.empty

edgesToValue :: Map.Map String Value -> Value
edgesToValue edges = Struct (Map.toList edges)

unifyVertices :: (MonadState UnifyState m, MonadError String m) => Vertex -> Vertex -> m Vertex
unifyVertices root1@(Vertex _ val1 edges1) root2@(Vertex _ val2 edges2) =
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
       in do
            valList <-
              sequence
                ( Set.foldr
                    ( \key acc ->
                        let valx = edges1 Map.! key
                            valy = edges2 Map.! key
                            unified = do vx <- buildVertex valx; vy <- buildVertex valy; unifyVertices vx vy
                         in fmap
                              ( \vertex ->
                                  let val = getValue vertex
                                   in case val of
                                        Bottom _ -> Left val
                                        _ -> Right (key, val)
                              )
                              unified
                              : acc
                    )
                    []
                    interLabels
                )
            let vs = sequence valList
            case vs of
              Left (Bottom msg) -> return $ newBottomVertex msg
              Left _ -> throwError "unifyVertices: impossible"
              Right vs' ->
                do
                  let newEdges = Map.unions [disjointVertices1, disjointVertices2, Map.fromList vs']
                  newID <- allocateID
                  return $ Vertex newID (edgesToValue newEdges) newEdges
    (Disjunction _ disjuncts, _) -> do
      xs <- mapM (\v -> buildVertex v >>= (`unifyVertices` root2)) disjuncts
      let xs' = filter (\(Vertex _ val _) -> case val of (Bottom _) -> False; _ -> True) xs
      case xs' of
        [] -> return $ newBottomVertex "values mismatch"
        [x'] -> return x'
        _ -> do
          curID <- gets getLastID
          modify (\s -> s {getLastID = curID + 1})
          return $ Vertex curID (Disjunction {getDefault = Nothing, getDisjuncts = map getValue xs'}) Map.empty
    (_, Bottom _) -> unifyVertices root2 root1
    (_, Disjunction _ _) -> unifyVertices root2 root1
    _ -> return $ newBottomVertex "values mismatch"
  where
    newBottomVertex msg = Vertex (negate 1) (Bottom msg) Map.empty

allocateID :: (MonadState UnifyState m) => m Int
allocateID = do
  curID <- gets getLastID
  modify (\s -> s {getLastID = curID + 1})
  return curID
