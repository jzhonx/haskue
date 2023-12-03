{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unify (unify) where

import Control.Monad.Except (MonadError, runExceptT, throwError)
import Control.Monad.State.Strict (MonadState, gets, modify, runState)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Value
  ( Disjunct (..),
    Value (..),
    fromDisjunct,
  )

data TraverseState = TraverseState
  { getVisisted :: IntMap.IntMap Bool
  }

data UnifyState = UnifyState
  { getTraverseState1 :: TraverseState,
    getTraverseState2 :: TraverseState
  }

unify :: (MonadError String m) => Value -> Value -> m Value
unify val1 val2 =
  let (res, _) = runState (runExceptT (unify' val1 val2)) (UnifyState (TraverseState IntMap.empty) (TraverseState IntMap.empty))
   in case res of
        Left err -> throwError err
        Right val -> return val

edgesToValue :: Map.Map String Value -> Value
edgesToValue edges = Struct (Map.keys edges) edges

unify' :: (MonadState UnifyState m, MonadError String m) => Value -> Value -> m Value
unify' val1 val2 = case (val1, val2) of
  (Bottom _, _) -> return val1
  (String x, String y) -> return $ if x == y then val1 else Bottom "strings mismatch"
  (Int x, Int y) -> return $ if x == y then val1 else Bottom "ints mismatch"
  (Struct _ _, Struct _ _) -> unifyStructs val1 val2
  (Disjunction _, _) -> unifyDisjunctions val1 val2
  (_, Bottom _) -> unify' val2 val1
  (_, Disjunction _) -> unify' val2 val1
  _ -> return $ Bottom "values not unifiable"

unifyStructs :: (MonadState UnifyState m, MonadError String m) => Value -> Value -> m Value
unifyStructs (Struct _ edges1) (Struct _ edges2) = do
  valList <- unifyIntersectionLabels
  let vs = sequence valList
  case vs of
    -- If any of the values is Bottom, then the whole struct is Bottom.
    Left (Bottom msg) -> return $ Bottom msg
    Left _ -> throwError "unifyVertices: impossible"
    Right vs' ->
      do
        let newEdges = Map.unions [disjointVertices1, disjointVertices2, Map.fromList vs']
        return $ edgesToValue newEdges
  where
    labels1Set = Map.keysSet edges1
    labels2Set = Map.keysSet edges2
    interLabels = Set.intersection labels1Set labels2Set
    disjointVertices1 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) edges1
    disjointVertices2 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) edges2
    processUnified :: String -> Value -> Either Value (String, Value)
    processUnified key val = case val of
      Bottom _ -> Left val
      _ -> Right (key, val)
    unifyIntersectionLabels =
      sequence
        ( Set.foldr
            ( \key acc ->
                let valx = edges1 Map.! key
                    valy = edges2 Map.! key
                    unified = unify' valx valy
                 in fmap (processUnified key) unified : acc
            )
            []
            interLabels
        )
unifyStructs _ _ = throwError "unifyStructs: impossible"

unifyDisjunctions :: (MonadState UnifyState m, MonadError String m) => Value -> Value -> m Value
unifyDisjunctions (Disjunction ds) val2 = do
  xs <- mapM (\v -> fromDisjunct v `unify'` val2) ds
  let xs' = filter (\case (Bottom _) -> False; _ -> True) xs
  case xs' of
    [] -> return $ Bottom "values mismatch"
    [x'] -> return x'
    _ -> do
      return $ Disjunction (map Disjunct xs')
unifyDisjunctions _ _ = throwError "unifyDisjunctions: impossible"
