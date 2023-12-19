{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unify (unify) where

import           Control.Monad.Except       (MonadError, runExceptT, throwError)
import           Control.Monad.State.Strict (MonadState, runState)
import qualified Data.IntMap.Strict         as IntMap
import qualified Data.Map.Strict            as Map
import qualified Data.Set                   as Set
import           Value                      (Value (..))

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
        Left err  -> throwError err
        Right val -> return val

edgesToValue :: Map.Map String Value -> Value
edgesToValue edges = Struct (Map.keys edges) edges Set.empty

unify' :: (MonadState UnifyState m, MonadError String m) => Value -> Value -> m Value
unify' val1 val2 = case (val1, val2) of
  (Bottom _, _) -> return val1
  (String x, String y) -> return $ if x == y then val1 else Bottom "strings mismatch"
  (Int x, Int y) -> return $ if x == y then val1 else Bottom "ints mismatch"
  (Struct {}, Struct {}) -> unifyStructs val1 val2
  (Disjunction _ _, _) -> unifyDisjunctions val1 val2
  (_, Bottom _) -> unify' val2 val1
  (_, Disjunction _ _) -> unify' val2 val1
  _ -> return $ Bottom "values not unifiable"

unifyStructs :: (MonadState UnifyState m, MonadError String m) => Value -> Value -> m Value
unifyStructs (Struct _ edges1 _) (Struct _ edges2 _) = do
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
      _        -> Right (key, val)
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
-- this is U0 rule, <v1> & <v2> => <v1&v2>
unifyDisjunctions (Disjunction [] ds1) (Disjunction [] ds2) = do
  ds <- mapM (`unifyValues` ds2) ds1
  disjunctionFromValues [] ds

-- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
unifyDisjunctions (Disjunction df1 ds1) (Disjunction [] ds2) = do
  df <- mapM (`unifyValues` ds2) df1
  ds <- mapM (`unifyValues` ds2) ds1
  disjunctionFromValues df ds

-- this is also the U1 rule.
unifyDisjunctions d1@(Disjunction [] _) d2@(Disjunction _ _) = unifyDisjunctions d2 d1
-- this is U2 rule, <v1,d1> & <v2,d2> => <v1&v2,d1&d2>
unifyDisjunctions (Disjunction df1 ds1) (Disjunction df2 ds2) = do
  df <- mapM (`unifyValues` df2) df1
  ds <- mapM (`unifyValues` ds2) ds1
  disjunctionFromValues df ds

-- this is the case for a disjunction unified with a value.
unifyDisjunctions (Disjunction [] ds) val = do
  ds' <- unifyValues val ds
  disjunctionFromValues [] [ds']
unifyDisjunctions (Disjunction df ds) val = do
  df' <- unifyValues val df
  ds' <- unifyValues val ds
  disjunctionFromValues [df'] [ds']
unifyDisjunctions d1 d2 =
  throwError $ "unifyDisjunctions: impossible unification, d1: " ++ show d1 ++ ", d2: " ++ show d2

unifyValues :: (MonadState UnifyState m, MonadError String m) => Value -> [Value] -> m [Value]
unifyValues val = mapM (`unify'` val)

disjunctionFromValues :: (MonadError String m) => [[Value]] -> [[Value]] -> m Value
disjunctionFromValues df ds = f (concatFilter df) (concatFilter ds)
  where
    concatFilter :: [[Value]] -> [Value]
    concatFilter xs = case filter (\x -> case x of Bottom _ -> False; _ -> True) (concat xs) of
      []  -> [Bottom "empty disjuncts"]
      xs' -> xs'
    f :: (MonadError String m) => [Value] -> [Value] -> m Value
    f [] []                 = emptyDisjunctError [] []
    f [Bottom _] [Bottom _] = return $ Bottom "empty disjuncts"
    f df' [Bottom _]        = return $ Disjunction [] df'
    f [Bottom _] ds'        = return $ Disjunction [] ds'
    f df' ds'               = return $ Disjunction df' ds'
    emptyDisjunctError :: (MonadError String m) => [Value] -> [Value] -> m Value
    emptyDisjunctError df' ds' =
      throwError $
        "disjunctionFromUnifyResult failed because of empty disjuncts, df: "
          ++ show df'
          ++ ", ds: "
          ++ show ds'
