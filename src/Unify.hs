{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unify (unify) where

import qualified AST
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Text.Printf (printf)
import Value

unify :: (EvalEnv m) => TreeNode -> TreeNode -> m TreeNode
unify t1 t2 = case (t1, t2) of
  (TNLeaf l1, TNLeaf l2) -> case (trfValue l1, trfValue l2) of
    (Bottom _, _) -> return t1
    (Top, _) -> return t2
    (Stub, _) -> return t2
    (String x, String y) ->
      return $ if x == y then t1 else mkTreeLeaf $ Bottom $ printf "strings mismatch: %s != %s" x y
    (Int x, Int y) ->
      return $ if x == y then t1 else mkTreeLeaf $ Bottom $ printf "ints mismatch: %d != %d" x y
    (Bool x, Bool y) ->
      return $ if x == y then t1 else mkTreeLeaf $ Bottom $ printf "bools mismatch: %s != %s" (show x) (show y)
    (Null, Null) -> return t1
    (_, Top) -> unify t2 t1
    (_, Stub) -> unify t2 t1
    (_, Bottom _) -> unify t2 t1
    _ -> return $ mkTreeLeaf $ Bottom $ printf "values not unifiable: %s, %s" (show t1) (show t2)
  (TNScope s1, TNScope s2) -> unifyStructs s1 s2
  (TNDisj _, _) -> unifyDisjunctions t1 t2
  (_, TNDisj _) -> unifyDisjunctions t2 t1
  _ -> return $ mkTreeLeaf $ Bottom $ printf "values not unifiable: %s, %s" (show t1) (show t2)

unifyStructs :: (EvalEnv m) => TNScope -> TNScope -> m TreeNode
unifyStructs s1 s2 = do
  valList <- unifyIntersectionLabels
  let vs = sequence valList
  case vs of
    -- If any of the values is Bottom, then the whole struct is Bottom.
    Left b@(TNLeaf (TreeLeaf (Bottom _))) -> return b
    Left _ -> throwError "unifyVertices: impossible"
    Right nodes ->
      do
        let newEdges = Map.unions [disjointVertices1, disjointVertices2, Map.fromList nodes]
        return $ fieldsToScope newEdges
  where
    (fields1, fields2) = (trsSubs s1, trsSubs s2)
    labels1Set = Map.keysSet fields1
    labels2Set = Map.keysSet fields2
    interLabels = Set.intersection labels1Set labels2Set
    disjointVertices1 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) fields1
    disjointVertices2 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) fields2
    processUnified :: String -> TreeNode -> Either TreeNode (String, TreeNode)
    processUnified key node = case node of
      (TNLeaf (TreeLeaf (Bottom _))) -> Left node
      _ -> Right (key, node)
    unifyIntersectionLabels :: (EvalEnv m) => m [Either TreeNode (String, TreeNode)]
    unifyIntersectionLabels =
      sequence
        ( Set.foldr
            ( \key acc ->
                let valx = fields1 Map.! key
                    valy = fields2 Map.! key
                    unified = unify valx valy
                 in fmap (processUnified key) unified : acc
            )
            []
            interLabels
        )

    fieldsToScope :: Map.Map String TreeNode -> TreeNode
    fieldsToScope subs =
      TNScope $
        TreeScope
          { trsOrdLabels = [],
            trsVars = Set.empty,
            trsConcretes = Set.empty,
            trsSubs = subs
          }

unifyDisjunctions :: (EvalEnv m) => TreeNode -> TreeNode -> m TreeNode
unifyDisjunctions t1 t2 = case (t1, t2) of
  (TNDisj dj1, TNDisj dj2) -> case (dj1, dj2) of
    -- this is U0 rule, <v1> & <v2> => <v1&v2>
    (TreeDisj [] ds1, TreeDisj [] ds2) -> do
      ds <- mapM (`unifyValues` ds2) ds1
      disjunctionFromValues [] ds
    -- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
    (TreeDisj df1 ds1, TreeDisj [] ds2) -> do
      df <- mapM (`unifyValues` ds2) df1
      ds <- mapM (`unifyValues` ds2) ds1
      disjunctionFromValues df ds
    -- this is also the U1 rule.
    (TreeDisj [] _, TreeDisj _ _) -> unifyDisjunctions t2 t1
    -- this is U2 rule, <v1,d1> & <v2,d2> => <v1&v2,d1&d2>
    (TreeDisj df1 ds1, TreeDisj df2 ds2) -> do
      df <- mapM (`unifyValues` df2) df1
      ds <- mapM (`unifyValues` ds2) ds1
      disjunctionFromValues df ds
  -- this is the case for a disjunction unified with a value.
  (TNDisj (TreeDisj [] ds), val) -> do
    ds2 <- unifyValues val ds
    disjunctionFromValues [] [ds2]
  (TNDisj (TreeDisj df ds), val) -> do
    df2 <- unifyValues val df
    ds2 <- unifyValues val ds
    disjunctionFromValues [df2] [ds2]
  (_, _) -> throwError $ printf "unifyDisjunctions: impossible unification, %s, %s" (show t1) (show t2)

unifyValues :: (EvalEnv m) => TreeNode -> [TreeNode] -> m [TreeNode]
unifyValues val = mapM (`unify` val)

disjunctionFromValues :: (MonadError String m) => [[TreeNode]] -> [[TreeNode]] -> m TreeNode
disjunctionFromValues df ds = f (concatFilter df) (concatFilter ds)
  where
    concatFilter :: [[TreeNode]] -> [TreeNode]
    concatFilter xs = case filter
      ( \x ->
          case x of
            TNLeaf (TreeLeaf (Bottom _)) -> False
            _ -> True
      )
      (concat xs) of
      [] -> [mkTreeLeaf $ Bottom "empty disjuncts"]
      xs' -> xs'
    f :: (MonadError String m) => [TreeNode] -> [TreeNode] -> m TreeNode
    f [] [] = emptyDisjunctError [] []
    f [TNLeaf (TreeLeaf (Bottom _))] [TNLeaf (TreeLeaf (Bottom _))] = return $ mkTreeLeaf $ Bottom "empty disjuncts"
    f df' [TNLeaf (TreeLeaf (Bottom _))] = return $ TNDisj $ TreeDisj [] df'
    f [TNLeaf (TreeLeaf (Bottom _))] ds' = return $ TNDisj $ TreeDisj [] ds'
    f df' ds' = return $ TNDisj $ TreeDisj df' ds'
    emptyDisjunctError :: (MonadError String m) => [TreeNode] -> [TreeNode] -> m TreeNode
    emptyDisjunctError df' ds' =
      throwError $
        "disjunctionFromUnifyResult failed because of empty disjuncts, df: "
          ++ show df'
          ++ ", ds: "
          ++ show ds'
