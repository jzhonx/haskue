{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unify (unify) where

import qualified AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (ask)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Path (BinOpDirect (..), Selector (BinOpSelector, StringSelector))
import Text.Printf (printf)
import Tree

unify :: (EvalEnv m) => Tree -> Tree -> TreeCursor -> m TreeCursor
unify t1 t2 tc = do
  node <- unifyToTree t1 t2 tc
  return (node, snd tc)

unifyToTree :: (EvalEnv m) => Tree -> Tree -> TreeCursor -> m Tree
unifyToTree t1 t2 = unifyWithDir (L, t1) (R, t2)

unifyWithDir :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
unifyWithDir dt1@(d1, t1) dt2@(d2, t2) tc = do
  dump $
    printf
      ("unifying, path: %s:, %s:\n%s" ++ "\n" ++ "with %s:\n%s")
      (show $ pathFromTC tc)
      (show d1)
      (show t1)
      (show d2)
      (show t2)
  res <- case (treeNode t1, treeNode t2) of
    (TNAtom l1, _) -> unifyLeaf (d1, l1, t1) dt2 tc
    (_, TNAtom l2) -> unifyLeaf (d2, l2, t2) dt1 tc
    (TNDisj dj1, _) -> unifyDisj (d1, dj1, t1) (d2, t2) tc
    (_, TNDisj dj2) -> do
      dump $ printf "unifying, sec: %s" (show t1)
      unifyDisj (d2, dj2, t2) (d1, t1) tc
    (TNScope s1, TNScope s2) -> unifyStructs s1 s2 tc
    (TNScope _, _) -> unifyOther dt2 dt1 tc
    _ -> unifyOther dt1 dt2 tc
  dump $ printf ("unifying, path: %s:, res:\n%s") (show $ pathFromTC tc) (show res)
  return res

{- |
parTC points to the bin op node.
-}
unifyLeaf :: (EvalEnv m) => (BinOpDirect, TNAtom, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
unifyLeaf (d1, l1, t1) dt2@(d2, t2) parTC = do
  case (trAmAtom l1, treeNode t2) of
    (Bottom _, _) -> returnTree $ TNAtom l1
    (Top, _) -> returnTree (treeNode t2)
    (String x, TNAtom s) -> case trAmAtom s of
      String y -> returnTree $ if x == y then TNAtom l1 else mismatch x y
      _ -> notUnifiable dt1 dt2
    (Int x, TNAtom s) -> case trAmAtom s of
      Int y -> returnTree $ if x == y then TNAtom l1 else mismatch x y
      _ -> notUnifiable dt1 dt2
    (Bool x, TNAtom s) -> case trAmAtom s of
      Bool y -> returnTree $ if x == y then TNAtom l1 else mismatch x y
      _ -> notUnifiable dt1 dt2
    (Null, TNAtom s) -> case trAmAtom s of
      Null -> returnTree $ TNAtom l1
      _ -> notUnifiable dt1 dt2
    (_, TNConstraint c) ->
      if l1 == trCnAtom c
        then returnTree (TNConstraint c)
        else
          return $
            mkTreeAtom
              (Bottom $ printf "values mismatch: %s != %s" (show l1) (show $ trCnAtom c))
              (treeOrig (fst parTC))
    (_, TNDisj dj2) -> do
      dump $ printf "unifyLeaf: TNDisj %s, %s" (show t2) (show t1)
      unifyDisj (d2, dj2, t2) (d1, t1) parTC
    (_, TNUnaryOp _) -> procOther
    (_, TNBinaryOp op) -> case trbRep op of
      -- Unifying an atom with a marked disjunction will not get the same atom. So we do not create a constraint.
      -- Another way is to add a field in Constraint to store whether the constraint is created from a marked
      -- disjunction.
      AST.Disjunction -> unifyOther dt2 dt1 parTC
      _ -> procOther
    (_, TNRefCycleVar) -> procOther
    (_, TNLink _) -> procOther
    _ -> notUnifiable dt1 dt2
 where
  dt1 = (d1, t1)

  returnTree :: (EvalEnv m) => TreeNode -> m Tree
  returnTree n = return $ substTreeNode n (fst parTC)

  mismatch :: (Show a) => a -> a -> TreeNode
  mismatch x y = TNAtom . TreeAtom $ Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

  procOther :: (EvalEnv m) => m Tree
  procOther = do
    Config{cfCreateCnstr = cc} <- ask
    if cc
      then mkCnstr (d1, l1) dt2 parTC
      else unifyOther dt2 dt1 parTC

mkCnstr :: (EvalEnv m) => (BinOpDirect, TNAtom) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
mkCnstr (_, l1) (_, t2) tc = return $ substTreeNode (TNConstraint $ mkTNConstraint l1 t2 unify) (fst tc)

unifyOther :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
unifyOther dt1@(d1, t1) dt2@(d2, t2) tc = case (treeNode t1, treeNode t2) of
  (TNUnaryOp _, _) -> evalOrDelay
  (TNBinaryOp _, _) -> evalOrDelay
  (TNConstraint c1, _) ->
    return $ substTreeNode (TNConstraint $ updateTNConstraintCnstr dt2 unify c1) (fst tc)
  -- According to the spec,
  -- A field value of the form r & v, where r evaluates to a reference cycle and v is a concrete value, evaluates to v.
  -- Unification is idempotent and unifying a value with itself ad infinitum, which is what the cycle represents,
  -- results in this value. Implementations should detect cycles of this kind, ignore r, and take v as the result of
  -- unification.
  -- We can just return the second value.
  (TNRefCycleVar, _) -> return t2
  (TNLink l, _) -> do
    substTC1 <- substLinkTC l $ mkSubTC (BinOpSelector d1) t1 tc
    case treeNode (fst substTC1) of
      TNLink _ -> do
        dump $ printf "unifyOther: TNLink %s, is still evaluated to TNLink %s" (show t1) (show $ fst substTC1)
        mkUnification dt1 dt2 (fst tc)
      _ -> unifyWithDir (d1, fst substTC1) dt2 tc
  _ -> notUnifiable dt1 dt2
 where
  evalOrDelay :: (EvalEnv m) => m Tree
  evalOrDelay =
    let subTC = mkSubTC (BinOpSelector d1) t1 tc
     in do
          x <- evalTC subTC
          dump $
            printf "unifyOther, path: %s, %s is evaluated to %s" (show $ pathFromTC tc) (show t1) (show $ fst x)
          updatedTC <- propUpTCSel (BinOpSelector d1) x
          dump $
            printf
              "unifyOther, path: %s, starts proc left results. %s: %s, %s: %s, tc:\n%s"
              (show $ pathFromTC updatedTC)
              (show d1)
              (show $ fst x)
              (show d2)
              (show t2)
              (showTreeCursor updatedTC)
          procLeftEvalRes (d1, fst x) dt2 updatedTC

procLeftEvalRes :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
procLeftEvalRes dt1@(_, t1) dt2@(d2, t2) tc = case treeNode t1 of
  TNAtom _ -> unifyWithDir dt1 dt2 tc
  TNDisj _ -> unifyWithDir dt1 dt2 tc
  TNScope _ -> unifyWithDir dt1 dt2 tc
  TNUnaryOp _ -> procDelay
  TNBinaryOp _ -> procDelay
  _ -> mkUnification dt1 dt2 (fst tc)
 where
  procDelay :: (EvalEnv m) => m Tree
  procDelay = case treeNode t2 of
    TNAtom l2 -> mkCnstr (d2, l2) dt1 tc
    _ -> mkUnification dt1 dt2 (fst tc)

-- | Unify two structs. The unification should take place in the pre order.
unifyStructs :: (EvalEnv m) => TNScope -> TNScope -> TreeCursor -> m Tree
unifyStructs s1 s2 tc = do
  let utc = (nodesToScope allNodes (fst tc), snd tc)
  dump $ printf "unifyStructs: %s gets updated to tree:\n%s" (show $ pathFromTC utc) (show (fst utc))
  u <- evalAllNodes utc
  return (fst u)
 where
  fields1 = trsSubs s1
  fields2 = trsSubs s2
  l1Set = Map.keysSet fields1
  l2Set = Map.keysSet fields2
  interLabels = Set.intersection l1Set l2Set
  disjFields1 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) fields1
  disjFields2 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) fields2

  interNodes :: [(String, Tree)]
  interNodes =
    ( Set.foldr
        ( \key acc ->
            let t1 = fields1 Map.! key
                t2 = fields2 Map.! key
                unifyOp = mkTree (TNBinaryOp $ mkTNBinaryOp AST.Unify unify t1 t2) Nothing -- No original node exists yet
             in (key, unifyOp) : acc
        )
        []
        interLabels
    )

  allNodes :: [(String, Tree)]
  allNodes = interNodes ++ Map.toList disjFields1 ++ Map.toList disjFields2

  evalAllNodes :: (EvalEnv m) => TreeCursor -> m TreeCursor
  evalAllNodes x = foldM evalNode x allNodes

  evalNode :: (EvalEnv m) => TreeCursor -> (String, Tree) -> m TreeCursor
  evalNode acc (key, node) = case treeNode (fst acc) of
    (TNAtom (TreeAtom{trAmAtom = Bottom _})) -> return acc
    _ -> do
      u <- evalTC $ mkSubTC (StringSelector key) node acc
      v <- propUpTCSel (StringSelector key) u
      dump $
        printf
          "unifyStructs: %s gets updated after eval %s, new struct tree:\n%s"
          (show $ pathFromTC v)
          key
          (show (fst v))
      return v

  nodesToScope :: [(String, Tree)] -> Tree -> Tree
  nodesToScope nodes =
    substTreeNode
      ( TNScope $
          TreeScope
            { trsOrdLabels = map fst nodes
            , trsVars = Set.empty
            , trsSubs = Map.fromList nodes
            }
      )

mkNodeWithDir ::
  (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> (Tree -> Tree -> m Tree) -> m Tree
mkNodeWithDir (d1, t1) (_, t2) f = case d1 of
  L -> f t1 t2
  R -> f t2 t1

notUnifiable :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> m Tree
notUnifiable dt1 dt2 = mkNodeWithDir dt1 dt2 f
 where
  f :: (EvalEnv m) => Tree -> Tree -> m Tree
  f x y = return $ mkTreeAtom (Bottom $ printf "values not unifiable: L:\n%s, R:\n%s" (show x) (show y)) Nothing

mkUnification :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> Tree -> m Tree
mkUnification dt1 dt2 t = return $ substTreeNode (TNBinaryOp $ mkTNBinaryOpDir AST.Unify unify dt1 dt2) t

unifyDisj :: (EvalEnv m) => (BinOpDirect, TNDisj, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
unifyDisj (d1, dj1, t1) (d2, unevaledT2) tc = do
  dump $
    printf
      ("unifyDisj: starts evaluation, path: %s, %s: %s, %s: %s")
      (show $ pathFromTC tc)
      (show d1)
      (show t1)
      (show d2)
      (show unevaledT2)
  let subTC = mkSubTC (BinOpSelector d2) unevaledT2 tc
  evaledTC2 <- evalTC subTC
  let t2 = fst evaledTC2
  dump $
    printf
      ("unifyDisj: path: %s, after evaluation, %s: %s, %s: %s")
      (show $ pathFromTC tc)
      (show d1)
      (show t1)
      (show d2)
      (show t2)
  case treeNode t2 of
    TNDisj dj2 -> case (dj1, dj2) of
      -- this is U0 rule, <v1> & <v2> => <v1&v2>
      (TreeDisj{trdDefault = Nothing, trdDisjuncts = ds1}, TreeDisj{trdDefault = Nothing, trdDisjuncts = ds2}) -> do
        ds <- mapM (`unifyOneToMany` ds2) ds1
        treeFromNodes Nothing ds origTree
      -- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
      (TreeDisj{trdDefault = Just df1, trdDisjuncts = ds1}, TreeDisj{trdDefault = Nothing, trdDisjuncts = ds2}) -> do
        dump $ printf ("unifyDisj: U1, df1: %s, ds1: %s, df2: N, ds2: %s") (show df1) (show ds1) (show ds2)
        dfs <- unifyOneToMany df1 ds2
        df <- treeFromNodes Nothing [dfs] Nothing
        ds <- mapM (`unifyOneToMany` ds2) ds1
        treeFromNodes (Just df) ds origTree
      -- this is also the U1 rule.
      (TreeDisj{trdDefault = Nothing}, TreeDisj{}) -> unifyDisj (d2, dj2, t2) (d1, t1) tc
      -- this is U2 rule, <v1,d1> & <v2,d2> => <v1&v2,d1&d2>
      (TreeDisj{trdDefault = Just df1, trdDisjuncts = ds1}, TreeDisj{trdDefault = Just df2, trdDisjuncts = ds2}) -> do
        dump $ printf ("unifyDisj: U2, df1: %s, ds1: %s, df2: %s, ds2: %s") (show df1) (show ds1) (show df2) (show ds2)
        df <- unifyToTree df1 df2 tc
        ds <- mapM (`unifyOneToMany` ds2) ds1
        dump $ printf ("unifyDisj: U2, df: %s, ds: %s") (show df) (show ds)
        treeFromNodes (Just df) ds origTree
    -- this is the case for a disjunction unified with a value.
    _ -> case dj1 of
      TreeDisj{trdDefault = Nothing, trdDisjuncts = ds} -> do
        ds2 <- unifyOneToMany t2 ds
        treeFromNodes Nothing [ds2] origTree
      -- let mismatch = mkTreeAtom (Bottom $ printf "values mismatch: %s with %s" (show t1) (show ds)) Nothing
      -- maybe (return mismatch) return $ listToTree ds2 t2
      TreeDisj{trdDefault = Just df, trdDisjuncts = ds} -> do
        dump $ printf ("unifyDisj: U1, unify with atom %s, disj: (df: %s, ds: %s)") (show t2) (show df) (show ds)
        df2 <- unifyToTree df t2 tc
        ds2 <- unifyOneToMany t2 ds
        dump $ printf ("unifyDisj: U1, df2: %s, ds2: %s") (show df2) (show ds2)
        r <- treeFromNodes (Just df2) [ds2] origTree
        dump $ printf ("unifyDisj: U1, result: %s") (show r)
        return r
 where
  unifyOneToMany :: (EvalEnv m) => Tree -> [Tree] -> m [Tree]
  unifyOneToMany node ts =
    let f = \x y -> unifyToTree x y tc
     in mapM (`f` node) ts

  origTree = treeOrig (fst tc)

treeFromNodes :: (MonadError String m) => Maybe Tree -> [[Tree]] -> Maybe Tree -> m Tree
treeFromNodes dfM ds orig = case (excludeDefault dfM, (concatExclude ds)) of
  (_, []) -> throwError $ "empty disjuncts"
  (Nothing, _d : []) -> return $ mkTree (treeNode _d) orig
  (Nothing, _ds) ->
    let
      node = TNDisj $ TreeDisj{trdDefault = Nothing, trdDisjuncts = _ds}
     in
      return $ mkTree node orig
  (_df, _ds) ->
    let
      node = TNDisj $ TreeDisj{trdDefault = _df, trdDisjuncts = _ds}
     in
      return $ mkTree node orig
 where
  -- concat the disjuncts and exclude the disjuncts with Bottom values.
  concatExclude :: [[Tree]] -> [Tree]
  concatExclude xs =
    filter
      ( \x ->
          case treeNode x of
            TNAtom (TreeAtom{trAmAtom = Bottom _}) -> False
            _ -> True
      )
      (concat xs)

  excludeDefault :: Maybe Tree -> Maybe Tree
  excludeDefault Nothing = Nothing
  excludeDefault (Just x) = case treeNode x of
    TNAtom (TreeAtom{trAmAtom = Bottom _}) -> Nothing
    _ -> Just x
