{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unify (unify) where

import qualified AST
import Control.Monad (foldM, forM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (ask)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Path (BinOpDirect (..), Selector (StringSelector), toBinOpSelector)
import Text.Printf (printf)
import Tree

unify :: (EvalEnv m) => Tree -> Tree -> TreeCursor -> m TreeCursor
unify t1 t2 tc = do
  node <- unifyToTree t1 t2 tc
  return (substTreeNode (treeNode node) (fst tc), snd tc)

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
    (TNAtom l1, _) -> unifyLeftAtom (d1, l1, t1) dt2 tc
    -- Below is the earliest time to create a constraint
    (_, TNAtom l2) -> unifyLeftAtom (d2, l2, t2) dt1 tc
    (TNDisj dj1, _) -> unifyLeftDisj (d1, dj1, t1) (d2, t2) tc
    (TNScope s1, _) -> unifyLeftStruct (d1, s1, t1) dt2 tc
    (TNBounds b1, _) -> unifyLeftBound (d1, b1, t1) dt2 tc
    _ -> unifyLeftOther dt1 dt2 tc
  dump $ printf ("unifying, path: %s:, res:\n%s") (show $ pathFromTC tc) (show res)
  return res

{- |
parTC points to the bin op node.
-}
unifyLeftAtom :: (EvalEnv m) => (BinOpDirect, TNAtom, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
unifyLeftAtom (d1, l1, t1) dt2@(d2, t2) parTC = do
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
    (_, TNBounds b) -> do
      dump $ printf "unifyAtomBounds: %s, %s" (show t1) (show t2)
      returnTree $ TNAtom $ TreeAtom $ unifyAtomBounds (d1, (trAmAtom l1)) (d2, (trBdList b))
    (_, TNConstraint c) ->
      if l1 == trCnAtom c
        then returnTree (TNConstraint c)
        else
          return $
            Tree
              (TNAtom . TreeAtom $ Bottom $ printf "values mismatch: %s != %s" (show l1) (show $ trCnAtom c))
              (treeOrig (fst parTC))
    (_, TNDisj dj2) -> do
      dump $ printf "unifyLeftAtom: TNDisj %s, %s" (show t2) (show t1)
      unifyLeftDisj (d2, dj2, t2) (d1, t1) parTC
    (_, TNFunc fn) -> case trfnType fn of
      -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
      -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
      -- marked disjunction.
      DisjFunc -> unifyLeftOther dt2 dt1 parTC
      _ -> procOther
    (_, TNRefCycleVar) -> procOther
    (_, TNLink _) -> procOther
    _ -> notUnifiable dt1 dt2
 where
  dt1 = (d1, t1)

  returnTree :: (EvalEnv m) => TreeNode -> m Tree
  returnTree n = return $ mkNewTree n

  mismatch :: (Show a) => a -> a -> TreeNode
  mismatch x y = TNAtom . TreeAtom $ Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

  procOther :: (EvalEnv m) => m Tree
  procOther = do
    Config{cfCreateCnstr = cc} <- ask
    if cc
      then mkCnstr (d1, l1) dt2
      else unifyLeftOther dt2 dt1 parTC

-- dirApply :: (a -> a -> b) -> (BinOpDirect, a) -> a -> b
-- dirApply f (di1, i1) i2 = if di1 == L then f i1 i2 else f i2 i1

mkCnstr :: (EvalEnv m) => (BinOpDirect, TNAtom) -> (BinOpDirect, Tree) -> m Tree
mkCnstr (_, l1) (_, t2) = return $ mkNewTree (TNConstraint $ mkTNConstraint l1 t2 unify)

unifyLeftBound :: (EvalEnv m) => (BinOpDirect, TNBounds, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
unifyLeftBound (d1, b1, t1) (d2, t2) tc = case treeNode t2 of
  TNAtom ta2 -> do
    dump $ printf "unifyAtomBounds: %s, %s" (show t1) (show t2)
    return $ mkTreeAtom (unifyAtomBounds (d2, (trAmAtom ta2)) (d1, trBdList b1))
  TNBounds b2 -> do
    dump $ printf "unifyBoundList: %s, %s" (show t1) (show t2)
    let res = unifyBoundList (d1, trBdList b1) (d2, trBdList b2)
    case res of
      Left err -> return $ mkTreeAtom (Bottom err)
      Right bs ->
        let
          r =
            foldl
              ( \acc x -> case x of
                  BdIsAtom a -> (fst acc, Just a)
                  _ -> (x : fst acc, snd acc)
              )
              ([], Nothing)
              bs
         in
          case snd r of
            Just a -> return $ mkTreeAtom a
            Nothing -> return $ mkTNBounds (fst r)
  TNFunc _ -> unifyLeftOther (d2, t2) (d1, t1) tc
  TNConstraint _ -> unifyLeftOther (d2, t2) (d1, t1) tc
  TNRefCycleVar -> unifyLeftOther (d2, t2) (d1, t1) tc
  TNLink _ -> unifyLeftOther (d2, t2) (d1, t1) tc
  TNDisj _ -> unifyLeftOther (d2, t2) (d1, t1) tc
  _ -> notUnifiable (d1, t1) (d2, t2)

unifyAtomBounds :: (BinOpDirect, Atom) -> (BinOpDirect, [Bound]) -> Atom
unifyAtomBounds (d1, a1) (_, bs) =
  let
    cs = map withBound bs
   in
    foldl (\_ x -> if x == a1 then a1 else x) a1 cs
 where
  withBound :: Bound -> Atom
  withBound b =
    let
      r = unifyBounds (d1, BdIsAtom a1) (R, b)
     in
      case r of
        Left s -> Bottom s
        Right v -> case v of
          x : [] -> case x of
            BdIsAtom a -> a
            _ -> Bottom $ printf "unexpected bounds unification result: %s" (show x)
          _ -> Bottom $ printf "unexpected bounds unification result: %s" (show v)

-- TODO: regex implementation
-- Second argument is the pattern.
reMatch :: String -> String -> Bool
reMatch = (==)

-- TODO: regex implementation
-- Second argument is the pattern.
reNotMatch :: String -> String -> Bool
reNotMatch = (/=)

unifyBoundList :: (BinOpDirect, [Bound]) -> (BinOpDirect, [Bound]) -> Either String [Bound]
unifyBoundList (d1, bs1) (d2, bs2) = case (bs1, bs2) of
  ([], _) -> return bs2
  (_, []) -> return bs1
  _ -> do
    bss <- manyToMany (d1, bs1) (d2, bs2)
    let bsMap = Map.fromListWith (\x y -> x ++ y) (map (\b -> (bdRep b, [b])) (concat bss))
    norm <- forM bsMap narrowBounds
    let m = Map.toList norm
    return $ concat $ map snd m
 where
  oneToMany :: (BinOpDirect, Bound) -> (BinOpDirect, [Bound]) -> Either String [Bound]
  oneToMany (ld1, b) (ld2, ts) =
    let f = \x y -> unifyBounds (ld1, x) (ld2, y)
     in do
          r <- mapM (`f` b) ts
          return $ concat r

  manyToMany :: (BinOpDirect, [Bound]) -> (BinOpDirect, [Bound]) -> Either String [[Bound]]
  manyToMany (ld1, ts1) (ld2, ts2) =
    if ld1 == R
      then mapM (\y -> oneToMany (ld2, y) (ld1, ts1)) ts2
      else mapM (\x -> oneToMany (ld1, x) (ld2, ts2)) ts1

-- | Narrow the bounds to the smallest set of bounds for the same bound type.
narrowBounds :: [Bound] -> Either String [Bound]
narrowBounds xs = case xs of
  [] -> return []
  (BdNE _) : _ -> return xs
  x : rs ->
    let
      f acc y =
        if length acc == 1
          then unifyBounds (L, acc !! 0) (R, y)
          else Left "bounds mismatch"
     in
      foldM f [x] rs

unifyBounds :: (BinOpDirect, Bound) -> (BinOpDirect, Bound) -> Either String [Bound]
unifyBounds db1@(d1, b1) db2@(_, b2) = case b1 of
  BdNE a1 -> case b2 of
    BdNE a2 -> return $ if a1 == a2 then [b1] else newOrdBounds
    BdNumCmp c2 -> uNENumCmp a1 c2
    BdStrMatch m2 -> uNEStrMatch a1 m2
    BdType t2 -> uNEType a1 t2
    BdIsAtom a2 -> if a1 == a2 then Left conflict else return [b2]
  BdNumCmp c1 -> case b2 of
    BdNumCmp c2 -> uNumCmpNumCmp c1 c2
    BdStrMatch _ -> Left conflict
    BdType t2 ->
      if t2 `elem` [BdInt, BdFloat, BdNumber]
        then return [b1]
        else Left conflict
    BdIsAtom a2 -> uNumCmpAtom c1 a2
    _ -> unifyBounds db2 db1
  BdStrMatch m1 -> case b2 of
    BdStrMatch m2 -> case (m1, m2) of
      (BdReMatch _, BdReMatch _) -> return $ if m1 == m2 then [b1] else newOrdBounds
      (BdReNotMatch _, BdReNotMatch _) -> return $ if m1 == m2 then [b1] else newOrdBounds
      _ -> return [b1, b2]
    BdType t2 ->
      if t2 `elem` [BdString]
        then return [b1]
        else Left conflict
    BdIsAtom a2 -> uStrMatchAtom m1 a2
    _ -> unifyBounds db2 db1
  BdType t1 -> case b2 of
    BdType t2 -> if t1 == t2 then return [b1] else Left conflict
    BdIsAtom a2 -> uTypeAtom t1 a2
    _ -> unifyBounds db2 db1
  BdIsAtom a1 -> case b2 of
    BdIsAtom a2 -> if a1 == a2 then return [b1] else Left conflict
    _ -> unifyBounds db2 db1
 where
  uNENumCmp :: Atom -> BdNumCmp -> Either String [Bound]
  uNENumCmp a1 (BdNumCmpCons o2 y) = do
    x <- case a1 of
      Int x -> return $ NumInt x
      Float x -> return $ NumFloat x
      _ -> Left conflict
    case o2 of
      BdLT -> if x < y then Left conflict else return newOrdBounds
      BdLE -> if x <= y then Left conflict else return newOrdBounds
      BdGT -> if x > y then Left conflict else return newOrdBounds
      BdGE -> if x >= y then Left conflict else return newOrdBounds

  uNEStrMatch :: Atom -> BdStrMatch -> Either String [Bound]
  uNEStrMatch a1 m2 = do
    _ <- case a1 of
      String x -> return x
      _ -> Left conflict
    case m2 of
      -- delay verification
      BdReMatch _ -> return [b1, b2]
      BdReNotMatch _ -> return [b1, b2]

  uNEType :: Atom -> BdType -> Either String [Bound]
  uNEType a1 t2 = case a1 of
    Bool _ -> if BdBool == t2 then Left conflict else return newOrdBounds
    Int _ -> if BdInt == t2 then Left conflict else return newOrdBounds
    Float _ -> if BdFloat == t2 then Left conflict else return newOrdBounds
    String _ -> if BdString == t2 then Left conflict else return newOrdBounds
    -- TODO: null?
    _ -> Left conflict

  ncncGroup :: [([BdNumCmpOp], [(Number -> Number -> Bool)])]
  ncncGroup =
    [ ([BdLT, BdLE], [(<=), (>)])
    , ([BdGT, BdGE], [(>=), (<)])
    ]

  uNumCmpNumCmp :: BdNumCmp -> BdNumCmp -> Either String [Bound]
  uNumCmpNumCmp (BdNumCmpCons o1 n1) (BdNumCmpCons o2 n2) =
    let
      c1g = if o1 `elem` (fst (ncncGroup !! 0)) then ncncGroup !! 0 else ncncGroup !! 1
      c1SameGCmp = (snd c1g) !! 0
      c1OppGCmp = (snd c1g) !! 1
      isSameGroup = o2 `elem` (fst c1g)
      oppClosedEnds = sort [o1, o2] == [BdLE, BdGE]
     in
      if isSameGroup
        then return $ if c1SameGCmp n1 n2 then [b1] else [b2]
        else
          if
            | oppClosedEnds && n1 == n2 -> case n1 of
                NumInt i -> return [BdIsAtom $ Int i]
                NumFloat f -> return [BdIsAtom $ Float f]
            | c1OppGCmp n1 n2 -> return newOrdBounds
            | otherwise -> Left conflict

  uNumCmpAtom :: BdNumCmp -> Atom -> Either String [Bound]
  uNumCmpAtom (BdNumCmpCons o1 n1) a2 = do
    x <- case a2 of
      Int x -> return $ NumInt x
      Float x -> return $ NumFloat x
      _ -> Left conflict
    let r = case o1 of
          BdLT -> x < n1
          BdLE -> x <= n1
          BdGT -> x > n1
          BdGE -> x >= n1
    if r then return [b2] else Left conflict

  uStrMatchAtom :: BdStrMatch -> Atom -> Either String [Bound]
  uStrMatchAtom m1 a2 = case a2 of
    String s2 ->
      let r = case m1 of
            BdReMatch p1 -> reMatch s2 p1
            BdReNotMatch p1 -> reNotMatch s2 p1
       in if r then return [b2] else Left conflict
    _ -> Left conflict

  uTypeAtom :: BdType -> Atom -> Either String [Bound]
  uTypeAtom t1 a2 =
    let r = case a2 of
          Bool _ -> t1 == BdBool
          Int _ -> BdInt `elem` [BdInt, BdNumber]
          Float _ -> BdFloat `elem` [BdFloat, BdNumber]
          String _ -> t1 == BdString
          _ -> False
     in if r then return [b2] else Left conflict

  conflict :: String
  conflict = printf "bounds %s and %s conflict" (show b1) (show b2)

  newOrdBounds :: [Bound]
  newOrdBounds = if d1 == L then [b1, b2] else [b2, b1]

unifyLeftOther :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
unifyLeftOther dt1@(d1, t1) dt2@(d2, t2) tc = case (treeNode t1, treeNode t2) of
  (TNFunc _, _) -> evalOrDelay
  -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
  -- containing an atom or a bottom.
  (TNConstraint c1, _) -> do
    na <- unifyWithDir (d1, mkNewTree (TNAtom $ trCnAtom c1)) dt2 tc
    case treeNode na of
      TNAtom TreeAtom{trAmAtom = Bottom _} -> return na
      _ -> return t1
  -- According to the spec,
  -- A field value of the form r & v, where r evaluates to a reference cycle and v is a concrete value, evaluates to v.
  -- Unification is idempotent and unifying a value with itself ad infinitum, which is what the cycle represents,
  -- results in this value. Implementations should detect cycles of this kind, ignore r, and take v as the result of
  -- unification.
  -- We can just return the second value.
  (TNRefCycleVar, _) -> return t2
  (TNLink l, _) -> do
    substTC1 <- substLinkTC l $ mkSubTC (toBinOpSelector d1) t1 tc
    case treeNode (fst substTC1) of
      TNLink _ -> do
        dump $ printf "unifyLeftOther: TNLink %s, is still evaluated to TNLink %s" (show t1) (show $ fst substTC1)
        mkUnification dt1 dt2
      _ -> unifyWithDir (d1, fst substTC1) dt2 tc
  _ -> notUnifiable dt1 dt2
 where
  evalOrDelay :: (EvalEnv m) => m Tree
  evalOrDelay =
    let subTC = mkSubTC (toBinOpSelector d1) t1 tc
     in do
          x <- evalTC subTC
          dump $
            printf "unifyLeftOther, path: %s, %s is evaluated to %s" (show $ pathFromTC tc) (show t1) (show $ fst x)
          updatedTC <- propUpTCSel (toBinOpSelector d1) x
          dump $
            printf
              "unifyLeftOther, path: %s, starts proc left results. %s: %s, %s: %s"
              (show $ pathFromTC updatedTC)
              (show d1)
              (show $ fst x)
              (show d2)
              (show t2)
          procLeftEvalRes (d1, fst x) dt2 updatedTC

procLeftEvalRes :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
procLeftEvalRes dt1@(_, t1) dt2@(d2, t2) tc = case treeNode t1 of
  TNFunc _ -> procDelay
  TNLink _ -> mkUnification dt1 dt2
  _ -> unifyWithDir dt1 dt2 tc
 where
  procDelay :: (EvalEnv m) => m Tree
  procDelay = case treeNode t2 of
    TNAtom l2 -> mkCnstr (d2, l2) dt1
    _ -> mkUnification dt1 dt2

unifyLeftStruct :: (EvalEnv m) => (BinOpDirect, TNScope, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
unifyLeftStruct (d1, s1, t1) (d2, t2) tc = case treeNode t2 of
  TNScope s2 -> unifyStructs (d1, s1) (d2, s2) tc
  _ -> unifyLeftOther (d2, t2) (d1, t1) tc

unifyStructs :: (EvalEnv m) => (BinOpDirect, TNScope) -> (BinOpDirect, TNScope) -> TreeCursor -> m Tree
unifyStructs (_, s1) (_, s2) tc = do
  let utc = (nodesToScope allNodes, snd tc)
  dump $ printf "unifyStructs: %s gets updated to tree:\n%s" (show $ pathFromTC utc) (show (fst utc))
  u <- evalAllNodes utc
  return (fst u)
 where
  fields1 = trsSubs s1
  fields2 = trsSubs s2
  l1Set = Map.keysSet fields1
  l2Set = Map.keysSet fields2
  interKeys = Set.intersection l1Set l2Set
  disjKeys1 = Set.difference l1Set interKeys
  disjKeys2 = Set.difference l2Set interKeys

  interNodes :: [(String, LabelAttr, Tree)]
  interNodes =
    ( Set.foldr
        ( \key acc ->
            let t1 = fields1 Map.! key
                t2 = fields2 Map.! key
                a1 = (trsAttrs s1) Map.! key
                a2 = (trsAttrs s2) Map.! key
                ua = mergeAttrs a1 a2
                unifyOp = mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify t1 t2) -- No original node exists yet
             in (key, ua, unifyOp) : acc
        )
        []
        interKeys
    )

  withAttr :: TNScope -> Set.Set String -> [(String, LabelAttr, Tree)]
  withAttr s keys = map (\key -> (key, (trsAttrs s) Map.! key, (trsSubs s) Map.! key)) (Set.toList keys)

  allNodes :: [(String, LabelAttr, Tree)]
  allNodes = interNodes ++ (withAttr s1 disjKeys1) ++ (withAttr s2 disjKeys2)

  evalAllNodes :: (EvalEnv m) => TreeCursor -> m TreeCursor
  evalAllNodes x = foldM evalNode x allNodes

  evalNode :: (EvalEnv m) => TreeCursor -> (String, LabelAttr, Tree) -> m TreeCursor
  evalNode acc (key, _, node) = case treeNode (fst acc) of
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

  nodesToScope :: [(String, LabelAttr, Tree)] -> Tree
  nodesToScope nodes =
    mkNewTree
      ( TNScope $
          TreeScope
            { trsOrdLabels = map (\(k, _, _) -> k) nodes
            , trsSubs = Map.fromList $ map (\(k, _, n) -> (k, n)) nodes
            , trsAttrs = Map.fromList $ map (\(k, a, _) -> (k, a)) nodes
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
  f x y = return $ mkTreeAtom (Bottom $ printf "values not unifiable: L:\n%s, R:\n%s" (show x) (show y))

mkUnification :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> m Tree
mkUnification dt1 dt2 = return $ mkNewTree (TNFunc $ mkBinaryOpDir AST.Unify unify dt1 dt2)

unifyLeftDisj :: (EvalEnv m) => (BinOpDirect, TNDisj, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
unifyLeftDisj (d1, dj1, t1) (d2, t2) tc = do
  case treeNode t2 of
    TNFunc _ -> unifyLeftOther (d2, t2) (d1, t1) tc
    TNConstraint _ -> unifyLeftOther (d2, t2) (d1, t1) tc
    TNRefCycleVar -> unifyLeftOther (d2, t2) (d1, t1) tc
    TNLink _ -> unifyLeftOther (d2, t2) (d1, t1) tc
    TNDisj dj2 -> case (dj1, dj2) of
      -- this is U0 rule, <v1> & <v2> => <v1&v2>
      (TreeDisj{trdDefault = Nothing, trdDisjuncts = ds1}, TreeDisj{trdDefault = Nothing, trdDisjuncts = ds2}) -> do
        ds <- mapM (`oneToMany` (d2, ds2)) (map (\x -> (d1, x)) ds1)
        treeFromNodes Nothing ds origTree
      -- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
      (TreeDisj{trdDefault = Just df1, trdDisjuncts = ds1}, TreeDisj{trdDefault = Nothing, trdDisjuncts = ds2}) -> do
        dump $ printf ("unifyLeftDisj: U1, df1: %s, ds1: %s, df2: N, ds2: %s") (show df1) (show ds1) (show ds2)
        dfs <- oneToMany (d1, df1) (d2, ds2)
        df <- treeFromNodes Nothing [dfs] Nothing
        dss <- manyToMany (d1, ds1) (d2, ds2)
        treeFromNodes (Just df) dss origTree
      -- this is also the U1 rule.
      (TreeDisj{trdDefault = Nothing}, TreeDisj{}) -> unifyLeftDisj (d2, dj2, t2) (d1, t1) tc
      -- this is U2 rule, <v1,d1> & <v2,d2> => <v1&v2,d1&d2>
      (TreeDisj{trdDefault = Just df1, trdDisjuncts = ds1}, TreeDisj{trdDefault = Just df2, trdDisjuncts = ds2}) -> do
        dump $
          printf
            ("unifyLeftDisj: path: %s, U2, d1:%s, df1: %s, ds1: %s, df2: %s, ds2: %s")
            (show $ pathFromTC tc)
            (show d1)
            (show df1)
            (show ds1)
            (show df2)
            (show ds2)
        df <- unifyWithDir (d1, df1) (d2, df2) tc
        dss <- manyToMany (d1, ds1) (d2, ds2)
        dump $ printf ("unifyLeftDisj: path: %s, U2, df: %s, dss: %s") (show $ pathFromTC tc) (show df) (show dss)
        treeFromNodes (Just df) dss origTree
    -- this is the case for a disjunction unified with a value.
    _ -> case dj1 of
      TreeDisj{trdDefault = Nothing, trdDisjuncts = ds1} -> do
        ds2 <- oneToMany (d2, t2) (d1, ds1)
        treeFromNodes Nothing [ds2] origTree
      TreeDisj{trdDefault = Just df1, trdDisjuncts = ds1} -> do
        dump $ printf ("unifyLeftDisj: U1, unify with atom %s, disj: (df: %s, ds: %s)") (show t2) (show df1) (show ds1)
        df2 <- unifyWithDir (d2, df1) (d2, t2) tc
        ds2 <- oneToMany (d2, t2) (d1, ds1)
        dump $ printf ("unifyLeftDisj: U1, df2: %s, ds2: %s") (show df2) (show ds2)
        r <- treeFromNodes (Just df2) [ds2] origTree
        dump $ printf ("unifyLeftDisj: U1, result: %s") (show r)
        return r
 where
  oneToMany :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, [Tree]) -> m [Tree]
  oneToMany (ld1, node) (ld2, ts) =
    let f = \x y -> unifyWithDir (ld1, x) (ld2, y) tc
     in mapM (`f` node) ts

  manyToMany :: (EvalEnv m) => (BinOpDirect, [Tree]) -> (BinOpDirect, [Tree]) -> m [[Tree]]
  manyToMany (ld1, ts1) (ld2, ts2) =
    if ld1 == R
      then mapM (\y -> oneToMany (ld2, y) (ld1, ts1)) ts2
      else mapM (\x -> oneToMany (ld1, x) (ld2, ts2)) ts1

  origTree = treeOrig (fst tc)

treeFromNodes :: (MonadError String m) => Maybe Tree -> [[Tree]] -> Maybe Tree -> m Tree
treeFromNodes dfM ds orig = case (excludeDefault dfM, (concatExclude ds)) of
  (_, []) -> throwError $ "empty disjuncts"
  (Nothing, _d : []) -> return $ Tree (treeNode _d) orig
  (Nothing, _ds) ->
    let
      node = TNDisj $ TreeDisj{trdDefault = Nothing, trdDisjuncts = _ds}
     in
      return $ Tree node orig
  (_df, _ds) ->
    let
      node = TNDisj $ TreeDisj{trdDefault = _df, trdDisjuncts = _ds}
     in
      return $ Tree node orig
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
