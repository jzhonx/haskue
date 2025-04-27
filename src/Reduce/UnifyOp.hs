{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.UnifyOp where

import qualified AST
import Common (
  BuildASTExpr (buildASTExpr),
  Config (..),
  Env,
  HasConfig (..),
  RuntimeParams (RuntimeParams, rpCreateCnstr),
  isTreeBottom,
 )
import Control.Monad (foldM, forM, when)
import Control.Monad.Reader (asks, local)
import qualified Cursor
import qualified Data.IntMap.Strict as IntMap
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isJust, isNothing)
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified TCOps
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

-- | UTree is a tree with a direction and an embedded flag.
data UTree = UTree
  { utDir :: Path.BinOpDirect
  , utEmbedID :: Maybe Int
  -- ^ Whether the tree is embedded in a struct.
  , utTC :: TCOps.TrCur
  -- ^ This tree cursor of the conjunct.
  }

instance Show UTree where
  show (UTree d e tc) =
    show d
      <> ","
      <> show (Cursor.tcTreeAddr tc)
      <> ","
      <> maybe "" (\x -> " embed:" <> show x) e
      <> "\n"
      <> show (Cursor.tcFocus tc)

showUTreeList :: [UTree] -> String
showUTreeList [] = "[]"
showUTreeList (x : xs) =
  show x
    <> "\n"
    <> foldl
      ( \acc y -> acc <> show y <> "\n"
      )
      ""
      xs

unify :: (RM.ReduceMonad s r m) => [VT.Tree] -> TCOps.TrCur -> m (Maybe VT.Tree)
unify ts unifyTC = do
  uts <-
    mapM
      ( \(i, _) -> do
          conjTC <- TCOps.goDownTCSegMust (Path.MutableArgTASeg i) unifyTC
          return $ UTree Path.R Nothing conjTC
      )
      (zip [0 ..] ts)
  unifyUTrees uts (Cursor.tcTreeAddr unifyTC)

{- | Unify a list of UTrees.

The order of the unification is the same as the order of the UTrees.
-}
unifyUTrees :: (RM.ReduceMonad s r m) => [UTree] -> Path.TreeAddr -> m (Maybe VT.Tree)
unifyUTrees uts unifyAddr = RM.debugSpanArgsOpRM "unifyUTrees" (showUTreeList uts) unifyAddr $ do
  when (length uts < 2) $ throwErrSt "not enough arguments"
  let isAllCyclic = all (VT.treeIsCyclic . Cursor.tcFocus . utTC) uts
  if isAllCyclic
    then return $ Just $ VT.mkBottomTree "structural cycle"
    else do
      normalized <-
        foldM
          ( \acc ut -> do
              r <- normalizeConjunct ut
              return $ acc ++ r
          )
          []
          uts

      case sequence normalized of
        Nothing -> return Nothing
        Just readies -> do
          -- Remove the reference cycle.
          --
          -- According to the spec, A field value of the form r & v, where r evaluates to a reference
          -- cycle and v is a concrete value, evaluates to v. Unification is idempotent and unifying a
          -- value with itself ad infinitum, which is what the cycle represents, results in this value.
          -- Implementations should detect cycles of this kind, ignore r, and take v as the result of
          -- unification.
          let filtered =
                filter
                  ( \ut -> case (VT.treeNode . Cursor.tcFocus . utTC) ut of
                      VT.TNRefCycle -> False
                      _ -> True
                  )
                  readies
          mergeUTrees filtered unifyAddr

{- | Unify two UTrees.

It is called in the mergeBin functions so that the order of the operands can be preserved.
-}
unifyBinUTrees :: (RM.ReduceMonad s r m) => UTree -> UTree -> Path.TreeAddr -> m (Maybe VT.Tree)
unifyBinUTrees ut1@(UTree{utDir = Path.L}) ut2 unifyAddr = unifyUTrees [ut1, ut2] unifyAddr
unifyBinUTrees ut1@(UTree{utDir = Path.R}) ut2 unifyAddr = unifyUTrees [ut2, ut1] unifyAddr

mergeUTrees :: (RM.ReduceMonad s r m) => [UTree] -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeUTrees uts unifyAddr = RM.debugSpanArgsOpRM "mergeUTrees" (showUTreeList uts) unifyAddr $ do
  rM <-
    foldM
      ( \accM ut -> case accM of
          Nothing -> return Nothing
          Just acc -> do
            rM <- mergeBinUTrees (acc{utDir = Path.L}) (ut{utDir = Path.R}) unifyAddr
            maybe
              (return Nothing)
              (\r -> return $ Just $ acc{utTC = r `Cursor.setTCFocus` utTC acc})
              rM
      )
      (Just $ head uts)
      (tail uts)
  maybe (return Nothing) (\r -> return $ Just $ Cursor.tcFocus (utTC r)) rM

{- | Normalize the unify operation tree.

It does the following:
1. Flatten the unify operation tree because unification is associative.
2. Reduce ref and disjoin mutable to basic form.
-}
normalizeConjunct :: (RM.ReduceMonad s r m) => UTree -> m [Maybe UTree]
normalizeConjunct ut@(UTree{utTC = tc}) = RM.debugSpanRM "normalizeConjunct" tc $ do
  MutEnv.Functions{MutEnv.reduceUnifyConj = reduceUnifyConj} <- asks MutEnv.getFuncs
  conjM <- reduceUnifyConj tc
  case conjM of
    Nothing -> return [Nothing]
    Just conj ->
      let conjTC = conj `Cursor.setTCFocus` tc
       in case VT.treeNode conj of
            VT.TNMutable (VT.UOp u) -> do
              foldM
                ( \acc (i, _) -> do
                    subConjTC <- TCOps.goDownTCSegMust (Path.MutableArgTASeg i) conjTC
                    subs <- normalizeConjunct (ut{utTC = subConjTC})
                    return $ acc ++ subs
                )
                []
                (zip [0 ..] (VT.ufConjuncts u))
            _ -> return [Just ut{utTC = conjTC}]

{- | Merge Two UTrees.

The special case is the struct. If two operands are structs, we must not immediately reduce the operands. Instead, we
should combine both fields and reduce sub-fields. The reason is stated in the spec,

> The successful unification of structs a and b is a new struct c which has all fields of both a and b, where the value
of a field f in c is a.f & b.f if f is defined in both a and b, or just a.f or b.f if f is in just a or b, respectively.
Any references to a or b in their respective field values need to be replaced with references to c. The result of a
unification is bottom (_|_) if any of its defined fields evaluates to bottom, recursively.

Suppose one of the structs contains a reference to a field in the other struct, and reducing the struct operand will
register a notifier that watches the field in the unified struct. The notifier will be triggered when the field is
updated. But the direction is from parent to the child. Once the operand is updated, the reference system will search
for the lowest ancestor mutable to re-run reduction since one of the LAM's dependencies is updated. This will cause the
unified struct to be reduced again, and the notifier will be triggered again. This will cause an infinite loop.

Consider the example:
x: { a: c } & { c: {} }

After reducing the left struct, the notifier, (/x/c, /x/fa0/a) will be registered to watch the field "c". When the field
"c" is updated, the notifier will be triggered. Then the struct labeled with "x" will be reduced again. An infinite loop
will occur.

Another example:
{
  a: b + 100
  b: a - 100
} &
{ b: 50 }

The "b" in the first struct will have to see the atom 50.

For operands that are references, we do not need reduce them. We only evaluate the expression when the reference is
dereferenced. If the reference is evaluated to a struct, the struct will be a raw struct.

opAddr is not necessarily equal to the parent of one of the tree cursors if the function is directly called.
-}
mergeBinUTrees :: (RM.ReduceMonad s r m) => UTree -> UTree -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeBinUTrees ut1@(UTree{utTC = tc1}) ut2@(UTree{utTC = tc2}) opAddr = do
  let t1 = Cursor.tcFocus tc1
      t2 = Cursor.tcFocus tc2
  RM.debugSpanArgsOpRM
    "mergeBinUTrees"
    ( printf
        ("merging %s, %s" ++ "\n" ++ "with %s, %s")
        (show $ utDir ut1)
        (show t1)
        (show $ utDir ut2)
        (show t2)
    )
    opAddr
    $ do
      -- Each case should handle embedded case when the left value is embedded.
      rM <- case (VT.treeNode t1, VT.treeNode t2) of
        -- VT.CnstredVal has the highest priority, because the real operand is the value of the VT.CnstredVal.
        (VT.TNCnstredVal c, _) -> mergeLeftCnstredVal (c, ut1) ut2 opAddr
        (_, VT.TNCnstredVal c) -> mergeLeftCnstredVal (c, ut2) ut1 opAddr
        (VT.TNBottom _, _) -> retTr t1
        (_, VT.TNBottom _) -> retTr t2
        (VT.TNTop, _) -> mergeLeftTop ut1 ut2
        (_, VT.TNTop) -> mergeLeftTop ut2 ut1
        (VT.TNAtom a1, _) -> mergeLeftAtom (a1, ut1) ut2 opAddr
        -- Below is the earliest time to create a constraint
        (_, VT.TNAtom a2) -> mergeLeftAtom (a2, ut2) ut1 opAddr
        (VT.TNDisj dj1, _) -> mergeLeftDisj (dj1, ut1) ut2 opAddr
        (_, VT.TNDisj dj2) -> mergeLeftDisj (dj2, ut2) ut1 opAddr
        (VT.TNStruct s1, _) -> mergeLeftStruct (s1, ut1) ut2 opAddr
        (_, VT.TNStruct s2) -> mergeLeftStruct (s2, ut2) ut1 opAddr
        (VT.TNBounds b1, _) -> mergeLeftBound (b1, ut1) ut2 opAddr
        (_, VT.TNBounds b2) -> mergeLeftBound (b2, ut2) ut1 opAddr
        _ -> mergeLeftOther ut1 ut2 opAddr

      -- close the merged tree
      maybe
        (return Nothing)
        (\r -> retTr (r{VT.treeRecurClosed = VT.treeRecurClosed t1 || VT.treeRecurClosed t2}))
        rM

retTr :: (RM.ReduceMonad s r m) => VT.Tree -> m (Maybe VT.Tree)
retTr = return . Just

mergeLeftCnstredVal ::
  (RM.ReduceMonad s r m) => (VT.CnstredVal VT.Tree, UTree) -> UTree -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeLeftCnstredVal (c1, ut1) ut2@UTree{utTC = tc2} opAddr = do
  let t2 = Cursor.tcFocus tc2
  eM2 <- case VT.treeNode t2 of
    -- ut2 is VT.CnstredVal, we need to merge original expressions.
    VT.TNCnstredVal c2 -> return $ VT.cnsedOrigExpr c2
    -- ut2 is not VT.CnstredVal, we need to build the original expression.
    _ -> Just <$> buildASTExpr False t2

  e <- case catMaybes [VT.cnsedOrigExpr c1, eM2] of
    -- If only one side has an original expression, we can use it directly.
    [e] -> return e
    -- If both sides have original expressions, we need to unify them.
    [e1, e2] -> return $ AST.binaryOpCons AST.Unify e1 e2
    _ -> throwErrSt "both CnstredVals are empty"

  rM <- unifyBinUTrees (ut1{utTC = VT.cnsedVal c1 `Cursor.setTCFocus` utTC ut1}) ut2 opAddr
  maybe
    (return Nothing)
    ( \r ->
        -- Re-encapsulate the VT.CnstredVal.
        case VT.treeNode r of
          VT.TNCnstredVal c -> retTr $ VT.setTN r (VT.TNCnstredVal $ c{VT.cnsedOrigExpr = Just e})
          _ -> retTr $ VT.setTN r (VT.TNCnstredVal $ VT.CnstredVal r (Just e))
    )
    rM

mergeLeftTop :: (RM.ReduceMonad s r m) => UTree -> UTree -> m (Maybe VT.Tree)
mergeLeftTop ut1 ut2 = do
  let t1 = Cursor.tcFocus (utTC ut1)
      t2 = Cursor.tcFocus (utTC ut2)
  case VT.treeNode t2 of
    -- If the left top is embedded in the right struct, we can immediately put the top into the tree without worrying
    -- any future existing/new fields. Because for example {_, a: 1} is equivalent to _ & {a: 1}. This follows the
    -- behavior of the spec:
    -- The result of { A } is A for any A (including definitions).
    -- Notice that this is different from the behavior of the latest CUE. The latest CUE would do the following:
    -- {_, _h: int} & {_h: "hidden"} -> _|_.
    VT.TNStruct _ | isJust (utEmbedID ut1) -> retTr t1
    _ -> retTr t2

mergeLeftAtom :: (RM.ReduceMonad s r m) => (VT.AtomV, UTree) -> UTree -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeLeftAtom (v1, ut1@(UTree{utDir = d1})) ut2@(UTree{utTC = tc2, utDir = d2}) opAddr = RM.debugSpanOpRM "mergeLeftAtom" opAddr $ do
  let t2 = Cursor.tcFocus tc2
  case (VT.amvAtom v1, VT.treeNode t2) of
    (VT.String x, VT.TNAtom s)
      | VT.String y <- VT.amvAtom s -> rtn $ if x == y then VT.TNAtom v1 else amismatch x y
    (VT.Int x, VT.TNAtom s)
      | VT.Int y <- VT.amvAtom s -> rtn $ if x == y then VT.TNAtom v1 else amismatch x y
    (VT.Float x, VT.TNAtom s)
      | VT.Float y <- VT.amvAtom s -> rtn $ if x == y then VT.TNAtom v1 else amismatch x y
    (VT.Bool x, VT.TNAtom s)
      | VT.Bool y <- VT.amvAtom s -> rtn $ if x == y then VT.TNAtom v1 else amismatch x y
    (VT.Null, VT.TNAtom s) | VT.Null <- VT.amvAtom s -> rtn $ VT.TNAtom v1
    (_, VT.TNBounds b) -> do
      logDebugStr $ printf "mergeLeftAtom, %s with VT.Bounds: %s" (show v1) (show t2)
      return $ Just $ mergeAtomBounds (d1, VT.amvAtom v1) (d2, VT.bdsList b)
    (_, VT.TNAtomCnstr c) ->
      if v1 == VT.cnsAtom c
        then retTr t2
        else retTr $ VT.mkBottomTree $ printf "values mismatch: %s != %s" (show v1) (show $ VT.cnsAtom c)
    (_, VT.TNDisj dj2) -> do
      logDebugStr $ printf "mergeLeftAtom: VT.TNDisj %s, %s" (show t2) (show v1)
      mergeLeftDisj (dj2, ut2) ut1 opAddr
    (_, VT.TNMutable mut2)
      -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
      -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
      -- marked disjunction.
      | (VT.DisjOp _) <- mut2 -> mergeLeftOther ut2 ut1 opAddr
      | otherwise -> mkCnstrOrOther t2
    (_, VT.TNRefCycle) -> mkCnstrOrOther t2
    (_, VT.TNStruct s2) -> mergeLeftStruct (s2, ut2) ut1 opAddr
    _ -> mergeLeftOther ut1 ut2 opAddr
 where
  rtn :: (RM.ReduceMonad s r m) => VT.TreeNode VT.Tree -> m (Maybe VT.Tree)
  rtn = return . Just . VT.mkNewTree

  amismatch :: (Show a) => a -> a -> VT.TreeNode VT.Tree
  amismatch x y = VT.TNBottom . VT.Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

  mkCnstrOrOther :: (RM.ReduceMonad s r m) => VT.Tree -> m (Maybe VT.Tree)
  mkCnstrOrOther t2 = do
    RuntimeParams{rpCreateCnstr = cc} <- asks (cfRuntimeParams . getConfig)
    logDebugStr $ printf "mergeLeftAtom: cc: %s, procOther: %s, %s" (show cc) (show ut1) (show ut2)
    if cc
      then do
        c <- mkCnstr v1 t2
        logDebugStr $ printf "mergeLeftAtom: constraint created, %s" (show c)
        retTr c
      else mergeLeftOther ut2 ut1 opAddr

mkCnstr :: (RM.ReduceMonad s r m) => VT.AtomV -> VT.Tree -> m VT.Tree
mkCnstr a cnstr = do
  let op = VT.mkMutableTree $ VT.mkUnifyOp [VT.mkAtomVTree a, cnstr]
  e <- buildASTExpr False op
  return $ VT.mkCnstrTree a e

mergeLeftBound :: (RM.ReduceMonad s r m) => (VT.Bounds, UTree) -> UTree -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeLeftBound (b1, ut1@(UTree{utDir = d1})) ut2@(UTree{utTC = tc2, utDir = d2}) opAddr = do
  let t2 = Cursor.tcFocus tc2
  case VT.treeNode t2 of
    VT.TNAtom ta2 -> do
      retTr $ mergeAtomBounds (d2, VT.amvAtom ta2) (d1, VT.bdsList b1)
    VT.TNBounds b2 -> do
      let res = mergeBoundList (d1, VT.bdsList b1) (d2, VT.bdsList b2)
      case res of
        Left err -> retTr (VT.mkBottomTree err)
        Right bs ->
          let
            r =
              foldl
                ( \acc x -> case x of
                    VT.BdIsAtom a -> (fst acc, Just a)
                    _ -> (x : fst acc, snd acc)
                )
                ([], Nothing)
                bs
           in
            case snd r of
              Just a -> retTr (VT.mkAtomTree a)
              Nothing -> retTr (VT.mkBoundsTree (fst r))
    VT.TNStruct s2 -> mergeLeftStruct (s2, ut2) ut1 opAddr
    _ -> mergeLeftOther ut2 ut1 opAddr

mergeAtomBounds :: (Path.BinOpDirect, VT.Atom) -> (Path.BinOpDirect, [VT.Bound]) -> VT.Tree
mergeAtomBounds (d1, a1) (d2, bs) =
  -- try to find the atom in the bounds list.
  foldl1 findAtom (map withBound bs)
 where
  ta1 = VT.mkAtomTree a1

  findAtom acc x = if acc == ta1 || x == ta1 then acc else x

  withBound :: VT.Bound -> VT.Tree
  withBound b =
    let
      r = mergeBounds (d1, VT.BdIsAtom a1) (d2, b)
     in
      case r of
        Left s -> VT.mkBottomTree s
        Right v -> case v of
          [x] -> case x of
            VT.BdIsAtom a -> VT.mkAtomTree a
            _ -> VT.mkBottomTree $ printf "unexpected bounds unification result: %s" (show x)
          _ -> VT.mkBottomTree $ printf "unexpected bounds unification result: %s" (show v)

-- TODO: regex implementation
-- Second argument is the pattern.
reMatch :: String -> String -> Bool
reMatch = (==)

-- TODO: regex implementation
-- Second argument is the pattern.
reNotMatch :: String -> String -> Bool
reNotMatch = (/=)

mergeBoundList :: (Path.BinOpDirect, [VT.Bound]) -> (Path.BinOpDirect, [VT.Bound]) -> Either String [VT.Bound]
mergeBoundList (d1, bs1) (d2, bs2) = case (bs1, bs2) of
  ([], _) -> return bs2
  (_, []) -> return bs1
  _ -> do
    bss <- manyToMany (d1, bs1) (d2, bs2)
    let bsMap = Map.fromListWith (++) (map (\b -> (VT.bdRep b, [b])) (concat bss))
    norm <- forM bsMap narrowBounds
    let m = Map.toList norm
    return $ concat $ map snd m
 where
  oneToMany :: (Path.BinOpDirect, VT.Bound) -> (Path.BinOpDirect, [VT.Bound]) -> Either String [VT.Bound]
  oneToMany (ld1, b) (ld2, ts) =
    let f x y = mergeBounds (ld1, x) (ld2, y)
     in do
          r <- mapM (`f` b) ts
          return $ concat r

  manyToMany :: (Path.BinOpDirect, [VT.Bound]) -> (Path.BinOpDirect, [VT.Bound]) -> Either String [[VT.Bound]]
  manyToMany (ld1, ts1) (ld2, ts2) =
    if ld1 == Path.R
      then mapM (\y -> oneToMany (ld2, y) (ld1, ts1)) ts2
      else mapM (\x -> oneToMany (ld1, x) (ld2, ts2)) ts1

-- | Narrow the bounds to the smallest set of bounds for the same bound type.
narrowBounds :: [VT.Bound] -> Either String [VT.Bound]
narrowBounds xs = case xs of
  [] -> return []
  (VT.BdNE _) : _ -> return xs
  x : rs ->
    let
      f acc y =
        if length acc == 1
          then mergeBounds (Path.L, acc !! 0) (Path.R, y)
          else Left "bounds mismatch"
     in
      foldM f [x] rs

mergeBounds :: (Path.BinOpDirect, VT.Bound) -> (Path.BinOpDirect, VT.Bound) -> Either String [VT.Bound]
mergeBounds db1@(d1, b1) db2@(_, b2) = case b1 of
  VT.BdNE a1 -> case b2 of
    VT.BdNE a2 -> return $ if a1 == a2 then [b1] else newOrdBounds
    VT.BdNumCmp c2 -> uNENumCmp a1 c2
    VT.BdStrMatch m2 -> uNEStrMatch a1 m2
    VT.BdType t2 -> uNEType a1 t2
    VT.BdIsAtom a2 -> if a1 == a2 then Left conflict else return [b2]
  VT.BdNumCmp c1 -> case b2 of
    VT.BdNumCmp c2 -> uNumCmpNumCmp c1 c2
    VT.BdStrMatch _ -> Left conflict
    VT.BdType t2 ->
      if t2 `elem` [VT.BdInt, VT.BdFloat, VT.BdNumber]
        then return [b1]
        else Left conflict
    VT.BdIsAtom a2 -> uNumCmpAtom c1 a2
    _ -> mergeBounds db2 db1
  VT.BdStrMatch m1 -> case b2 of
    VT.BdStrMatch m2 -> case (m1, m2) of
      (VT.BdReMatch _, VT.BdReMatch _) -> return $ if m1 == m2 then [b1] else newOrdBounds
      (VT.BdReNotMatch _, VT.BdReNotMatch _) -> return $ if m1 == m2 then [b1] else newOrdBounds
      _ -> return [b1, b2]
    VT.BdType t2 ->
      if t2 `elem` [VT.BdString]
        then return [b1]
        else Left conflict
    VT.BdIsAtom a2 -> uStrMatchAtom m1 a2
    _ -> mergeBounds db2 db1
  VT.BdType t1 -> case b2 of
    VT.BdType t2 -> if t1 == t2 then return [b1] else Left conflict
    VT.BdIsAtom a2 -> uTypeAtom t1 a2
    _ -> mergeBounds db2 db1
  VT.BdIsAtom a1 -> case b2 of
    VT.BdIsAtom a2 -> if a1 == a2 then return [b1] else Left conflict
    _ -> mergeBounds db2 db1
 where
  uNENumCmp :: VT.Atom -> VT.BdNumCmp -> Either String [VT.Bound]
  uNENumCmp a1 (VT.BdNumCmpCons o2 y) = do
    x <- case a1 of
      VT.Int x -> return $ VT.NumInt x
      VT.Float x -> return $ VT.NumFloat x
      _ -> Left conflict
    case o2 of
      VT.BdLT -> if x < y then Left conflict else return newOrdBounds
      VT.BdLE -> if x <= y then Left conflict else return newOrdBounds
      VT.BdGT -> if x > y then Left conflict else return newOrdBounds
      VT.BdGE -> if x >= y then Left conflict else return newOrdBounds

  uNEStrMatch :: VT.Atom -> VT.BdStrMatch -> Either String [VT.Bound]
  uNEStrMatch a1 m2 = do
    _ <- case a1 of
      VT.String x -> return x
      _ -> Left conflict
    case m2 of
      -- delay verification
      VT.BdReMatch _ -> return [b1, b2]
      VT.BdReNotMatch _ -> return [b1, b2]

  uNEType :: VT.Atom -> VT.BdType -> Either String [VT.Bound]
  uNEType a1 t2 = case a1 of
    VT.Bool _ -> if VT.BdBool == t2 then Left conflict else return newOrdBounds
    VT.Int _ -> if VT.BdInt == t2 then Left conflict else return newOrdBounds
    VT.Float _ -> if VT.BdFloat == t2 then Left conflict else return newOrdBounds
    VT.String _ -> if VT.BdString == t2 then Left conflict else return newOrdBounds
    -- TODO: null?
    _ -> Left conflict

  ncncGroup :: [([VT.BdNumCmpOp], [(VT.Number -> VT.Number -> Bool)])]
  ncncGroup =
    [ ([VT.BdLT, VT.BdLE], [(<=), (>)])
    , ([VT.BdGT, VT.BdGE], [(>=), (<)])
    ]

  uNumCmpNumCmp :: VT.BdNumCmp -> VT.BdNumCmp -> Either String [VT.Bound]
  uNumCmpNumCmp (VT.BdNumCmpCons o1 n1) (VT.BdNumCmpCons o2 n2) =
    let
      c1g = if o1 `elem` fst (ncncGroup !! 0) then ncncGroup !! 0 else ncncGroup !! 1
      c1SameGCmp = snd c1g !! 0
      c1OppGCmp = snd c1g !! 1
      isSameGroup = o2 `elem` (fst c1g)
      oppClosedEnds = sort [o1, o2] == [VT.BdLE, VT.BdGE]
     in
      if isSameGroup
        then return $ if c1SameGCmp n1 n2 then [b1] else [b2]
        else
          if
            | oppClosedEnds && n1 == n2 -> case n1 of
                VT.NumInt i -> return [VT.BdIsAtom $ VT.Int i]
                VT.NumFloat f -> return [VT.BdIsAtom $ VT.Float f]
            | c1OppGCmp n1 n2 -> return newOrdBounds
            | otherwise -> Left conflict

  uNumCmpAtom :: VT.BdNumCmp -> VT.Atom -> Either String [VT.Bound]
  uNumCmpAtom (VT.BdNumCmpCons o1 n1) a2 = do
    x <- case a2 of
      VT.Int x -> return $ VT.NumInt x
      VT.Float x -> return $ VT.NumFloat x
      _ -> Left conflict
    let r = case o1 of
          VT.BdLT -> x < n1
          VT.BdLE -> x <= n1
          VT.BdGT -> x > n1
          VT.BdGE -> x >= n1
    if r then return [b2] else Left conflict

  uStrMatchAtom :: VT.BdStrMatch -> VT.Atom -> Either String [VT.Bound]
  uStrMatchAtom m1 a2 = case a2 of
    VT.String s2 ->
      let r = case m1 of
            VT.BdReMatch p1 -> reMatch s2 p1
            VT.BdReNotMatch p1 -> reNotMatch s2 p1
       in if r then return [b2] else Left conflict
    _ -> Left conflict

  uTypeAtom :: VT.BdType -> VT.Atom -> Either String [VT.Bound]
  uTypeAtom t1 a2 =
    let r = case a2 of
          VT.Bool _ -> t1 == VT.BdBool
          VT.Int _ -> t1 `elem` [VT.BdInt, VT.BdNumber]
          VT.Float _ -> t1 `elem` [VT.BdFloat, VT.BdNumber]
          VT.String _ -> t1 == VT.BdString
          _ -> False
     in if r then return [b2] else Left conflict

  conflict :: String
  conflict = printf "bounds %s and %s conflict" (show b1) (show b2)

  newOrdBounds :: [VT.Bound]
  newOrdBounds = if d1 == Path.L then [b1, b2] else [b2, b1]

-- | mergeLeftOther is the sink of the unification process.
mergeLeftOther :: (RM.ReduceMonad s r m) => UTree -> UTree -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeLeftOther ut1@(UTree{utTC = tc1, utDir = d1}) ut2@(UTree{utTC = tc2}) opAddr = do
  let t1 = Cursor.tcFocus tc1
      t2 = Cursor.tcFocus tc2
  case VT.treeNode t1 of
    VT.TNRefCycle -> throwErrSt "ref cycle should not be used in merge"
    (VT.TNMutable mut) -> case mut of
      VT.Ref _ -> throwErrSt "ref should not be used in merge"
      VT.DisjOp _ -> throwErrSt "disjoin should not be used in merge"
      _ -> do
        rM1 <- Mutate.reduceToConcrete tc1
        maybe
          (return Nothing)
          (\r1 -> unifyBinUTrees (ut1{utTC = r1 `Cursor.setTCFocus` tc1}) ut2 opAddr)
          rM1

    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    (VT.TNAtomCnstr c1) -> do
      naM <- unifyBinUTrees (ut1{utTC = VT.mkNewTree (VT.TNAtom $ VT.cnsAtom c1) `Cursor.setTCFocus` tc1}) ut2 opAddr
      maybe
        (return Nothing)
        ( \na -> case VT.treeNode na of
            VT.TNBottom _ -> retTr na
            _ -> retTr t1
        )
        naM
    _ -> returnNotUnifiable ut1 ut2

returnNotUnifiable :: (RM.ReduceMonad s r m) => UTree -> UTree -> m (Maybe VT.Tree)
returnNotUnifiable (UTree{utTC = tc1, utDir = d1}) (UTree{utTC = tc2}) = do
  let t1 = Cursor.tcFocus tc1
      t2 = Cursor.tcFocus tc2
  case d1 of
    Path.L -> f t1 t2
    Path.R -> f t2 t1
 where
  f x y = do
    tx <- VT.showValueType x
    ty <- VT.showValueType y
    retTr $ VT.mkBottomTree $ printf "%s can not be unified with %s" tx ty

mergeLeftStruct :: (RM.ReduceMonad s r m) => (VT.Struct VT.Tree, UTree) -> UTree -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeLeftStruct (s1, ut1) ut2@(UTree{utTC = tc2}) opAddr = do
  let t2 = Cursor.tcFocus tc2
  if
    -- When the left struct is an empty struct with embedded fields (an embedded value), we can get the reduced left
    -- struct and unify the reduced result (which should be the embeded value) with right value.
    -- For example, {1,1} & 1 -> 1 & 1 & 1
    | VT.hasEmptyFields s1 && not (null $ VT.stcEmbeds s1) -> do
        uts <-
          foldM
            ( \acc i -> do
                subTC <- TCOps.goDownTCSegMust (Path.StructTASeg (Path.EmbedTASeg i)) (utTC ut1)
                return $ ut1{utTC = subTC, utEmbedID = Just i} : acc
            )
            []
            (IntMap.keys $ VT.stcEmbeds s1)
        unifyUTrees (if utDir ut1 == Path.L then uts ++ [ut2] else ut2 : uts) opAddr
    -- -- TODO: reduce embedded
    -- r1 <- reduceUnifyMutTreeArg (Path.toBinOpTASeg (utDir ut1))
    -- case VT.treeNode r1 of
    -- VT.TNMutable _ -> return $ VT.mkNewTree VT.TNStub -- No concrete value exists.
    -- _ -> mergeBinUTrees (ut1{utTC = r1 `Cursor.setTCFocus` utTC ut1}) ut2
    -- When the left is an empty struct and the right value is an embedded value of type non-struct, meaning we are
    -- using the embedded value to replace the struct.
    -- For example, the parent struct is {a: 1, b}, and the function is {a: 1} & b.
    | VT.hasEmptyFields s1 && isJust (utEmbedID ut2) -> case VT.treeNode t2 of
        VT.TNStruct s2 -> mergeStructs (s1, ut1) (s2, ut2)
        _ -> retTr t2
    | otherwise -> case VT.treeNode t2 of
        VT.TNStruct s2 -> mergeStructs (s1, ut1) (s2, ut2)
        _ -> mergeLeftOther ut2 ut1 opAddr

{- | unify two structs.

The s1 is made the left struct, and s2 is made the right struct.

For closedness, unification only generates a closed struct but not a recursively closed struct since to close a struct
recursively, the only way is to reference the struct via a #ident.
-}
mergeStructs ::
  (RM.ReduceMonad s r m) =>
  (VT.Struct VT.Tree, UTree) ->
  (VT.Struct VT.Tree, UTree) ->
  m (Maybe VT.Tree)
mergeStructs (s1, ut1@UTree{utDir = Path.L}) (s2, ut2) = do
  checkRes <- do
    rE1 <- _preprocessBlock (utTC ut1) s1
    rE2 <- _preprocessBlock (utTC ut2) s2
    return $ do
      r1 <- rE1
      r2 <- rE2
      return (r1, r2)
  case checkRes of
    Left err -> retTr err
    Right (r1, r2) -> mergeStructsInner (utEmbedID ut1, r1) (utEmbedID ut2, r2)
mergeStructs dt1@(_, UTree{utDir = Path.R}) dt2 = mergeStructs dt2 dt1

mergeStructsInner ::
  (RM.ReduceMonad s r m) =>
  (Maybe Int, VT.Struct VT.Tree) ->
  (Maybe Int, VT.Struct VT.Tree) ->
  m (Maybe VT.Tree)
mergeStructsInner (eidM1, s1) (eidM2, s2) = do
  when (isJust eidM1 && isJust eidM2) $ throwErrSt "both structs are embedded, not allowed"

  sid <- RM.allocRMObjID
  let merged = fieldsToStruct sid (_unionFields (s1, eidM1) (s2, eidM2)) (s1, eidM1) (s2, eidM2)
  -- in reduce, the new combined fields will be checked by the combined patterns.
  retTr merged

fieldsToStruct ::
  Int -> [(String, VT.Field VT.Tree)] -> (VT.Struct VT.Tree, Maybe Int) -> (VT.Struct VT.Tree, Maybe Int) -> VT.Tree
fieldsToStruct sid fields (st1, eidM1) (st2, eidM2) =
  VT.mkStructTree $
    VT.emptyStruct
      { VT.stcID = sid
      , VT.stcOrdLabels = map fst fields
      , VT.stcBlockIdents = case (eidM1, eidM2) of
          (Nothing, Nothing) -> VT.stcBlockIdents st1 `Set.union` VT.stcBlockIdents st2
          (Just _, Nothing) -> VT.stcBlockIdents st2
          (Nothing, Just _) -> VT.stcBlockIdents st1
          (Just _, Just _) -> Set.empty
      , VT.stcFields = Map.fromList fields
      , VT.stcLets = VT.stcLets st1 `Map.union` VT.stcLets st2
      , VT.stcDynFields = combinedPendSubs
      , VT.stcCnstrs = combinedPatterns
      , VT.stcEmbeds = case (eidM1, eidM2) of
          (Nothing, Nothing) -> VT.stcEmbeds st1 `IntMap.union` VT.stcEmbeds st2
          -- If the any is embedded, we should not add embedings as reducing the merged embeddings would cause infinite
          -- evaluation.
          _ -> IntMap.empty
      , VT.stcClosed = VT.stcClosed st1 || VT.stcClosed st2
      , VT.stcPerms =
          let neitherEmbedded = isNothing eidM1 && isNothing eidM2
           in -- st1 and st2 could be both closed.
              VT.stcPerms st1
                ++ VT.stcPerms st2
                -- st2 as an opposite struct of st1
                ++ [mkPermItem st1 st2 | neitherEmbedded && VT.stcClosed st1]
                -- st1 as an opposite struct of st2
                ++ [mkPermItem st2 st1 | neitherEmbedded && VT.stcClosed st2]
      }
 where
  combinedPendSubs = IntMap.union (VT.stcDynFields st1) (VT.stcDynFields st2)
  -- The combined patterns are the patterns of the first struct and the patterns of the second struct.
  combinedPatterns = IntMap.union (VT.stcCnstrs st1) (VT.stcCnstrs st2)

  mkPermItem :: VT.Struct VT.Tree -> VT.Struct VT.Tree -> VT.PermItem
  mkPermItem struct opStruct =
    VT.PermItem
      { VT.piCnstrs = Set.fromList $ IntMap.keys $ VT.stcCnstrs struct
      , -- TODO: exclude let bindings
        VT.piLabels = Set.fromList $ VT.stcOrdLabels struct
      , VT.piDyns = Set.fromList $ IntMap.keys $ VT.stcDynFields struct
      , -- TODO: exclude let bindings
        VT.piOpLabels = Set.fromList $ VT.stcOrdLabels opStruct
      , VT.piOpDyns = Set.fromList $ IntMap.keys $ VT.stcDynFields opStruct
      }

{- | Merge two fields.

The structs can not be both embedded.
-}
_unionFields :: (VT.Struct VT.Tree, Maybe Int) -> (VT.Struct VT.Tree, Maybe Int) -> [(String, VT.Field VT.Tree)]
_unionFields (st1, eidM1) (st2, eidM2) =
  foldr
    ( \label acc ->
        let
          f1M = VT.lookupStructField label st1
          f2M = VT.lookupStructField label st2
         in
          if
            | label `Set.member` l1Set && label `Set.member` l2Set
            , Just sf1 <- f1M
            , Just sf2 <- f2M ->
                let x = _mkUnifiedField sf1 sf2
                    -- If either of the structs is embedded, we need to add the id to the objects set.
                    ufield = case catMaybes [eidM1, eidM2] of
                      [i] -> x{VT.ssfObjects = Set.insert i (VT.ssfObjects x)}
                      _ -> x
                 in (label, ufield) : acc
            | label `Set.member` l1Set, Just sf1 <- f1M -> (label, sf1) : acc
            | label `Set.member` l2Set, Just sf2 <- f2M -> (label, sf2) : acc
            | otherwise -> acc
    )
    []
    unionLabels
 where
  fields1 = VT.stcFields st1
  fields2 = VT.stcFields st2
  l1Set = Map.keysSet fields1
  l2Set = Map.keysSet fields2

  -- Put the labels in the order of the first struct and append the labels that are not in the first struct.
  unionLabels =
    VT.stcOrdLabels st1
      ++ foldr (\l acc -> if l `Set.member` l1Set then acc else l : acc) [] (VT.stcOrdLabels st2)

-- | Merge two fields by creating a unify node with merged attributes.
_mkUnifiedField :: VT.Field VT.Tree -> VT.Field VT.Tree -> VT.Field VT.Tree
_mkUnifiedField sf1 sf2 =
  let
    -- No original node exists yet
    unifyValOp = VT.mkUnifyOp [VT.ssfValue sf1, VT.ssfValue sf2]
    unifiedBaseRaw = case catMaybes [VT.ssfBaseRaw sf1, VT.ssfBaseRaw sf2] of
      [br1, br2] -> Just $ VT.mkMutableTree $ VT.mkUnifyOp [br1, br2]
      [br] -> Just br
      _ -> Nothing
   in
    VT.Field
      { VT.ssfValue = VT.mkMutableTree unifyValOp
      , VT.ssfBaseRaw = unifiedBaseRaw
      , VT.ssfAttr = VT.mergeAttrs (VT.ssfAttr sf1) (VT.ssfAttr sf2)
      , VT.ssfObjects = VT.ssfObjects sf1 `Set.union` VT.ssfObjects sf2
      }

{- | Preprocess the block.

It does the followings:

1. Validate if the identifier of the any reference in the sub tree is in the scope.
2. Rewrite the identifier of the let bindings in the block with the sid.

According to spec, A block is a possibly empty sequence of declarations.

The scope of a declared identifier is the extent of source text in which the identifier denotes the specified field,
alias, or package.
-}
_preprocessBlock ::
  (RM.ReduceMonad s r m) =>
  TCOps.TrCur ->
  VT.Struct VT.Tree ->
  m (Either VT.Tree (VT.Struct VT.Tree))
_preprocessBlock blockTC block = do
  RM.debugSpanRM "_preprocessBlock" blockTC $ do
    rM <- _validateRefIdents blockTC
    logDebugStr $ printf "_preprocessBlock: rM: %s" (show rM)
    maybe
      ( do
          let
            sid = VT.stcID block
            blockAddr = Cursor.tcTreeAddr blockTC
          structT <- _appendSIDToLetRef blockAddr sid blockTC
          -- rewrite all ident keys of the let bindings map with the sid.
          case VT.treeNode structT of
            VT.TNStruct struct -> do
              let
                blockIdents =
                  Set.fromList $
                    map
                      (\k -> if k `Map.member` VT.stcLets struct then k ++ "_" ++ show sid else k)
                      (Set.toList $ VT.stcBlockIdents struct)
                lets = Map.fromList $ map (\(k, v) -> (k ++ "_" ++ show sid, v)) (Map.toList $ VT.stcLets struct)
                newStruct = struct{VT.stcBlockIdents = blockIdents, VT.stcLets = lets}
              logDebugStr $ printf "_preprocessBlock: newStruct: %s" (show $ VT.mkStructTree newStruct)
              return $ Right newStruct
            _ -> throwErrSt $ printf "tree must be struct, but got %s" (show structT)
      )
      (return . Left)
      rM

{- | Validate if the identifier of the any reference in the sub tree is in the scope.

This is needed because after merging two blocks, some not found references could become valid because the merged block
could have the identifier. Because we are destroying the block and replace it with the merged block, we need to check
all sub references to make sure later reducing them will not cause them to find newly created identifiers.
-}
_validateRefIdents :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m (Maybe VT.Tree)
_validateRefIdents _tc =
  snd <$> TCOps.traverseTC _extAllSubNodes find (_tc, Nothing)
 where
  find (tc, acc) = do
    case VT.treeNode (Cursor.tcFocus tc) of
      VT.TNMutable (VT.Ref (VT.Reference{VT.refArg = VT.RefPath ident _})) -> do
        m <- RefSys.searchTCIdent ident tc
        logDebugStr $ printf "_validateRefIdents: ident: %s, m: %s" ident (show m)
        maybe
          (return (tc, Just $ VT.mkBottomTree $ printf "identifier %s is not found" ident))
          (const $ return (tc, acc))
          m
      _ -> return (tc, acc)

{- | Append the ident of all references in the tree cursor with the sid if the ident references a let binding which is
declared in the block specified by the block address.

This makes sure after merging two structs, two same references from two different structs referencing the same let name
will not conflict with each other.
-}
_appendSIDToLetRef :: (RM.ReduceMonad s r m) => Path.TreeAddr -> Int -> TCOps.TrCur -> m VT.Tree
_appendSIDToLetRef blockAddr sid _tc =
  Cursor.tcFocus <$> TCOps.traverseTCSimple _extAllSubNodes rewrite _tc
 where
  rewrite tc =
    let focus = Cursor.tcFocus tc
     in case VT.treeNode focus of
          VT.TNMutable (VT.Ref ref@(VT.Reference{VT.refArg = VT.RefPath ident _})) -> do
            m <- RefSys.searchTCIdent ident tc
            logDebugStr $ printf "_appendSIDToLetRef: ident: %s, m: %s" ident (show m)

            maybe
              (return focus)
              ( \(addr, isLB) -> do
                  logDebugStr $
                    printf
                      "_appendSIDToLetRef: rewrite %s, blockAddr: %s, addr: %s"
                      ident
                      (show blockAddr)
                      (show addr)
                  if isLB && (Just blockAddr == Path.initTreeAddr addr)
                    then do
                      let newFocus = VT.setTN focus (VT.TNMutable $ VT.Ref $ append ref)
                      return newFocus
                    else return focus
              )
              ( do
                  (x, y) <- m
                  return (Cursor.tcTreeAddr x, y)
              )
          _ -> return focus

  append :: VT.Reference VT.Tree -> VT.Reference VT.Tree
  append ref@(VT.Reference{VT.refArg = VT.RefPath ident sels}) =
    ref{VT.refArg = VT.RefPath (ident ++ "_" ++ show sid) sels}
  append r = r

-- | Extended version of all sub nodes of the tree, including patterns, dynamic fields and let bindings.
_extAllSubNodes :: VT.Tree -> [(Path.TASeg, VT.Tree)]
_extAllSubNodes x = VT.subNodes x ++ rawNodes x
 where
  rawNodes :: VT.Tree -> [(Path.TASeg, VT.Tree)]
  rawNodes t = case VT.treeNode t of
    VT.TNStruct struct ->
      [(Path.StructTASeg $ Path.PatternTASeg i 1, VT.scsValue c) | (i, c) <- IntMap.toList $ VT.stcCnstrs struct]
        ++ [(Path.StructTASeg $ Path.DynFieldTASeg i 1, VT.dsfValue dsf) | (i, dsf) <- IntMap.toList $ VT.stcDynFields struct]
        ++ [(Path.StructTASeg $ Path.LetTASeg s, VT.lbValue lb) | (s, lb) <- Map.toList $ VT.stcLets struct]
        ++ [(Path.StructTASeg $ Path.EmbedTASeg i, VT.embValue emb) | (i, emb) <- IntMap.toList $ VT.stcEmbeds struct]
    _ -> []

mergeLeftDisj :: (RM.ReduceMonad s r m) => (VT.Disj VT.Tree, UTree) -> UTree -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeLeftDisj (dj1, ut1) ut2@(UTree{utTC = tc2}) opAddr = do
  -- RM.withAddrAndFocus $ \addr _ ->
  --   logDebugStr $ printf "mergeLeftDisj: addr: %s, dj: %s, right: %s" (show addr) (show ut1) (show ut2)
  let t2 = Cursor.tcFocus tc2
  case VT.treeNode t2 of
    VT.TNMutable _ -> mergeLeftOther ut2 ut1 opAddr
    VT.TNAtomCnstr _ -> mergeLeftOther ut2 ut1 opAddr
    VT.TNRefCycle -> mergeLeftOther ut2 ut1 opAddr
    VT.TNDisj dj2 -> mergeDisjWithDisj (dj1, ut1) (dj2, ut2) opAddr
    -- this is the case for a disjunction unified with a value.
    _ -> mergeDisjWithVal (dj1, ut1) ut2 opAddr

-- Note: isEmbedded is still required. Think about the following values,
-- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
-- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
-- In current CUE's implementation, CUE puts the fields of the single value first.
mergeDisjWithVal :: (RM.ReduceMonad s r m) => (VT.Disj VT.Tree, UTree) -> UTree -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeDisjWithVal (dj1, _ut1@(UTree{utDir = fstDir, utTC = tc1})) _ut2 opAddr = RM.debugSpanOpRM "mergeDisjWithVal" opAddr $ do
  uts1 <- utsFromDisjs (length $ VT.dsjDisjuncts dj1) _ut1
  let defIdxes1 = VT.dsjDefIndexes dj1
  if fstDir == Path.L
    -- uts1 & ut2 generates a m x 1 matrix.
    then do
      matrix <- mapM (\ut1 -> unifyBinUTrees ut1 _ut2 opAddr) uts1
      treeFromMatrix (defIdxes1, []) (length uts1, 1) [matrix]
    -- ut2 & uts1 generates a 1 x m matrix.
    else do
      matrix <- mapM (\ut1 -> unifyBinUTrees ut1 _ut2 opAddr) uts1
      treeFromMatrix ([], defIdxes1) (1, length uts1) (map (: []) matrix)

{- | Unify two disjuncts.

We do not need to compute the unification of default values since they are already unified in the disjuncts. We just
need to pick the correct indexes of the default values from the matrix.

Some rules for unifying disjuncts:

U0: ⟨v1⟩ & ⟨v2⟩         => ⟨v1&v2⟩
U1: ⟨v1, d1⟩ & ⟨v2⟩     => ⟨v1&v2, d1&v2⟩
U2: ⟨v1, d1⟩ & ⟨v2, d2⟩ => ⟨v1&v2, d1&d2⟩
-}
mergeDisjWithDisj ::
  (RM.ReduceMonad s r m) => (VT.Disj VT.Tree, UTree) -> (VT.Disj VT.Tree, UTree) -> Path.TreeAddr -> m (Maybe VT.Tree)
mergeDisjWithDisj (dj1, _ut1@(UTree{utDir = fstDir, utTC = tc1})) (dj2, _ut2) opAddr =
  RM.debugSpanOpRM "mergeDisjWithDisj" opAddr $ do
    uts1 <- utsFromDisjs (length $ VT.dsjDisjuncts dj1) _ut1
    uts2 <- utsFromDisjs (length $ VT.dsjDisjuncts dj2) _ut2
    let
      defIdxes1 = VT.dsjDefIndexes dj1
      defIdxes2 = VT.dsjDefIndexes dj2

    if fstDir == Path.L
      -- uts1 & uts2 generates a m x n matrix.
      then do
        matrix <- mapM (\ut1 -> mapM (\ut2 -> unifyBinUTrees ut1 ut2 opAddr) uts2) uts1
        treeFromMatrix (defIdxes1, defIdxes2) (length uts1, length uts2) matrix
      -- uts2 & uts1 generates a n x m matrix.
      else do
        matrix <- mapM (\ut2 -> mapM (\ut1 -> unifyBinUTrees ut2 ut1 opAddr) uts1) uts2
        treeFromMatrix (defIdxes2, defIdxes1) (length uts2, length uts1) matrix

utsFromDisjs :: (Env r s m) => Int -> UTree -> m [UTree]
utsFromDisjs n ut@(UTree{utTC = tc}) = do
  mapM
    ( \i -> do
        djTC <- TCOps.goDownTCSegMust (Path.DisjDisjunctTASeg i) tc
        return $ ut{utTC = djTC}
    )
    [0 .. (n - 1)]

treeFromMatrix :: (Env r s m) => ([Int], [Int]) -> (Int, Int) -> [[Maybe VT.Tree]] -> m (Maybe VT.Tree)
treeFromMatrix (lDefIndexes, rDefIndexes) (m, n) matrix = do
  let defIndexes = case (lDefIndexes, rDefIndexes) of
        ([], []) -> []
        -- For each i in the left default indexes, we have a list of default values, x<i,0>, x<i,1>, ..., x<i,(n-1)>
        (ls, []) -> concatMap (\i -> map (+ (i * n)) [0 .. n - 1]) ls
        -- For each j in the right default indexes, we have a list of default values, x<0,j>, x<1,j>, ..., x<(m-1),j>
        ([], rs) -> concatMap (\j -> map (\i -> (i * n) + j) [0 .. m - 1]) rs
        -- For each i in the left default indexes, we have one default value, x<i,j>.
        (ls, rs) -> concatMap (\i -> map (+ (i * n)) rs) ls
      disjunctsM = concat matrix
  maybe
    (return Nothing)
    ( \disjuncts ->
        return $ Just $ VT.mkDisjTree $ VT.emptyDisj{VT.dsjDefIndexes = defIndexes, VT.dsjDisjuncts = disjuncts}
    )
    (sequence disjunctsM)

{- | Check the labels' permission.

The focus of the tree must be a struct.
-}
checkLabelsPerm ::
  (RM.ReduceMonad s r m) =>
  Set.Set String ->
  IntMap.IntMap (VT.StructCnstr VT.Tree) ->
  Bool ->
  Bool ->
  Set.Set String ->
  TCOps.TrCur ->
  m TCOps.TrCur
checkLabelsPerm baseLabels baseCnstrs isBaseClosed isEitherEmbedded labelsSet tc =
  foldM
    ( \acc opLabel ->
        if isTreeBottom (Cursor.tcFocus acc)
          then return acc
          else
            checkPerm baseLabels baseCnstrs isBaseClosed isEitherEmbedded opLabel acc
              >>= maybe
                (return acc)
                -- If the checkPerm returns a bottom, update the bottom to the struct.
                ( \err -> return (err `Cursor.setTCFocus` acc)
                -- RM.mustStruct $ \_ -> do
                -- field <-
                --   maybe
                --     (throwErrSt "struct-value is not found")
                --     return
                --     (VT.lookupStructField opLabel struct)
                -- RM.modifyTMTN $ VT.TNStruct $ VT.updateStructField opLabel (btm `VT.updateFieldValue` field) struct
                )
    )
    tc
    labelsSet

checkPerm ::
  (RM.ReduceMonad s r m) =>
  Set.Set String ->
  IntMap.IntMap (VT.StructCnstr VT.Tree) ->
  Bool ->
  Bool ->
  String ->
  TCOps.TrCur ->
  m (Maybe VT.Tree)
checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel tc =
  RM.debugSpanArgsRM
    "checkPerm"
    ( printf
        "newLabel: %s, baseLabels: %s, baseAllCnstrs: %s, isBaseClosed: %s, isEitherEmbedded: %s"
        (show newLabel)
        (show $ Set.toList baseLabels)
        (show $ IntMap.toList baseAllCnstrs)
        (show isBaseClosed)
        (show isEitherEmbedded)
    )
    tc
    $ _checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel tc

_checkPerm ::
  (RM.ReduceMonad s r m) =>
  Set.Set String ->
  IntMap.IntMap (VT.StructCnstr VT.Tree) ->
  Bool ->
  Bool ->
  String ->
  TCOps.TrCur ->
  m (Maybe VT.Tree)
_checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel tc
  | not isBaseClosed || isEitherEmbedded = return Nothing
  | newLabel `Set.member` baseLabels = return Nothing
  | otherwise = do
      -- A "new" field is allowed if there is at least one pattern that matches the field.
      allowed <-
        foldM
          ( \acc cnstr ->
              if acc
                then return acc
                else do
                  let pat = VT.scsPattern cnstr
                  r <- patMatchLabel pat newLabel tc
                  logDebugStr $ printf "checkPerm: pat: %s, newLabel: %s, r: %s" (show pat) newLabel (show r)
                  return r
          )
          -- By default, "new" label is not allowed.
          False
          (IntMap.elems baseAllCnstrs)

      logDebugStr $ printf "checkPerm: newLabel: %s, allowed: %s" (show newLabel) (show allowed)

      -- A field is disallowed if no pattern exists or no pattern matches the label.
      if allowed
        then return Nothing
        else return . Just $ VT.mkBottomTree $ printf "%s is not allowed" newLabel

-- | Returns whether the pattern matches the label.
patMatchLabel :: (RM.ReduceMonad s r m) => VT.Tree -> String -> TCOps.TrCur -> m Bool
patMatchLabel pat name tc = case VT.treeNode pat of
  VT.TNMutable mut
    -- If the mutable is a reference or an index, then we should try to use the value of the mutable.
    | Nothing <- VT.getSFuncFromMutable mut ->
        maybe
          (return False)
          ( -- The lable mutable might be a reference. The pending element should not be marked as deleted.
            \val -> case VT.treeNode val of
              -- If the mutable is a reference and it currently has no value.
              VT.TNStub -> return False
              _ -> match val
          )
          (VT.getMutVal mut)
  _ -> match pat
 where
  match :: (RM.ReduceMonad s r m) => VT.Tree -> m Bool
  match v = do
    MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
    let
      segOp = VT.mkMutableTree $ VT.mkUnifyOp [VT.mkAtomTree $ VT.String name, v]
    -- Since segOps a list of unify nodes that unify the string with the bounds, we can use RM.inDiscardSubTM to
    -- evaluate the unify nodes and get the strings.
    r <-
      -- We should not create constraints in this context because we should not delay the evaluation of the
      -- pattern.
      local
        ( \r ->
            let conf = getConfig r
             in setConfig r conf{cfRuntimeParams = (cfRuntimeParams conf){rpCreateCnstr = False}}
        )
        $ reduce (segOp `Cursor.setTCFocus` tc)
    -- Filter the strings from the results. Non-string results are ignored meaning the fields do not match the
    -- pattern.
    case VT.getAtomFromTree r of
      Just (VT.String _) -> return True
      _ -> return False
