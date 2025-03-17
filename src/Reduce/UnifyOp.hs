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
  TreeOp (isTreeBottom),
 )
import Control.Monad (foldM, forM)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (asks, local)
import qualified Cursor
import qualified Data.IntMap.Strict as IntMap
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe)
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified TCursorOps
import Text.Printf (printf)
import Util (debugSpan, logDebugStr)
import qualified Value.Tree as VT

{- | Reduce the tree that is a mutable to the form that can be used in the unify operation.

If the tree is a struct or a list, no sub nodes need to be reduced as these nodes will be merged and reduced in a new
scope.
-}
shallowReduce :: (RM.ReduceMonad s r m) => m ()
shallowReduce = RM.withAddrAndFocus $ \addr _ -> debugSpan (printf "shallowReduce, addr: %s" (show addr)) $ do
  -- save the original tree before effects are applied to the focus of the tree.
  orig <- RM.getRMTree
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNMutable _ ->
      local
        ( \r ->
            let fns = MutEnv.getFuncs r
             in MutEnv.setFuncs r fns{MutEnv.fnReduce = shallowReduce}
        )
        Mutate.mutate
    VT.TNStub -> throwErrSt "stub node should not be reduced"
    _ -> return ()

  -- Overwrite the treenode of the raw with the reduced tree's VT.TreeNode to preserve tree attributes.
  RM.withTree $ \t -> RM.putRMTree $ VT.setTN orig (VT.treeNode t)

{- | Reduce the argument of the mutable.

If nothing concrete can be returned, then the original argument is returned.
-}
reduceUnifyArg :: (RM.ReduceMonad s r m) => Path.TASeg -> VT.Tree -> m VT.Tree
reduceUnifyArg seg sub = RM.withAddrAndFocus $ \addr _ ->
  debugSpan (printf "reduceMutableArg, addr: %s, seg: %s" (show addr) (show seg)) $ do
    m <-
      Mutate.mutValToArgsRM
        seg
        sub
        ( do
            shallowReduce
            RM.withTree $ \x -> return $ case VT.treeNode x of
              VT.TNMutable mut -> Just $ fromMaybe sub (VT.getMutVal mut)
              _ -> Just x
        )
    return $ fromJust m

-- | Create a unify node from two UTrees.
mkUnifyUTreesNode :: UTree -> UTree -> VT.Mutable VT.Tree
mkUnifyUTreesNode ut1 ut2 =
  -- Values of UTrees are created to receive the updated values.
  VT.mkBinaryOp AST.Unify (\a b -> unifyUTrees (ut1{utVal = a}) (ut2{utVal = b})) (utVal ut1) (utVal ut2)

-- | UTree is a tree with a direction and an embedded flag.
data UTree = UTree
  { utVal :: VT.Tree
  , utDir :: Path.BinOpDirect
  , utEmbedded :: Bool
  -- ^ Whether the tree is embedded in a struct.
  }

instance Show UTree where
  show (UTree t d e) = printf "(%s,embed:%s,\n%s)" (show d) (show e) (show t)

unify :: (RM.ReduceMonad s r m) => VT.Tree -> VT.Tree -> m ()
unify t1 t2 = unifyUTrees (UTree t1 Path.L False) (UTree t2 Path.R False)

-- | Unify the right embedded tree with the left tree.
unifyREmbedded :: (RM.ReduceMonad s r m) => VT.Tree -> VT.Tree -> m ()
unifyREmbedded t1 t2 = unifyUTrees (UTree t1 Path.L False) (UTree t2 Path.R True)

{- | Unify UTrees.

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
-}
unifyUTrees :: (RM.ReduceMonad s r m) => UTree -> UTree -> m ()
unifyUTrees ut1@(UTree{utVal = t1}) ut2@(UTree{utVal = t2}) = RM.withAddrAndFocus $ \addr _ ->
  debugSpan (printf ("unifying, addr: %s:, %s" ++ "\n" ++ "with %s") (show addr) (show ut1) (show ut2)) $ do
    -- Each case should handle embedded case when the left value is embedded.
    case (VT.treeNode t1, VT.treeNode t2) of
      -- VT.CnstredVal has the highest priority, because the real operand is the value of the VT.CnstredVal.
      (VT.TNCnstredVal c, _) -> unifyLeftCnstredVal (c, ut1) ut2
      (_, VT.TNCnstredVal c) -> unifyLeftCnstredVal (c, ut2) ut1
      (VT.TNBottom _, _) -> RM.putRMTree t1
      (_, VT.TNBottom _) -> RM.putRMTree t2
      (VT.TNTop, _) -> unifyLeftTop ut1 ut2
      (_, VT.TNTop) -> unifyLeftTop ut2 ut1
      (VT.TNAtom a1, _) -> unifyLeftAtom (a1, ut1) ut2
      -- Below is the earliest time to create a constraint
      (_, VT.TNAtom a2) -> unifyLeftAtom (a2, ut2) ut1
      (VT.TNDisj dj1, _) -> unifyLeftDisj (dj1, ut1) ut2
      (_, VT.TNDisj dj2) -> unifyLeftDisj (dj2, ut2) ut1
      (VT.TNStruct s1, _) -> unifyLeftStruct (s1, ut1) ut2
      (_, VT.TNStruct s2) -> unifyLeftStruct (s2, ut2) ut1
      (VT.TNBounds b1, _) -> unifyLeftBound (b1, ut1) ut2
      (_, VT.TNBounds b2) -> unifyLeftBound (b2, ut2) ut1
      _ -> unifyLeftOther ut1 ut2

    -- close the merged tree
    RM.withTree $ \t ->
      RM.putRMTree (t{VT.treeRecurClosed = VT.treeRecurClosed t1 || VT.treeRecurClosed t2})

    MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
    -- reduce the merged tree
    RM.withTree $ \t -> case VT.treeNode t of
      -- If the unify result is incomplete, skip the reduction.
      VT.TNStub -> return ()
      _ -> reduce

unifyLeftCnstredVal :: (RM.ReduceMonad s r m) => (VT.CnstredVal VT.Tree, UTree) -> UTree -> m ()
unifyLeftCnstredVal (c1, ut1) ut2@UTree{utVal = t2} = do
  unifyUTrees ut1{utVal = VT.cnsedVal c1} ut2

  eM2 <- case VT.treeNode t2 of
    -- ut2 was VT.CnstredVal, we need to merge original expressions.
    VT.TNCnstredVal c2 -> return $ VT.cnsedOrigExpr c2
    -- ut2 was not VT.CnstredVal, we need to build the original expression.
    _ -> Just <$> buildASTExpr False t2

  e <- case catMaybes [VT.cnsedOrigExpr c1, eM2] of
    -- If only one side has an original expression, we can use it directly.
    [e] -> return e
    -- If both sides have original expressions, we need to unify them.
    [e1, e2] -> return $ AST.binaryOpCons AST.Unify e1 e2
    _ -> throwErrSt "both CnstredVals are empty"

  -- Re-encapsulate the VT.CnstredVal.
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNCnstredVal c -> RM.modifyRMTN (VT.TNCnstredVal $ c{VT.cnsedOrigExpr = Just e})
    _ -> RM.modifyRMTN (VT.TNCnstredVal $ VT.CnstredVal t (Just e))

unifyLeftTop :: (RM.ReduceMonad s r m) => UTree -> UTree -> m ()
unifyLeftTop ut1 ut2 = do
  case VT.treeNode . utVal $ ut2 of
    -- If the left top is embedded in the right struct, we can immediately put the top into the tree without worrying
    -- any future existing/new fields. Because for example {_, a: 1} is equivalent to _ & {a: 1}. This follows the
    -- behavior of the spec:
    -- The result of { A } is A for any A (including definitions).
    -- Notice that this is different from the behavior of the latest CUE. The latest CUE would do the following:
    -- {_, _h: int} & {_h: "hidden"} -> _|_.
    VT.TNStruct _ | utEmbedded ut1 -> RM.putRMTree (utVal ut1)
    _ -> RM.putRMTree (utVal ut2)

unifyLeftAtom :: (RM.ReduceMonad s r m) => (VT.AtomV, UTree) -> UTree -> m ()
unifyLeftAtom (v1, ut1@(UTree{utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = do
  case (VT.amvAtom v1, VT.treeNode t2) of
    (VT.String x, VT.TNAtom s)
      | VT.String y <- VT.amvAtom s -> putTree $ if x == y then VT.TNAtom v1 else amismatch x y
    (VT.Int x, VT.TNAtom s)
      | VT.Int y <- VT.amvAtom s -> putTree $ if x == y then VT.TNAtom v1 else amismatch x y
    (VT.Float x, VT.TNAtom s)
      | VT.Float y <- VT.amvAtom s -> putTree $ if x == y then VT.TNAtom v1 else amismatch x y
    (VT.Bool x, VT.TNAtom s)
      | VT.Bool y <- VT.amvAtom s -> putTree $ if x == y then VT.TNAtom v1 else amismatch x y
    (VT.Null, VT.TNAtom s) | VT.Null <- VT.amvAtom s -> putTree $ VT.TNAtom v1
    (_, VT.TNBounds b) -> do
      logDebugStr $ printf "unifyLeftAtom, %s with VT.Bounds: %s" (show v1) (show t2)
      RM.putRMTree $ unifyAtomBounds (d1, VT.amvAtom v1) (d2, VT.bdsList b)
    (_, VT.TNAtomCnstr c) ->
      if v1 == VT.cnsAtom c
        then putCnstr (VT.cnsAtom c)
        else RM.putRMTree . VT.mkBottomTree $ printf "values mismatch: %s != %s" (show v1) (show $ VT.cnsAtom c)
    (_, VT.TNDisj dj2) -> do
      logDebugStr $ printf "unifyLeftAtom: VT.TNDisj %s, %s" (show t2) (show v1)
      unifyLeftDisj (dj2, ut2) ut1
    (_, VT.TNMutable mut2)
      | (VT.SFunc m2) <- mut2 -> case VT.sfnType m2 of
          -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
          -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
          -- marked disjunction.
          VT.DisjMutable -> unifyLeftOther ut2 ut1
          _ -> procOther
      | otherwise -> procOther
    (_, VT.TNRefCycle _) -> procOther
    -- If the left atom is embedded in the right struct and there is no fields and no pending dynamic fields, we can
    -- immediately put the atom into the tree without worrying any future new fields. This is what CUE currently
    -- does.
    (_, VT.TNStruct s2) | utEmbedded ut1 && VT.hasEmptyFields s2 -> putTree (VT.TNAtom v1)
    _ -> unifyLeftOther ut1 ut2
 where
  putTree :: (RM.ReduceMonad s r m) => VT.TreeNode VT.Tree -> m ()
  putTree n = RM.putRMTree $ VT.mkNewTree n

  amismatch :: (Show a) => a -> a -> VT.TreeNode VT.Tree
  amismatch x y = VT.TNBottom . VT.Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

  procOther :: (RM.ReduceMonad s r m) => m ()
  procOther = do
    RuntimeParams{rpCreateCnstr = cc} <- asks (cfRuntimeParams . getConfig)
    logDebugStr $ printf "unifyLeftAtom: cc: %s, procOther: %s, %s" (show cc) (show ut1) (show ut2)
    if cc
      then do
        c <- putCnstr v1 >> RM.getRMTree
        logDebugStr $ printf "unifyLeftAtom: constraint created, %s" (show c)
      else unifyLeftOther ut2 ut1

  putCnstr :: (RM.ReduceMonad s r m) => VT.AtomV -> m ()
  putCnstr a1 = do
    unifyOp <- RM.getRMParent
    logDebugStr $ printf "unifyLeftAtom: creating constraint, t: %s" (show unifyOp)
    -- TODO: this is hack now. The unifyOp has a mutStub, which makes the buildASTExpr unhappy.
    let emptyUnifyOp = case VT.getMutableFromTree unifyOp of
          Just mut -> VT.mkMutableTree $ VT.setMutVal Nothing mut
          _ -> unifyOp
    e <- maybe (buildASTExpr False emptyUnifyOp) return (VT.treeExpr unifyOp)
    logDebugStr $ printf "unifyLeftAtom: creating constraint, e: %s, t: %s" (show e) (show unifyOp)
    RM.putRMTree $ VT.mkCnstrTree a1 e

unifyLeftBound :: (RM.ReduceMonad s r m) => (VT.Bounds, UTree) -> UTree -> m ()
unifyLeftBound (b1, ut1@(UTree{utVal = t1, utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = case VT.treeNode t2 of
  VT.TNAtom ta2 -> do
    logDebugStr $ printf "unifyAtomBounds: %s, %s" (show t1) (show t2)
    RM.putRMTree $ unifyAtomBounds (d2, VT.amvAtom ta2) (d1, VT.bdsList b1)
  VT.TNBounds b2 -> do
    logDebugStr $ printf "unifyBoundList: %s, %s" (show t1) (show t2)
    let res = unifyBoundList (d1, VT.bdsList b1) (d2, VT.bdsList b2)
    case res of
      Left err -> RM.putRMTree (VT.mkBottomTree err)
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
            Just a -> RM.putRMTree (VT.mkAtomTree a)
            Nothing -> RM.putRMTree (VT.mkBoundsTree (fst r))
  -- If the left bounds are embedded in the right struct and there is no fields and no pending dynamic fields, we can
  -- immediately put the bounds into the tree without worrying any future new fields. This is what CUE currently
  -- does.
  VT.TNStruct s2 | utEmbedded ut1 && VT.hasEmptyFields s2 -> RM.putRMTree t1
  _ -> unifyLeftOther ut2 ut1

unifyAtomBounds :: (Path.BinOpDirect, VT.Atom) -> (Path.BinOpDirect, [VT.Bound]) -> VT.Tree
unifyAtomBounds (d1, a1) (d2, bs) =
  -- try to find the atom in the bounds list.
  foldl1 findAtom (map withBound bs)
 where
  ta1 = VT.mkAtomTree a1

  findAtom acc x = if acc == ta1 || x == ta1 then acc else x

  withBound :: VT.Bound -> VT.Tree
  withBound b =
    let
      r = unifyBounds (d1, VT.BdIsAtom a1) (d2, b)
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

unifyBoundList :: (Path.BinOpDirect, [VT.Bound]) -> (Path.BinOpDirect, [VT.Bound]) -> Either String [VT.Bound]
unifyBoundList (d1, bs1) (d2, bs2) = case (bs1, bs2) of
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
    let f x y = unifyBounds (ld1, x) (ld2, y)
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
          then unifyBounds (Path.L, acc !! 0) (Path.R, y)
          else Left "bounds mismatch"
     in
      foldM f [x] rs

unifyBounds :: (Path.BinOpDirect, VT.Bound) -> (Path.BinOpDirect, VT.Bound) -> Either String [VT.Bound]
unifyBounds db1@(d1, b1) db2@(_, b2) = case b1 of
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
    _ -> unifyBounds db2 db1
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
    _ -> unifyBounds db2 db1
  VT.BdType t1 -> case b2 of
    VT.BdType t2 -> if t1 == t2 then return [b1] else Left conflict
    VT.BdIsAtom a2 -> uTypeAtom t1 a2
    _ -> unifyBounds db2 db1
  VT.BdIsAtom a1 -> case b2 of
    VT.BdIsAtom a2 -> if a1 == a2 then return [b1] else Left conflict
    _ -> unifyBounds db2 db1
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

-- | unifyLeftOther is the sink of the unification process.
unifyLeftOther :: (RM.ReduceMonad s r m) => UTree -> UTree -> m ()
unifyLeftOther ut1@(UTree{utVal = t1, utDir = d1}) ut2@(UTree{utVal = t2}) =
  case VT.treeNode t1 of
    (VT.TNMutable _) -> do
      RM.withAddrAndFocus $ \addr _ ->
        logDebugStr $ printf "unifyLeftOther starts, addr: %s, %s, %s" (show addr) (show ut1) (show ut2)
      -- If the left value is mutable, we should shallow reduce the left value first.
      r1 <- reduceUnifyArg (Path.toBinOpTASeg d1) t1
      case VT.treeNode r1 of
        VT.TNMutable _ -> return () -- No concrete value exists.
        _ -> unifyUTrees (ut1{utVal = r1}) ut2

    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    (VT.TNAtomCnstr c1) -> do
      r <- unifyUTrees (ut1{utVal = VT.mkNewTree (VT.TNAtom $ VT.cnsAtom c1)}) ut2
      na <- RM.getRMTree
      RM.putRMTree $ case VT.treeNode na of
        VT.TNBottom _ -> na
        _ -> t1
      return r
    -- According to the spec,
    -- A field value of the form r & v, where r evaluates to a reference cycle and v is a concrete value, evaluates to v.
    -- Unification is idempotent and unifying a value with itself ad infinitum, which is what the cycle represents,
    -- results in this value. Implementations should detect cycles of this kind, ignore r, and take v as the result of
    -- unification.
    -- We can just return the second value.
    (VT.TNRefCycle _) -> RM.putRMTree t2
    -- TODO: comment
    VT.TNStructuralCycle (VT.StructuralCycle infAddr) -> do
      curPath <- RM.getRMAbsAddr
      logDebugStr $
        printf
          "unifyLeftOther: unifying with structural cycle, inf path: %s, current path: %s"
          (show infAddr)
          (show curPath)
      if Path.isPrefix infAddr curPath
        then RM.putRMTree $ VT.mkBottomTree "structural cycle"
        else do
          raw <-
            maybe (throwErrSt "original expression is not found") return (VT.treeExpr t1)
              >>= RefSys.evalExprRM
          -- TODO: why?
          r1 <- reduceUnifyArg (Path.toBinOpTASeg d1) raw
          logDebugStr $
            printf
              "unifyLeftOther: found structural cycle, trying original deref'd %s with %s"
              (show r1)
              (show t2)
          unifyUTrees ut1{utVal = r1} ut2
    _ -> putNotUnifiable
 where
  putNotUnifiable :: (RM.ReduceMonad s r m) => m ()
  putNotUnifiable = mkNodeWithDir ut1 ut2 f
   where
    f :: (RM.ReduceMonad s r m) => VT.Tree -> VT.Tree -> m ()
    f x y = RM.putRMTree $ VT.mkBottomTree $ printf "values not unifiable: L:\n%s, R:\n%s" (show x) (show y)

unifyLeftStruct :: (RM.ReduceMonad s r m) => (VT.Struct VT.Tree, UTree) -> UTree -> m ()
unifyLeftStruct (s1, ut1@(UTree{utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = case VT.treeNode t2 of
  -- If either of the structs is embedded, closed struct restrictions are ignored.
  VT.TNStruct s2 -> unifyStructs (d1, utEmbedded ut1, s1) (d2, utEmbedded ut2, s2)
  _ -> unifyLeftOther ut2 ut1

{- | unify two structs.

The s1 is made the left struct, and s2 is made the right struct.

For closedness, unification only generates a closed struct but not a recursively closed struct since to close a struct
recursively, the only way is to reference the struct via a #ident.
-}
unifyStructs ::
  (RM.ReduceMonad s r m) =>
  (Path.BinOpDirect, Bool, VT.Struct VT.Tree) ->
  (Path.BinOpDirect, Bool, VT.Struct VT.Tree) ->
  m ()
unifyStructs (Path.L, isEmbed1, s1) (_, isEmbed2, s2) = do
  checkRes <- do
    rE1 <- _preprocessScopeVars s1
    rE2 <- _preprocessScopeVars s2
    return $ do
      r1 <- rE1
      r2 <- rE2
      return (r1, r2)
  case checkRes of
    Left err -> RM.putRMTree err
    Right (r1, r2) -> unifyStructsInner (isEmbed1, r1) (isEmbed2, r2)
unifyStructs dt1@(Path.R, _, _) dt2 = unifyStructs dt2 dt1

unifyStructsInner ::
  (RM.ReduceMonad s r m) =>
  (Bool, VT.Struct VT.Tree) ->
  (Bool, VT.Struct VT.Tree) ->
  m ()
unifyStructsInner (isEmbed1, s1) (isEmbed2, s2) = do
  sid <- RM.allocRMObjID
  let merged = nodesToStruct sid (unionFields s1 s2) s1 s2
  RM.withAddrAndFocus $ \addr _ ->
    logDebugStr $ printf "unifyStructs: %s gets updated to tree:\n%s" (show addr) (show merged)
  -- in reduce, the new combined fields will be checked by the combined patterns.
  RM.putRMTree merged

  let isEitherEmbeded = isEmbed1 || isEmbed2
  checkLabelsPerm
    (Set.fromList $ VT.stcOrdLabels s1)
    (VT.stcCnstrs s1)
    (VT.stcClosed s1)
    isEitherEmbeded
    (VT.stcOrdLabels s2)
  checkLabelsPerm
    (Set.fromList $ VT.stcOrdLabels s2)
    (VT.stcCnstrs s2)
    (VT.stcClosed s2)
    isEitherEmbeded
    (VT.stcOrdLabels s1)
 where
  -- merge two fields by creating a unify node with merged attributes.
  mkUnifiedField :: VT.Field VT.Tree -> VT.Field VT.Tree -> VT.Field VT.Tree
  mkUnifiedField sf1 sf2 =
    let
      -- No original node exists yet
      f = VT.mkBinaryOp AST.Unify unify (VT.ssfValue sf1) (VT.ssfValue sf2)
     in
      VT.Field
        { VT.ssfValue = VT.mkMutableTree f
        , VT.ssfAttr = VT.mergeAttrs (VT.ssfAttr sf1) (VT.ssfAttr sf2)
        , VT.ssfCnstrs = VT.ssfCnstrs sf1 ++ VT.ssfCnstrs sf2
        , VT.ssfPends = VT.ssfPends sf1 ++ VT.ssfPends sf2
        , VT.ssfNoStatic = VT.ssfNoStatic sf1 && VT.ssfNoStatic sf2
        }

  -- merge two fields.
  unionFields :: VT.Struct VT.Tree -> VT.Struct VT.Tree -> [(String, VT.Field VT.Tree)]
  unionFields st1 st2 =
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
                  (label, mkUnifiedField sf1 sf2) : acc
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

  nodesToStruct ::
    Int -> [(String, VT.Field VT.Tree)] -> VT.Struct VT.Tree -> VT.Struct VT.Tree -> VT.Tree
  nodesToStruct sid nodes st1 st2 =
    VT.mkStructTree $
      VT.emptyStruct
        { VT.stcID = sid
        , VT.stcOrdLabels = map fst nodes
        , VT.stcFields = Map.fromList nodes
        , VT.stcLets = VT.stcLets st1 `Map.union` VT.stcLets st2
        , VT.stcPendSubs = combinedPendSubs
        , VT.stcCnstrs = combinedPatterns
        , VT.stcClosed = VT.stcClosed st1 || VT.stcClosed st2
        , VT.stcPerms =
            -- st1 and st2 could be both closed.
            VT.stcPerms st1
              ++ VT.stcPerms st2
              -- st2 as an opposite struct of st1
              ++ ( if not isEmbed2 && VT.stcClosed st1
                    then [mkPermItem st1 st2]
                    else []
                 )
              -- st1 as an opposite struct of st2
              ++ ( if not isEmbed1 && VT.stcClosed st2
                    then [mkPermItem st2 st1]
                    else []
                 )
        }
   where
    combinedPendSubs = IntMap.union (VT.stcPendSubs st1) (VT.stcPendSubs st2)
    -- The combined patterns are the patterns of the first struct and the patterns of the second struct.
    combinedPatterns = IntMap.union (VT.stcCnstrs st1) (VT.stcCnstrs st2)

    mkPermItem :: VT.Struct VT.Tree -> VT.Struct VT.Tree -> VT.PermItem
    mkPermItem struct opStruct =
      VT.PermItem
        { VT.piCnstrs = Set.fromList $ IntMap.keys $ VT.stcCnstrs struct
        , -- TODO: exclude let bindings
          VT.piLabels = Set.fromList $ VT.stcOrdLabels struct
        , VT.piDyns = Set.fromList $ IntMap.keys $ VT.stcPendSubs struct
        , -- TODO: exclude let bindings
          VT.piOpLabels = Set.fromList $ VT.stcOrdLabels opStruct
        , VT.piOpDyns = Set.fromList $ IntMap.keys $ VT.stcPendSubs opStruct
        }

-- | Preprocess the scope variables.
_preprocessScopeVars :: (RM.ReduceMonad s r m) => VT.Struct VT.Tree -> m (Either VT.Tree (VT.Struct VT.Tree))
_preprocessScopeVars _struct = RM.withAddrAndFocus $ \addr _ ->
  debugSpan (printf "_preprocessScopeVars, add: %s" (show addr)) $ do
    tc <- RM.getRMCursor
    let
      ptc = fromJust $ Cursor.parentTC tc
      scopeAddr = Cursor.tcTreeAddr ptc
    preprocess scopeAddr (VT.mkStructTree _struct <$ ptc)
 where
  preprocess scopeAddr tc = do
    rM <- _findInvalidScopeVars tc
    logDebugStr $ printf "_preprocessScopeVars: rM: %s" (show rM)
    maybe
      ( do
          let sid = VT.stcID _struct
          -- Rewrite the scope variables.
          structT <- _rewriteScopeVars scopeAddr sid tc
          -- rewrite all var keys of the let bindings map with the sid.
          case VT.treeNode structT of
            VT.TNStruct struct -> do
              let
                m = Map.fromList $ map (\(k, v) -> (k ++ "_" ++ show sid, v)) (Map.toList $ VT.stcLets struct)
                newStruct = struct{VT.stcLets = m}
              logDebugStr $ printf "_preprocessScopeVars: newStruct: %s" (show $ VT.mkStructTree newStruct)
              return $ Right newStruct
            _ -> throwErrSt $ printf "tree must be struct, but got %s" (show structT)
      )
      (return . Left)
      rM

{- | Validate the vars in the scope because after merging two structs, the vars which were invalid could become valid.

We need to check all vars. If there is a ref in the deeper scope referencing a non-existed field in the current
scope, we should return an error because in the new scope the field may exist.
-}
_findInvalidScopeVars :: (Env r m) => Cursor.TreeCursor VT.Tree -> m (Maybe VT.Tree)
_findInvalidScopeVars _tc =
  snd
    <$> TCursorOps.traverseTC
      _allSubNodes
      find
      (_tc, Nothing)
 where
  find (tc, acc) = do
    case VT.treeNode (Cursor.vcFocus tc) of
      VT.TNMutable (VT.Ref (VT.Reference{VT.refArg = VT.RefPath var _})) -> do
        m <- RefSys.searchTCVar var tc
        logDebugStr $ printf "_findInvalidScopeVars: var: %s, m: %s" var (show m)
        maybe
          (return (tc, Just $ VT.mkBottomTree $ printf "identifier %s is not found" var))
          (const $ return (tc, acc))
          m
      _ -> return (tc, acc)

_rewriteScopeVars :: (Env r m) => Path.TreeAddr -> Int -> Cursor.TreeCursor VT.Tree -> m VT.Tree
_rewriteScopeVars scopeAddr sid _tc =
  Cursor.vcFocus
    <$> TCursorOps.traverseTCSimple
      _allSubNodes
      rewrite
      _tc
 where
  rewrite tc =
    let focus = Cursor.vcFocus tc
     in case VT.treeNode focus of
          VT.TNMutable (VT.Ref ref@(VT.Reference{VT.refArg = VT.RefPath var _})) -> do
            m <- RefSys.searchTCVar var tc
            logDebugStr $ printf "_rewriteScopeVars: var: %s, m: %s" var (show m)

            maybe
              (return focus)
              ( \(addr, isLB) -> do
                  logDebugStr $ printf "_rewriteScopeVars: rewrite %s, scopeAddr: %s, addr: %s" var (show scopeAddr) (show addr)
                  if isLB && (Just scopeAddr == Path.initTreeAddr addr)
                    then do
                      let newFocus = VT.setTN focus (VT.TNMutable $ VT.Ref $ _rewriteLBWithSID sid ref)
                      return newFocus
                    else return focus
              )
              m
          _ -> return focus

_rewriteLBWithSID :: Int -> VT.Reference VT.Tree -> VT.Reference VT.Tree
_rewriteLBWithSID sid ref@(VT.Reference{VT.refArg = VT.RefPath var sels}) =
  ref{VT.refArg = VT.RefPath (var ++ "_" ++ show sid) sels}
_rewriteLBWithSID _ r = r

_allSubNodes :: VT.Tree -> [(Path.TASeg, VT.Tree)]
_allSubNodes x = VT.subNodes x ++ rawNodes x
 where
  rawNodes :: VT.Tree -> [(Path.TASeg, VT.Tree)]
  rawNodes t = case VT.treeNode t of
    VT.TNStruct struct ->
      [(Path.StructTASeg $ Path.PatternTASeg i 1, VT.scsValue c) | (i, c) <- IntMap.toList $ VT.stcCnstrs struct]
        ++ [(Path.StructTASeg $ Path.PendingTASeg i 1, VT.dsfValue dsf) | (i, dsf) <- IntMap.toList $ VT.stcPendSubs struct]
        ++ [(Path.StructTASeg $ Path.LetTASeg s, VT.lbValue lb) | (s, lb) <- Map.toList $ VT.stcLets struct]
    _ -> []

mkNodeWithDir ::
  (RM.ReduceMonad s r m) => UTree -> UTree -> (VT.Tree -> VT.Tree -> m ()) -> m ()
mkNodeWithDir (UTree{utVal = t1, utDir = d1}) (UTree{utVal = t2}) f = case d1 of
  Path.L -> f t1 t2
  Path.R -> f t2 t1

unifyLeftDisj :: (RM.ReduceMonad s r m) => (VT.Disj VT.Tree, UTree) -> UTree -> m ()
unifyLeftDisj
  (dj1, ut1@(UTree{utDir = d1, utEmbedded = isEmbedded1}))
  ut2@( UTree
          { utVal = t2
          , utDir = d2
          , utEmbedded = isEmbedded2
          }
        ) = do
    RM.withAddrAndFocus $ \addr _ ->
      logDebugStr $ printf "unifyLeftDisj: addr: %s, dj: %s, right: %s" (show addr) (show ut1) (show ut2)
    case VT.treeNode t2 of
      VT.TNMutable _ -> unifyLeftOther ut2 ut1
      VT.TNAtomCnstr _ -> unifyLeftOther ut2 ut1
      VT.TNRefCycle _ -> unifyLeftOther ut2 ut1
      -- If the left disj is embedded in the right struct and there is no fields and no pending dynamic fields, we can
      -- immediately put the disj into the tree without worrying any future new fields. This is what CUE currently
      -- does.
      VT.TNStruct s2
        | utEmbedded ut1 && VT.hasEmptyFields s2 -> RM.putRMTree (utVal ut1)
      VT.TNDisj dj2 -> case (dj1, dj2) of
        -- this is U0 rule, <v1> & <v2> => <v1&v2>
        (VT.Disj{VT.dsjDefault = Nothing, VT.dsjDisjuncts = ds1}, VT.Disj{VT.dsjDefault = Nothing, VT.dsjDisjuncts = ds2}) -> do
          logDebugStr $ printf "unifyLeftDisj: U0, ds1: %s, ds2: %s" (show ds1) (show ds2)
          ds <- mapM (`oneToMany` (d2, isEmbedded2, ds2)) (map (\x -> (d1, isEmbedded1, x)) ds1)
          treeFromNodes Nothing ds >>= RM.putRMTree
        -- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
        (VT.Disj{VT.dsjDefault = Just df1, VT.dsjDisjuncts = ds1}, VT.Disj{VT.dsjDefault = Nothing, VT.dsjDisjuncts = ds2}) -> do
          logDebugStr $ printf "unifyLeftDisj: U1, df1: %s, ds1: %s, df2: N, ds2: %s" (show df1) (show ds1) (show ds2)
          dfs <- oneToMany (d1, isEmbedded1, df1) (d2, isEmbedded2, ds2)
          df <- treeFromNodes Nothing [dfs]
          dss <- manyToMany (d1, isEmbedded1, ds1) (d2, isEmbedded2, ds2)
          treeFromNodes (Just df) dss >>= RM.putRMTree
        -- this is also the U1 rule.
        (VT.Disj{VT.dsjDefault = Nothing}, VT.Disj{}) -> unifyLeftDisj (dj2, ut2) ut1
        -- this is U2 rule, <v1,d1> & <v2,d2> => <v1&v2,d1&d2>
        (VT.Disj{VT.dsjDefault = Just df1, VT.dsjDisjuncts = ds1}, VT.Disj{VT.dsjDefault = Just df2, VT.dsjDisjuncts = ds2}) -> do
          RM.withAddrAndFocus $ \addr _ ->
            logDebugStr $
              printf
                "unifyLeftDisj: addr: %s, U2, d1:%s, df1: %s, ds1: %s, df2: %s, ds2: %s"
                (show addr)
                (show d1)
                (show df1)
                (show ds1)
                (show df2)
                (show ds2)
          df <- unifyUTreesInTemp (ut1{utVal = df1}) (ut2{utVal = df2})
          dss <- manyToMany (d1, isEmbedded1, ds1) (d2, isEmbedded2, ds2)
          RM.withAddrAndFocus $ \addr _ ->
            logDebugStr $ printf "unifyLeftDisj: addr: %s, U2, df: %s, dss: %s" (show addr) (show df) (show dss)
          treeFromNodes (Just df) dss >>= RM.putRMTree
      -- this is the case for a disjunction unified with a value.
      _ -> case dj1 of
        VT.Disj{VT.dsjDefault = Nothing, VT.dsjDisjuncts = ds1} -> do
          logDebugStr $
            printf "unifyLeftDisj: unify with %s, disj: (ds: %s)" (show t2) (show ds1)
          ds2 <- oneToMany (d2, isEmbedded2, t2) (d1, isEmbedded1, ds1)
          treeFromNodes Nothing [ds2] >>= RM.putRMTree
        VT.Disj{VT.dsjDefault = Just df1, VT.dsjDisjuncts = ds1} -> do
          logDebugStr $
            printf "unifyLeftDisj: U1, unify with %s, disj: (df: %s, ds: %s)" (show t2) (show df1) (show ds1)
          df2 <- unifyUTreesInTemp (ut1{utVal = df1}) ut2
          ds2 <- oneToMany (d2, isEmbedded2, t2) (d1, isEmbedded1, ds1)
          logDebugStr $ printf "unifyLeftDisj: U1, df2: %s, ds2: %s" (show df2) (show ds2)
          r <- treeFromNodes (Just df2) [ds2]
          logDebugStr $ printf "unifyLeftDisj: U1, result: %s" (show r)
          RM.putRMTree r
   where
    -- Note: isEmbedded is still required. Think about the following values,
    -- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
    -- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
    oneToMany ::
      (RM.ReduceMonad s r m) => (Path.BinOpDirect, Bool, VT.Tree) -> (Path.BinOpDirect, Bool, [VT.Tree]) -> m [VT.Tree]
    oneToMany (ld1, em1, node) (ld2, em2, ts) =
      let f x y = unifyUTreesInTemp (UTree x ld1 em1) (UTree y ld2 em2)
       in mapM (`f` node) ts

    manyToMany ::
      (RM.ReduceMonad s r m) =>
      (Path.BinOpDirect, Bool, [VT.Tree]) ->
      (Path.BinOpDirect, Bool, [VT.Tree]) ->
      m [[VT.Tree]]
    manyToMany (ld1, em1, ts1) (ld2, em2, ts2) =
      if ld1 == Path.R
        then mapM (\y -> oneToMany (ld2, em2, y) (ld1, em1, ts1)) ts2
        else mapM (\x -> oneToMany (ld1, em1, x) (ld2, em2, ts2)) ts1

unifyUTreesInTemp :: (RM.ReduceMonad s r m) => UTree -> UTree -> m VT.Tree
unifyUTreesInTemp ut1 ut2 = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  RM.inTempSubRM
    (VT.mkMutableTree $ mkUnifyUTreesNode ut1 ut2)
    $ reduce >> RM.getRMTree

treeFromNodes :: (MonadError String m) => Maybe VT.Tree -> [[VT.Tree]] -> m VT.Tree
treeFromNodes dfM ds = case (excludeBottomM dfM, concatDedupNonBottoms ds) of
  -- if there is no non-bottom disjuncts, we return the first bottom.
  (_, []) -> maybe (throwErrSt $ printf "no disjuncts") return (firstBottom ds)
  (Nothing, [_d]) -> return $ VT.mkNewTree (VT.treeNode _d)
  (Nothing, _ds) ->
    let
      node = VT.TNDisj $ VT.Disj{VT.dsjDefault = Nothing, VT.dsjDisjuncts = _ds}
     in
      return $ VT.mkNewTree node
  (_df, _ds) ->
    let
      node = VT.TNDisj $ VT.Disj{VT.dsjDefault = _df, VT.dsjDisjuncts = _ds}
     in
      return $ VT.mkNewTree node
 where
  -- concat and dedup the non-bottom disjuncts
  concatDedupNonBottoms :: [[VT.Tree]] -> [VT.Tree]
  concatDedupNonBottoms xs =
    dedup $ concatMap (filter (not . isTreeBottom)) xs

  firstBottom :: [[VT.Tree]] -> Maybe VT.Tree
  firstBottom xs = let ys = concatMap (filter isTreeBottom) xs in if null ys then Nothing else Just $ head ys

  excludeBottomM :: Maybe VT.Tree -> Maybe VT.Tree
  excludeBottomM = maybe Nothing (\x -> if isTreeBottom x then Nothing else Just x)

  dedup :: [VT.Tree] -> [VT.Tree]
  dedup = foldr (\y acc -> if y `elem` acc then acc else y : acc) []

{- | Check the labels' permission.

The focus of the tree must be a struct.
-}
checkLabelsPerm ::
  (RM.ReduceMonad s r m) =>
  Set.Set String ->
  IntMap.IntMap (VT.StructCnstr VT.Tree) ->
  Bool ->
  Bool ->
  [String] ->
  m ()
checkLabelsPerm baseLabels baseCnstrs isBaseClosed isEitherEmbedded =
  mapM_
    ( \opLabel ->
        checkPerm baseLabels baseCnstrs isBaseClosed isEitherEmbedded opLabel
          >>= maybe
            (return ())
            -- If the checkPerm returns a bottom, update the bottom to the struct.
            ( \btm -> do
                RM.mustStruct $ \struct -> do
                  field <-
                    maybe
                      (throwErrSt "struct-value is not found")
                      return
                      (VT.lookupStructField opLabel struct)
                  RM.modifyRMTN $ VT.TNStruct $ VT.updateStructField opLabel (btm <$ field) struct
            )
    )

checkPerm ::
  (RM.ReduceMonad s r m) =>
  Set.Set String ->
  IntMap.IntMap (VT.StructCnstr VT.Tree) ->
  Bool ->
  Bool ->
  String ->
  m (Maybe VT.Tree)
checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel = do
  r <- _checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel
  logDebugStr $
    printf
      "checkPerm: newLabel: %s, baseLabels: %s, baseAllCnstrs: %s, isBaseClosed: %s, isEitherEmbedded: %s, r: %s"
      (show newLabel)
      (show baseLabels)
      (show baseAllCnstrs)
      (show isBaseClosed)
      (show isEitherEmbedded)
      (show r)
  return r

_checkPerm ::
  (RM.ReduceMonad s r m) =>
  Set.Set String ->
  IntMap.IntMap (VT.StructCnstr VT.Tree) ->
  Bool ->
  Bool ->
  String ->
  m (Maybe VT.Tree)
_checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel
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
                  r <- patMatchLabel pat newLabel
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
patMatchLabel :: (RM.ReduceMonad s r m) => VT.Tree -> String -> m Bool
patMatchLabel pat name = case VT.treeNode pat of
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
      mkUnifyNode = VT.mkBinaryOp AST.Unify unify
      segOp = VT.mkMutableTree $ mkUnifyNode (VT.mkAtomTree $ VT.String name) v
    -- Since segOps a list of unify nodes that unify the string with the bounds, we can use RM.inDiscardSubRM to
    -- evaluate the unify nodes and get the strings.
    r <-
      -- We should not create constraints in this context because we should not delay the evaluation of the
      -- pattern.
      local
        ( \r ->
            let conf = getConfig r
             in setConfig r conf{cfRuntimeParams = (cfRuntimeParams conf){rpCreateCnstr = False}}
        )
        $ RM.inDiscardSubRM Path.TempTASeg segOp (reduce >> RM.getRMTree)
    -- Filter the strings from the results. Non-string results are ignored meaning the fields do not match the
    -- pattern.
    case VT.getAtomFromTree r of
      Just (VT.String _) -> return True
      _ -> return False
