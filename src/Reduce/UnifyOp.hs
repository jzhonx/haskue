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
import Control.Monad (foldM, forM, when)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (asks, local)
import qualified Cursor
import qualified Data.IntMap.Strict as IntMap
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, isNothing)
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified TCursorOps
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

{- | Reduce the tree that is a mutable to the form that can be used in the unify operation.

If the tree is a struct or a list, no sub nodes need to be reduced as these nodes will be merged and reduced in a new
scope.
-}
reduceMutTree :: (RM.ReduceMonad s r m) => m ()
reduceMutTree = RM.debugSpanRM "reduceMutTree" $ do
  -- save the original tree before effects are applied to the focus of the tree.
  orig <- RM.getRMTree
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNMutable _ ->
      local
        ( \r ->
            let fns = MutEnv.getFuncs r
             in MutEnv.setFuncs r fns{MutEnv.fnReduce = reduceMutTree}
        )
        Mutate.mutate
    VT.TNStub -> throwErrSt "stub node should not be reduced"
    _ -> return ()

  -- Overwrite the treenode of the raw with the reduced tree's VT.TreeNode to preserve tree attributes.
  RM.withTree $ \t -> RM.putRMTree $ VT.setTN orig (VT.treeNode t)

{- | Reduce the argument of the mutable.

If nothing concrete can be returned, then the original argument is returned.
-}
reduceUnifyMutTreeArg :: (RM.ReduceMonad s r m) => Path.TASeg -> VT.Tree -> m VT.Tree
reduceUnifyMutTreeArg seg sub = RM.debugSpanArgsRM "reduceUnifyMutTreeArg" (printf "seg: %s" (show seg)) $ do
  m <-
    Mutate.mutValToArgsRM
      seg
      sub
      ( do
          reduceMutTree
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
  , utEmbedID :: Maybe Int
  -- ^ Whether the tree is embedded in a struct.
  , utAddr :: Path.TreeAddr
  -- ^ This address will be used by preprocessor as a starting address to validate and rewrite identifiers.
  }

instance Show UTree where
  show (UTree t d e a) = printf "(%s,addr:%s,embed:%s,\n%s)" (show d) (show a) (show e) (show t)

unify :: (RM.ReduceMonad s r m) => VT.Tree -> VT.Tree -> m ()
unify t1 t2 = do
  addr <- RM.getRMAbsAddr
  let
    funcAddr = fromJust $ Path.initTreeAddr addr
    lAddr = Path.appendSeg Path.binOpLeftTASeg funcAddr
    rAddr = Path.appendSeg Path.binOpRightTASeg funcAddr
  unifyUTrees (UTree t1 Path.L Nothing lAddr) (UTree t2 Path.R Nothing rAddr)

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
unifyUTrees ut1 ut2 = RM.debugSpanRM
  "unifyUTrees"
  $ do
    mergeUTrees ut1 ut2

    MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
    -- reduce the merged tree
    RM.withTree $ \t -> case VT.treeNode t of
      -- If the unify result is incomplete, skip the reduction.
      VT.TNStub -> return ()
      _ -> reduce

mergeUTrees :: (RM.ReduceMonad s r m) => UTree -> UTree -> m ()
mergeUTrees ut1@(UTree{utVal = t1}) ut2@(UTree{utVal = t2}) = RM.debugSpanArgsRM
  "mergeUTrees"
  (printf ("unifying %s" ++ "\n" ++ "with %s") (show ut1) (show ut2))
  $ do
    -- Each case should handle embedded case when the left value is embedded.
    case (VT.treeNode t1, VT.treeNode t2) of
      -- VT.CnstredVal has the highest priority, because the real operand is the value of the VT.CnstredVal.
      (VT.TNCnstredVal c, _) -> mergeLeftCnstredVal (c, ut1) ut2
      (_, VT.TNCnstredVal c) -> mergeLeftCnstredVal (c, ut2) ut1
      (VT.TNBottom _, _) -> RM.putRMTree t1
      (_, VT.TNBottom _) -> RM.putRMTree t2
      (VT.TNTop, _) -> mergeLeftTop ut1 ut2
      (_, VT.TNTop) -> mergeLeftTop ut2 ut1
      (VT.TNAtom a1, _) -> mergeLeftAtom (a1, ut1) ut2
      -- Below is the earliest time to create a constraint
      (_, VT.TNAtom a2) -> mergeLeftAtom (a2, ut2) ut1
      (VT.TNDisj dj1, _) -> mergeLeftDisj (dj1, ut1) ut2
      (_, VT.TNDisj dj2) -> mergeLeftDisj (dj2, ut2) ut1
      (VT.TNStruct s1, _) -> mergeLeftStruct (s1, ut1) ut2
      (_, VT.TNStruct s2) -> mergeLeftStruct (s2, ut2) ut1
      (VT.TNBounds b1, _) -> mergeLeftBound (b1, ut1) ut2
      (_, VT.TNBounds b2) -> mergeLeftBound (b2, ut2) ut1
      _ -> mergeLeftOther ut1 ut2

    -- close the merged tree
    RM.withTree $ \t ->
      RM.putRMTree (t{VT.treeRecurClosed = VT.treeRecurClosed t1 || VT.treeRecurClosed t2})

-- | Unify the right embedded tree with the left tree.
mergeRightEmbedded :: (RM.ReduceMonad s r m) => VT.Tree -> (VT.Tree, Int) -> m ()
mergeRightEmbedded t1 (t2, eid2) = do
  addr <- RM.getRMAbsAddr
  let
    funcAddr = fromJust $ Path.initTreeAddr addr
    lAddr = Path.appendSeg Path.binOpLeftTASeg funcAddr
    rAddr = Path.appendSeg Path.binOpRightTASeg funcAddr
  mergeUTrees (UTree t1 Path.L Nothing lAddr) (UTree t2 Path.R (Just eid2) rAddr)

mergeLeftCnstredVal :: (RM.ReduceMonad s r m) => (VT.CnstredVal VT.Tree, UTree) -> UTree -> m ()
mergeLeftCnstredVal (c1, ut1) ut2@UTree{utVal = t2} = do
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

  mergeUTrees ut1{utVal = VT.cnsedVal c1} ut2
  -- Re-encapsulate the VT.CnstredVal.
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNCnstredVal c -> RM.modifyRMTN (VT.TNCnstredVal $ c{VT.cnsedOrigExpr = Just e})
    _ -> RM.modifyRMTN (VT.TNCnstredVal $ VT.CnstredVal t (Just e))

mergeLeftTop :: (RM.ReduceMonad s r m) => UTree -> UTree -> m ()
mergeLeftTop ut1 ut2 = do
  case VT.treeNode . utVal $ ut2 of
    -- If the left top is embedded in the right struct, we can immediately put the top into the tree without worrying
    -- any future existing/new fields. Because for example {_, a: 1} is equivalent to _ & {a: 1}. This follows the
    -- behavior of the spec:
    -- The result of { A } is A for any A (including definitions).
    -- Notice that this is different from the behavior of the latest CUE. The latest CUE would do the following:
    -- {_, _h: int} & {_h: "hidden"} -> _|_.
    VT.TNStruct _ | isJust (utEmbedID ut1) -> RM.putRMTree (utVal ut1)
    _ -> RM.putRMTree (utVal ut2)

mergeLeftAtom :: (RM.ReduceMonad s r m) => (VT.AtomV, UTree) -> UTree -> m ()
mergeLeftAtom (v1, ut1@(UTree{utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = do
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
      logDebugStr $ printf "mergeLeftAtom, %s with VT.Bounds: %s" (show v1) (show t2)
      RM.putRMTree $ mergeAtomBounds (d1, VT.amvAtom v1) (d2, VT.bdsList b)
    (_, VT.TNAtomCnstr c) ->
      if v1 == VT.cnsAtom c
        then putCnstr (VT.cnsAtom c)
        else RM.putRMTree . VT.mkBottomTree $ printf "values mismatch: %s != %s" (show v1) (show $ VT.cnsAtom c)
    (_, VT.TNDisj dj2) -> do
      logDebugStr $ printf "mergeLeftAtom: VT.TNDisj %s, %s" (show t2) (show v1)
      mergeLeftDisj (dj2, ut2) ut1
    (_, VT.TNMutable mut2)
      | (VT.SFunc m2) <- mut2 -> case VT.sfnType m2 of
          -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
          -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
          -- marked disjunction.
          VT.DisjMutable -> mergeLeftOther ut2 ut1
          _ -> procOther
      | otherwise -> procOther
    (_, VT.TNRefCycle _) -> procOther
    (_, VT.TNStruct s2) -> mergeLeftStruct (s2, ut2) ut1
    _ -> mergeLeftOther ut1 ut2
 where
  putTree :: (RM.ReduceMonad s r m) => VT.TreeNode VT.Tree -> m ()
  putTree n = RM.putRMTree $ VT.mkNewTree n

  amismatch :: (Show a) => a -> a -> VT.TreeNode VT.Tree
  amismatch x y = VT.TNBottom . VT.Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

  procOther :: (RM.ReduceMonad s r m) => m ()
  procOther = do
    RuntimeParams{rpCreateCnstr = cc} <- asks (cfRuntimeParams . getConfig)
    logDebugStr $ printf "mergeLeftAtom: cc: %s, procOther: %s, %s" (show cc) (show ut1) (show ut2)
    if cc
      then do
        c <- putCnstr v1 >> RM.getRMTree
        logDebugStr $ printf "mergeLeftAtom: constraint created, %s" (show c)
      else mergeLeftOther ut2 ut1

  putCnstr :: (RM.ReduceMonad s r m) => VT.AtomV -> m ()
  putCnstr a1 = do
    unifyOp <- RM.getRMParent
    logDebugStr $ printf "mergeLeftAtom: creating constraint, t: %s" (show unifyOp)
    -- TODO: this is hack now. The unifyOp has a mutStub, which makes the buildASTExpr unhappy.
    let emptyUnifyOp = case VT.getMutableFromTree unifyOp of
          Just mut -> VT.mkMutableTree $ VT.setMutVal Nothing mut
          _ -> unifyOp
    e <- maybe (buildASTExpr False emptyUnifyOp) return (VT.treeExpr unifyOp)
    logDebugStr $ printf "mergeLeftAtom: creating constraint, e: %s, t: %s" (show e) (show unifyOp)
    RM.putRMTree $ VT.mkCnstrTree a1 e

mergeLeftBound :: (RM.ReduceMonad s r m) => (VT.Bounds, UTree) -> UTree -> m ()
mergeLeftBound (b1, ut1@(UTree{utVal = t1, utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = case VT.treeNode t2 of
  VT.TNAtom ta2 -> do
    logDebugStr $ printf "mergeAtomBounds: %s, %s" (show t1) (show t2)
    RM.putRMTree $ mergeAtomBounds (d2, VT.amvAtom ta2) (d1, VT.bdsList b1)
  VT.TNBounds b2 -> do
    logDebugStr $ printf "mergeBoundList: %s, %s" (show t1) (show t2)
    let res = mergeBoundList (d1, VT.bdsList b1) (d2, VT.bdsList b2)
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
  VT.TNStruct s2 -> mergeLeftStruct (s2, ut2) ut1
  _ -> mergeLeftOther ut2 ut1

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
mergeLeftOther :: (RM.ReduceMonad s r m) => UTree -> UTree -> m ()
mergeLeftOther ut1@(UTree{utVal = t1, utDir = d1}) ut2@(UTree{utVal = t2}) =
  case VT.treeNode t1 of
    (VT.TNMutable _) -> do
      RM.withAddrAndFocus $ \addr _ ->
        logDebugStr $ printf "mergeLeftOther starts, addr: %s, %s, %s" (show addr) (show ut1) (show ut2)
      -- If the left value is mutable, we should shallow reduce the left value first.
      r1 <- reduceUnifyMutTreeArg (Path.toBinOpTASeg d1) t1
      case VT.treeNode r1 of
        VT.TNMutable _ -> return () -- No concrete value exists.
        _ -> mergeUTrees (ut1{utVal = r1}) ut2

    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    (VT.TNAtomCnstr c1) -> do
      mergeUTrees (ut1{utVal = VT.mkNewTree (VT.TNAtom $ VT.cnsAtom c1)}) ut2
      na <- RM.getRMTree
      RM.putRMTree $ case VT.treeNode na of
        VT.TNBottom _ -> na
        _ -> t1
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
          "mergeLeftOther: unifying with structural cycle, inf path: %s, current path: %s"
          (show infAddr)
          (show curPath)
      if Path.isPrefix infAddr curPath
        then RM.putRMTree $ VT.mkBottomTree "structural cycle"
        else do
          MutEnv.Functions{MutEnv.fnEvalExpr = evalExpr} <- asks MutEnv.getFuncs
          raw <-
            maybe (throwErrSt "original expression is not found") return (VT.treeExpr t1)
              >>= evalExpr
          -- TODO: why?
          r1 <- reduceUnifyMutTreeArg (Path.toBinOpTASeg d1) raw
          logDebugStr $
            printf
              "mergeLeftOther: found structural cycle, trying original deref'd %s with %s"
              (show r1)
              (show t2)
          mergeUTrees ut1{utVal = r1} ut2
    _ -> putNotUnifiable
 where
  putNotUnifiable :: (RM.ReduceMonad s r m) => m ()
  putNotUnifiable = mkNodeWithDir ut1 ut2 f
   where
    f :: (RM.ReduceMonad s r m) => VT.Tree -> VT.Tree -> m ()
    f x y = do
      tx <- VT.showValueType x
      ty <- VT.showValueType y
      RM.putRMTree $ VT.mkBottomTree $ printf "%s can not be unified with %s" tx ty

mergeLeftStruct :: (RM.ReduceMonad s r m) => (VT.Struct VT.Tree, UTree) -> UTree -> m ()
mergeLeftStruct (s1, ut1) ut2@(UTree{utVal = t2}) =
  if
    -- When the left struct is an empty struct with embedded fields, we can get the reduced left struct and unify the
    -- reduced result (which should be the embeded value) with right value.
    | VT.hasEmptyFields s1 && not (null $ VT.stcEmbeds s1) ->
        do
          r1 <- reduceUnifyMutTreeArg (Path.toBinOpTASeg (utDir ut1)) t2
          case VT.treeNode r1 of
            VT.TNMutable _ -> return () -- No concrete value exists.
            _ -> mergeUTrees (ut1{utVal = r1}) ut2
    | VT.hasEmptyFields s1 && isJust (utEmbedID ut2) -> case VT.treeNode t2 of
        -- When the left is an empty struct and the right value is an embedded value of type non-struct, meaning we are
        -- using the embedded value to replace the struct.
        VT.TNStruct s2 -> mergeStructs (s1, ut1) (s2, ut2)
        _ -> RM.putRMTree t2
    | otherwise -> case VT.treeNode t2 of
        VT.TNStruct s2 -> mergeStructs (s1, ut1) (s2, ut2)
        _ -> mergeLeftOther ut2 ut1

{- | unify two structs.

The s1 is made the left struct, and s2 is made the right struct.

For closedness, unification only generates a closed struct but not a recursively closed struct since to close a struct
recursively, the only way is to reference the struct via a #ident.
-}
mergeStructs ::
  (RM.ReduceMonad s r m) =>
  (VT.Struct VT.Tree, UTree) ->
  (VT.Struct VT.Tree, UTree) ->
  m ()
mergeStructs (s1, ut1@UTree{utDir = Path.L}) (s2, ut2) = do
  checkRes <- do
    rE1 <- _preprocessBlock (utAddr ut1) s1
    rE2 <- _preprocessBlock (utAddr ut2) s2
    return $ do
      r1 <- rE1
      r2 <- rE2
      return (r1, r2)
  case checkRes of
    Left err -> RM.putRMTree err
    Right (r1, r2) -> mergeStructsInner (utEmbedID ut1, r1) (utEmbedID ut2, r2)
mergeStructs dt1@(_, UTree{utDir = Path.R}) dt2 = mergeStructs dt2 dt1

mergeStructsInner ::
  (RM.ReduceMonad s r m) =>
  (Maybe Int, VT.Struct VT.Tree) ->
  (Maybe Int, VT.Struct VT.Tree) ->
  m ()
mergeStructsInner (eidM1, s1) (eidM2, s2) = do
  when (isJust eidM1 && isJust eidM2) $ throwErrSt "both structs are embedded, not allowed"

  sid <- RM.allocRMObjID
  let merged = fieldsToStruct sid (_unionFields (s1, eidM1) (s2, eidM2)) (s1, eidM1) (s2, eidM2)
  RM.withAddrAndFocus $ \addr _ ->
    logDebugStr $ printf "mergeStructs: %s gets updated to tree:\n%s" (show addr) (show merged)
  -- in reduce, the new combined fields will be checked by the combined patterns.
  RM.putRMTree merged

  let isEitherEmbeded = isJust eidM1 || isJust eidM2
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
          -- st1 and st2 could be both closed.
          VT.stcPerms st1
            ++ VT.stcPerms st2
            -- st2 as an opposite struct of st1
            ++ ( if isNothing eidM2 && VT.stcClosed st1
                  then [mkPermItem st1 st2]
                  else []
               )
            -- st1 as an opposite struct of st2
            ++ ( if isNothing eidM1 && VT.stcClosed st2
                  then [mkPermItem st2 st1]
                  else []
               )
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
    unifyValOp = VT.mkBinaryOp AST.Unify unify (VT.ssfValue sf1) (VT.ssfValue sf2)
    unifiedBaseRaw = case catMaybes [VT.ssfBaseRaw sf1, VT.ssfBaseRaw sf2] of
      [br1, br2] -> Just $ VT.mkMutableTree $ VT.mkBinaryOp AST.Unify unify br1 br2
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

According to spec, A block is a possibly empty sequence of declarations.

The scope of a declared identifier is the extent of source text in which the identifier denotes the specified field,
alias, or package.
-}
_preprocessBlock ::
  (RM.ReduceMonad s r m) =>
  Path.TreeAddr ->
  VT.Struct VT.Tree ->
  m (Either VT.Tree (VT.Struct VT.Tree))
_preprocessBlock blockAddr block = RM.debugSpanArgsRM "_preprocessBlock" (printf "blockAddr: %s" (show blockAddr)) $ do
  -- Use the block address to get the tree cursor and replace the tree focus with the block.
  -- This simplifies processing for cases that the focus is reference.
  ptc <- RefSys.inAbsAddrRMMust blockAddr RM.getRMCursor
  preprocess (VT.mkStructTree block <$ ptc)
 where
  preprocess tc = do
    rM <- _validateRefIdents tc
    logDebugStr $ printf "_preprocessBlock: rM: %s" (show rM)
    maybe
      ( do
          let sid = VT.stcID block
          structT <- _appendSIDToLetRef blockAddr sid tc
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
_validateRefIdents :: (Env r s m) => Cursor.TreeCursor VT.Tree -> m (Maybe VT.Tree)
_validateRefIdents _tc =
  snd <$> TCursorOps.traverseTC _extAllSubNodes find (_tc, Nothing)
 where
  find (tc, acc) = do
    case VT.treeNode (Cursor.vcFocus tc) of
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
_appendSIDToLetRef :: (Env r s m) => Path.TreeAddr -> Int -> Cursor.TreeCursor VT.Tree -> m VT.Tree
_appendSIDToLetRef blockAddr sid _tc =
  Cursor.vcFocus <$> TCursorOps.traverseTCSimple _extAllSubNodes rewrite _tc
 where
  rewrite tc =
    let focus = Cursor.vcFocus tc
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
              m
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

mkNodeWithDir ::
  (RM.ReduceMonad s r m) => UTree -> UTree -> (VT.Tree -> VT.Tree -> m ()) -> m ()
mkNodeWithDir (UTree{utVal = t1, utDir = d1}) (UTree{utVal = t2}) f = case d1 of
  Path.L -> f t1 t2
  Path.R -> f t2 t1

mergeLeftDisj :: (RM.ReduceMonad s r m) => (VT.Disj VT.Tree, UTree) -> UTree -> m ()
mergeLeftDisj (dj1, ut1@(UTree{utDir = d1})) ut2@(UTree{utVal = t2}) = do
  RM.withAddrAndFocus $ \addr _ ->
    logDebugStr $ printf "mergeLeftDisj: addr: %s, dj: %s, right: %s" (show addr) (show ut1) (show ut2)
  case VT.treeNode t2 of
    VT.TNMutable _ -> mergeLeftOther ut2 ut1
    VT.TNAtomCnstr _ -> mergeLeftOther ut2 ut1
    VT.TNRefCycle _ -> mergeLeftOther ut2 ut1
    -- VT.TNStruct s2 -> mergeLeftStruct (s2, ut2) ut1
    VT.TNDisj dj2 -> case (dj1, dj2) of
      -- this is U0 rule, <v1> & <v2> => <v1&v2>
      (VT.Disj{VT.dsjDefault = Nothing, VT.dsjDisjuncts = ds1}, VT.Disj{VT.dsjDefault = Nothing, VT.dsjDisjuncts = ds2}) -> do
        logDebugStr $ printf "mergeLeftDisj: U0, ds1: %s, ds2: %s" (show ds1) (show ds2)
        ds <- mapM (`oneToManyDisj` (utsFromDisjs ds2 ut2)) (utsFromDisjs ds1 ut1)
        treeFromNodes Nothing ds >>= RM.putRMTree
      -- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
      (VT.Disj{VT.dsjDefault = Just df1, VT.dsjDisjuncts = ds1}, VT.Disj{VT.dsjDefault = Nothing, VT.dsjDisjuncts = ds2}) -> do
        logDebugStr $ printf "mergeLeftDisj: U1, df1: %s, ds1: %s, df2: N, ds2: %s" (show df1) (show ds1) (show ds2)
        dfs <- oneToManyDisj (utFromDefault df1 ut1) (utsFromDisjs ds2 ut2)
        df <- treeFromNodes Nothing [dfs]
        dss <- manyToManyDisj (utsFromDisjs ds1 ut1) (utsFromDisjs ds2 ut2)
        treeFromNodes (Just df) dss >>= RM.putRMTree
      -- this is also the U1 rule.
      (VT.Disj{VT.dsjDefault = Nothing}, VT.Disj{}) -> mergeLeftDisj (dj2, ut2) ut1
      -- this is U2 rule, <v1,d1> & <v2,d2> => <v1&v2,d1&d2>
      (VT.Disj{VT.dsjDefault = Just df1, VT.dsjDisjuncts = ds1}, VT.Disj{VT.dsjDefault = Just df2, VT.dsjDisjuncts = ds2}) -> do
        RM.withAddrAndFocus $ \addr _ ->
          logDebugStr $
            printf
              "mergeLeftDisj: addr: %s, U2, d1:%s, df1: %s, ds1: %s, df2: %s, ds2: %s"
              (show addr)
              (show d1)
              (show df1)
              (show ds1)
              (show df2)
              (show ds2)
        df <- unifyUTreesInTemp (ut1{utVal = df1}) (ut2{utVal = df2})
        dss <- manyToManyDisj (utsFromDisjs ds1 ut1) (utsFromDisjs ds2 ut2)
        RM.withAddrAndFocus $ \addr _ ->
          logDebugStr $ printf "mergeLeftDisj: addr: %s, U2, df: %s, dss: %s" (show addr) (show df) (show dss)
        treeFromNodes (Just df) dss >>= RM.putRMTree
    -- this is the case for a disjunction unified with a value.
    _ -> case dj1 of
      VT.Disj{VT.dsjDefault = Nothing, VT.dsjDisjuncts = ds1} -> do
        logDebugStr $
          printf "mergeLeftDisj: unify with %s, disj: (ds: %s)" (show t2) (show ds1)
        ds2 <- oneToManyDisj ut2 (utsFromDisjs ds1 ut1)
        treeFromNodes Nothing [ds2] >>= RM.putRMTree
      VT.Disj{VT.dsjDefault = Just df1, VT.dsjDisjuncts = ds1} -> do
        logDebugStr $
          printf "mergeLeftDisj: U1, unify with %s, disj: (df: %s, ds: %s)" (show t2) (show df1) (show ds1)
        df2 <- unifyUTreesInTemp (ut1{utVal = df1}) ut2
        ds2 <- oneToManyDisj ut2 (utsFromDisjs ds1 ut1)
        logDebugStr $ printf "mergeLeftDisj: U1, df2: %s, ds2: %s" (show df2) (show ds2)
        r <- treeFromNodes (Just df2) [ds2]
        logDebugStr $ printf "mergeLeftDisj: U1, result: %s" (show r)
        RM.putRMTree r
 where
  utFromDefault :: VT.Tree -> UTree -> UTree
  utFromDefault df ut@(UTree{utAddr = addr}) = ut{utVal = df, utAddr = Path.appendSeg Path.DisjDefaultTASeg addr}

  utsFromDisjs :: [VT.Tree] -> UTree -> [UTree]
  utsFromDisjs ds ut@(UTree{utAddr = addr}) =
    map (\(i, x) -> ut{utVal = x, utAddr = Path.appendSeg (Path.DisjDisjunctTASeg i) addr}) (zip [0 ..] ds)

-- Note: isEmbedded is still required. Think about the following values,
-- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
-- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
-- In current CUE's implementation, CUE puts the fields of the single value first.
oneToManyDisj ::
  (RM.ReduceMonad s r m) => UTree -> [UTree] -> m [VT.Tree]
oneToManyDisj ut1 = mapM (\ut2 -> unifyUTreesInTemp ut1{utDir = Path.L} ut2{utDir = Path.R})

manyToManyDisj :: (RM.ReduceMonad s r m) => [UTree] -> [UTree] -> m [[VT.Tree]]
manyToManyDisj uts1 = mapM (`oneToManyDisj` uts1)

unifyUTreesInTemp :: (RM.ReduceMonad s r m) => UTree -> UTree -> m VT.Tree
unifyUTreesInTemp ut1 ut2 = do
  -- TODO: just mergeUTrees?
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
                  RM.modifyRMTN $ VT.TNStruct $ VT.updateStructField opLabel (btm `VT.updateFieldValue` field) struct
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
  res <- _checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel
  RM.debugInstantRM "checkPerm" $
    printf
      "newLabel: %s, baseLabels: %s, baseAllCnstrs: %s, isBaseClosed: %s, isEitherEmbedded: %s, res: %s"
      (show newLabel)
      (show baseLabels)
      (show baseAllCnstrs)
      (show isBaseClosed)
      (show isEitherEmbedded)
      (show res)
  return res

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
