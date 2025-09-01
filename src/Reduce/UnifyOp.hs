{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.UnifyOp where

import qualified AST
import Common (
  EnvIO,
 )
import Control.Monad (foldM, forM, when)
import Cursor
import qualified Data.IntMap.Strict as IntMap
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isNothing)
import qualified Data.Set as Set
import qualified Data.Text as T
import Exception (throwErrSt)
import Path
import Reduce.RMonad (
  ResolveMonad,
  allocRMObjID,
  debugInstantRM,
  debugSpanMTreeArgsRM,
  debugSpanTreeArgsRM,
  debugSpanTreeRM,
 )
import Reduce.RefSys (searchTCIdent, selToIdent)
import Text.Printf (printf)
import Value

-- | UTree is a tree with a direction.
data UTree = UTree
  { utDir :: BinOpDirect
  , utTC :: TrCur
  -- ^ This tree cursor of the conjunct.
  }

instance Show UTree where
  show (UTree d tc) =
    show d
      <> ","
      <> show (tcAddr tc)
      <> ","
      <> show (tcFocus tc)

{- | Get the embedded object ID of the tree. The embedded object ID is the last embedded object ID in the tree address.

Because unification is a top down operation, no nested embedded object ID has been found yet. So we can just return the
last embedded object ID in the tree address.
-}
getEmbeddedOID :: UTree -> Maybe Int
getEmbeddedOID ut =
  let TreeAddr segs = tcAddr (utTC ut)
      getEID (BlockTASeg (EmbedTASeg i)) = Just i
      getEID _ = Nothing
   in -- segs are stored in reverse order so we use foldl to get the last embedded object ID.
      foldl
        ( \acc x ->
            case acc of
              Just _ -> acc
              Nothing -> getEID x
        )
        Nothing
        segs

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

showTCList :: [TrCur] -> String
showTCList [] = "[]"
showTCList (x : xs) =
  show x
    <> "\n"
    <> foldl
      ( \acc y -> acc <> show (tcFocus y) <> "\n"
      )
      ""
      xs

{- | Unify a list of trees that are ready after preprocessing.

It handles the following cases:
1. If all trees are structurally cyclic, return a bottom tree.
2. Reference cycle.

If RC can not be cancelled, then the result is Nothing.

The order of the unification is the same as the order of the trees.

The tree cursor is only used to know where the unification is happening.
-}
unifyNormalizedTCs :: (ResolveMonad s r m) => [TrCur] -> TrCur -> m (Maybe Tree)
unifyNormalizedTCs tcs unifyTC = debugSpanMTreeArgsRM "unifyNormalizedTCs" (showTCList tcs) unifyTC $ do
  when (length tcs < 2) $ throwErrSt "not enough arguments for unification"

  let isAllCyclic = all (treeIsSCyclic . tcFocus) tcs
  if isAllCyclic
    then return $ Just $ mkBottomTree "structural cycle"
    else do
      debugInstantRM "unifyNormalizedTCs" (printf "normalized: %s" (show tcs)) unifyTC
      let (regs, rcs) =
            foldr
              ( \tc (accRegs, accRCs) ->
                  let t = tcFocus tc
                   in case t of
                        IsRefCycle -> (accRegs, accRCs + 1)
                        IsUnifiedWithRC True -> (tc : accRegs, accRCs + 1)
                        _ -> (tc : accRegs, accRCs)
              )
              ([], 0 :: Int)
              tcs

      if
        | null regs, rcs == 0 -> throwErrSt "no trees to unify"
        | null regs, canCancelRC unifyTC -> return $ Just $ mkNewTree TNTop
        | null regs ->
            -- If there are no regular trees.
            return $ Just (mkNewTree TNRefCycle)
        | otherwise -> do
            r <- mergeTCs regs unifyTC
            -- If there is no reference cycle, or the reference cycle can be cancelled, return the result of merging
            -- regular conjuncts.
            if rcs == 0 || canCancelRC unifyTC
              then return $ Just r
              else return $ Just $ r{treeUnifiedWithRC = True}

{- | Check if the reference cycle can be cancelled.

A reference cycle can be cancelled if
* in the form of f: RC & v
-}
canCancelRC :: TrCur -> Bool
canCancelRC unifyTC = isAddrCanonical (tcAddr unifyTC)

{- | Unify two UTrees that are discovered in the merging process.

The new conjuncts are not necessarily ready.

The order of the operands is preserved.
-}
unifyForNewBinConjs :: (ResolveMonad s r m) => UTree -> UTree -> TrCur -> m (Maybe Tree)
unifyForNewBinConjs ut1@(UTree{utDir = L}) ut2 tc = unifyForNewConjs [ut1, ut2] tc
unifyForNewBinConjs ut1@(UTree{utDir = R}) ut2 tc = unifyForNewConjs [ut2, ut1] tc

unifyForNewConjs :: (ResolveMonad s r m) => [UTree] -> TrCur -> m (Maybe Tree)
unifyForNewConjs uts tc = do
  let xs =
        map
          ( \x ->
              let y = utTC x
               in case rtrNonMut (tcFocus y) of
                    Just v -> Just (v `setTCFocus` y)
                    Nothing -> Nothing
          )
          uts
  case sequence xs of
    Just ys -> unifyNormalizedTCs ys tc
    Nothing -> return Nothing

mergeTCs :: (ResolveMonad s r m) => [TrCur] -> TrCur -> m Tree
mergeTCs tcs unifyTC = debugSpanTreeArgsRM "mergeTCs" (showTCList tcs) unifyTC $ do
  when (null tcs) $ throwErrSt "not enough arguments"
  r <-
    foldM
      ( \acc tc -> do
          r <- mergeBinUTrees (acc{utDir = L}) (UTree{utDir = R, utTC = tc}) unifyTC
          return $ acc{utTC = r `setTCFocus` utTC acc}
      )
      (UTree{utDir = L, utTC = head tcs})
      (tail tcs)
  return $ tcFocus (utTC r)

{- | Merge Two UTrees that are not of type mutable.

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
mergeBinUTrees :: (ResolveMonad s r m) => UTree -> UTree -> TrCur -> m Tree
mergeBinUTrees ut1@(UTree{utTC = tc1}) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t1 = tcFocus tc1
      t2 = tcFocus tc2
  debugSpanTreeArgsRM
    "mergeBinUTrees"
    ( printf
        ("merging %s, %s" ++ "\n" ++ "with %s, %s")
        (show $ utDir ut1)
        (show t1)
        (show $ utDir ut2)
        (show t2)
    )
    unifyTC
    $ do
      -- Each case should handle embedded case when the left value is embedded.
      r <- case (treeNode t1, treeNode t2) of
        (TNBottom _, _) -> retTr t1
        (_, TNBottom _) -> retTr t2
        (TNTop, _) -> mergeLeftTop ut1 ut2
        (_, TNTop) -> mergeLeftTop ut2 ut1
        (TNAtom a1, _) -> mergeLeftAtom (a1, ut1) ut2 unifyTC
        (_, TNAtom a2) -> mergeLeftAtom (a2, ut2) ut1 unifyTC
        (TNDisj dj1, _) -> mergeLeftDisj (dj1, ut1) ut2 unifyTC
        (_, TNDisj dj2) -> mergeLeftDisj (dj2, ut2) ut1 unifyTC
        (TNBlock es1, _) -> mergeLeftBlock (es1, ut1) ut2 unifyTC
        (_, TNBlock es2) -> mergeLeftBlock (es2, ut2) ut1 unifyTC
        (TNBounds b1, _) -> mergeLeftBound (b1, ut1) ut2 unifyTC
        (_, TNBounds b2) -> mergeLeftBound (b2, ut2) ut1 unifyTC
        _ -> mergeLeftOther ut1 ut2 unifyTC

      -- close the merged tree
      retTr (r{treeRecurClosed = treeRecurClosed t1 || treeRecurClosed t2})

retTr :: (ResolveMonad s r m) => Tree -> m Tree
retTr = return

mergeLeftTop :: (ResolveMonad s r m) => UTree -> UTree -> m Tree
mergeLeftTop _ ut2 = do
  let t2 = tcFocus (utTC ut2)
  retTr t2

mergeLeftAtom :: (ResolveMonad s r m) => (Atom, UTree) -> UTree -> TrCur -> m Tree
mergeLeftAtom (v1, ut1@(UTree{utDir = d1})) ut2@(UTree{utTC = tc2, utDir = d2}) unifyTC =
  debugSpanTreeRM "mergeLeftAtom" unifyTC $ do
    let t2 = tcFocus tc2
    case (v1, treeNode t2) of
      (String x, TNAtom s)
        | String y <- s -> rtn $ if x == y then TNAtom v1 else amismatch x y
      (Int x, TNAtom s)
        | Int y <- s -> rtn $ if x == y then TNAtom v1 else amismatch x y
      (Float x, TNAtom s)
        | Float y <- s -> rtn $ if x == y then TNAtom v1 else amismatch x y
      (Bool x, TNAtom s)
        | Bool y <- s -> rtn $ if x == y then TNAtom v1 else amismatch x y
      (Null, TNAtom s) | Null <- s -> rtn $ TNAtom v1
      (_, TNBounds b) -> do
        return $ mergeAtomBounds (d1, v1) (d2, bdsList b)
      (_, TNAtomCnstr c) ->
        if v1 == cnsAtom c
          then retTr t2
          else retTr $ mkBottomTree $ printf "values mismatch: %s != %s" (show v1) (show $ cnsAtom c)
      (_, TNDisj dj2) -> do
        mergeLeftDisj (dj2, ut2) ut1 unifyTC
      (_, TNMutable mut2)
        -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
        -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
        -- marked disjunction.
        | (MutOp (DisjOp _)) <- mut2 -> mergeLeftOther ut2 ut1 unifyTC
        | otherwise -> mergeLeftOther ut2 ut1 unifyTC
      (_, TNBlock s2) -> mergeLeftBlock (s2, ut2) ut1 unifyTC
      _ -> mergeLeftOther ut1 ut2 unifyTC
 where
  rtn :: (ResolveMonad s r m) => TreeNode -> m Tree
  rtn = return . mkNewTree

  amismatch :: (Show a) => a -> a -> TreeNode
  amismatch x y = TNBottom . Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

mergeLeftBound :: (ResolveMonad s r m) => (Bounds, UTree) -> UTree -> TrCur -> m Tree
mergeLeftBound (b1, ut1@(UTree{utDir = d1})) ut2@(UTree{utTC = tc2, utDir = d2}) unifyTC = do
  let t2 = tcFocus tc2
  case treeNode t2 of
    TNAtom ta2 -> do
      retTr $ mergeAtomBounds (d2, ta2) (d1, bdsList b1)
    TNBounds b2 -> do
      let res = mergeBoundList (d1, bdsList b1) (d2, bdsList b2)
      case res of
        Left err -> retTr (mkBottomTree err)
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
              Just a -> retTr (mkAtomTree a)
              Nothing -> retTr (mkBoundsTreeFromList (fst r))
    TNBlock s2 -> mergeLeftBlock (s2, ut2) ut1 unifyTC
    _ -> mergeLeftOther ut2 ut1 unifyTC

mergeAtomBounds :: (BinOpDirect, Atom) -> (BinOpDirect, [Bound]) -> Tree
mergeAtomBounds (d1, a1) (d2, bs) =
  -- try to find the atom in the bounds list.
  foldl1 findAtom (map withBound bs)
 where
  ta1 = mkAtomTree a1

  findAtom acc x = if acc == ta1 || x == ta1 then acc else x

  withBound :: Bound -> Tree
  withBound b =
    let
      r = mergeBounds (d1, BdIsAtom a1) (d2, b)
     in
      case r of
        Left s -> mkBottomTree s
        Right v -> case v of
          [x] -> case x of
            BdIsAtom a -> mkAtomTree a
            _ -> mkBottomTree $ printf "unexpected bounds unification result: %s" (show x)
          _ -> mkBottomTree $ printf "unexpected bounds unification result: %s" (show v)

-- TODO: regex implementation
-- Second argument is the pattern.
reMatch :: T.Text -> T.Text -> Bool
reMatch = (==)

-- TODO: regex implementation
-- Second argument is the pattern.
reNotMatch :: T.Text -> T.Text -> Bool
reNotMatch = (/=)

mergeBoundList :: (BinOpDirect, [Bound]) -> (BinOpDirect, [Bound]) -> Either String [Bound]
mergeBoundList (d1, bs1) (d2, bs2) = case (bs1, bs2) of
  ([], _) -> return bs2
  (_, []) -> return bs1
  _ -> do
    bss <- manyToMany (d1, bs1) (d2, bs2)
    let bsMap = Map.fromListWith (++) (map (\b -> (bdRep b, [b])) (concat bss))
    norm <- forM bsMap narrowBounds
    let m = Map.toList norm
    return $ concat $ map snd m
 where
  oneToMany :: (BinOpDirect, Bound) -> (BinOpDirect, [Bound]) -> Either String [Bound]
  oneToMany (ld1, b) (ld2, ts) =
    let f x y = mergeBounds (ld1, x) (ld2, y)
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
          then mergeBounds (L, acc !! 0) (R, y)
          else Left "bounds mismatch"
     in
      foldM f [x] rs

mergeBounds :: (BinOpDirect, Bound) -> (BinOpDirect, Bound) -> Either String [Bound]
mergeBounds db1@(d1, b1) db2@(_, b2) = case b1 of
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
    _ -> mergeBounds db2 db1
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
    _ -> mergeBounds db2 db1
  BdType t1 -> case b2 of
    BdType t2 -> if t1 == t2 then return [b1] else Left conflict
    BdIsAtom a2 -> uTypeAtom t1 a2
    _ -> mergeBounds db2 db1
  BdIsAtom a1 -> case b2 of
    BdIsAtom a2 -> if a1 == a2 then return [b1] else Left conflict
    _ -> mergeBounds db2 db1
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

  ncncGroup :: [([BdNumCmpOp], [Number -> Number -> Bool])]
  ncncGroup =
    [ ([BdLT, BdLE], [(<=), (>)])
    , ([BdGT, BdGE], [(>=), (<)])
    ]

  uNumCmpNumCmp :: BdNumCmp -> BdNumCmp -> Either String [Bound]
  uNumCmpNumCmp (BdNumCmpCons o1 n1) (BdNumCmpCons o2 n2) =
    let
      c1g = if o1 `elem` fst (ncncGroup !! 0) then ncncGroup !! 0 else ncncGroup !! 1
      c1SameGCmp = snd c1g !! 0
      c1OppGCmp = snd c1g !! 1
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
          Int _ -> t1 `elem` [BdInt, BdNumber]
          Float _ -> t1 `elem` [BdFloat, BdNumber]
          String _ -> t1 == BdString
          _ -> False
     in if r then return [b2] else Left conflict

  conflict :: String
  conflict =
    let conv x = AST.exprToOneLinerStr $ buildBoundASTExpr x
     in printf "bounds %s and %s conflict" (conv b1) (conv b2)

  newOrdBounds :: [Bound]
  newOrdBounds = if d1 == L then [b1, b2] else [b2, b1]

-- | mergeLeftOther is the sink of the unification process.
mergeLeftOther :: (ResolveMonad s r m) => UTree -> UTree -> TrCur -> m Tree
mergeLeftOther ut1@(UTree{utTC = tc1}) ut2 unifyTC = do
  let t1 = tcFocus tc1
  case treeNode t1 of
    TNRefCycle{} -> throwErrSt "ref cycle should not be used in merge"
    (TNMutable (Mutable mop _)) -> throwErrSt $ printf "mutable op %s should not be used in merge" (show mop)
    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    (TNAtomCnstr c1) -> do
      na <- unifyForNewBinConjs (ut1{utTC = mkNewTree (TNAtom $ cnsAtom c1) `setTCFocus` tc1}) ut2 unifyTC
      -- Because the ut2 has been guaranteed to be a concrete tree cursor and the ut1 is an atom, so there must be a
      -- result.
      case treeNode (fromJust na) of
        TNBottom _ -> retTr (fromJust na)
        _ -> retTr t1
    _ -> returnNotUnifiable ut1 ut2

returnNotUnifiable :: (ResolveMonad s r m) => UTree -> UTree -> m Tree
returnNotUnifiable (UTree{utTC = tc1, utDir = d1}) (UTree{utTC = tc2}) = do
  let t1 = tcFocus tc1
      t2 = tcFocus tc2
  case d1 of
    L -> f t1 t2
    R -> f t2 t1
 where
  f x y = do
    tx <- showValueType x
    ty <- showValueType y
    retTr $ mkBottomTree $ printf "%s can not be unified with %s" tx ty

mergeLeftBlock :: (ResolveMonad s r m) => (Block, UTree) -> UTree -> TrCur -> m Tree
mergeLeftBlock (s1, ut1) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t2 = tcFocus tc2
  case treeNode t2 of
    TNBlock s2 -> mergeBlocks (s1, ut1) (s2, ut2) unifyTC
    _ -> mergeLeftOther ut2 ut1 unifyTC

{- | unify two structs.

The s1 is made the left struct, and s2 is made the right struct.

For closedness, unification only generates a closed struct but not a recursively closed struct since to close a struct
recursively, the only way is to reference the struct via a #ident.
-}
mergeBlocks :: (ResolveMonad s r m) => (Block, UTree) -> (Block, UTree) -> TrCur -> m Tree
mergeBlocks (s1, ut1@UTree{utDir = L}) (s2, ut2) unifyTC =
  let
    eidM1 = getEmbeddedOID ut1
    utAddr1 = tcAddr . utTC $ ut1
    eidM2 = getEmbeddedOID ut2
    utAddr2 = tcAddr . utTC $ ut2
   in
    debugSpanTreeArgsRM
      "mergeBlocks"
      (printf "eidM1: %s, addr1: %s, eidM2: %s, addr2: %s" (show eidM1) (show utAddr1) (show eidM2) (show utAddr2))
      unifyTC
      $ do
        checkRes <- do
          rE1 <- preprocessBlock (utTC ut1) s1
          rE2 <- preprocessBlock (utTC ut2) s2
          return $ do
            r1 <- rE1
            r2 <- rE2
            return (r1, r2)
        case checkRes of
          Left err -> retTr err
          Right (r1, r2) -> mergeBlocksInner (eidM1, r1) (eidM2, r2)
mergeBlocks dt1@(_, UTree{utDir = R}) dt2 unifyTC = mergeBlocks dt2 dt1 unifyTC

mergeBlocksInner :: (ResolveMonad s r m) => (Maybe Int, Block) -> (Maybe Int, Block) -> m Tree
mergeBlocksInner (eidM1, b1@(IsBlockStruct st1)) (eidM2, b2@(IsBlockStruct st2)) = do
  bid <- allocRMObjID
  let merged = fieldsToBlock bid (unionFields (st1, eidM1) (st2, eidM2)) (b1, st1, eidM1) (b2, st2, eidM2)
  -- in reduce, the new combined fields will be checked by the combined patterns.
  retTr merged
mergeBlocksInner (_, b1) (_, b2) = throwErrSt $ printf "unexpected block types: %s, %s" (show b1) (show b2)

fieldsToBlock :: Int -> [(T.Text, Field)] -> (Block, Struct, Maybe Int) -> (Block, Struct, Maybe Int) -> Tree
fieldsToBlock bid fields (blk1, st1, eidM1) (blk2, st2, eidM2) =
  mkBlockTree $
    emptyBlock
      { blkID = bid
      , blkOrdLabels = unionLabels blk1 blk2
      , blkBindings = blkBindings blk1 `Map.union` blkBindings blk2
      , blkStaticFields =
          if
            | isNothing eidM1 && isNothing eidM2 ->
                Map.unionWith
                  ( \l r ->
                      Field
                        { ssfValue = mkMutableTree $ mkUnifyOp [ssfValue l, ssfValue r]
                        , ssfAttr = mergeAttrs (ssfAttr l) (ssfAttr r)
                        , ssfObjects = Set.empty
                        }
                  )
                  (blkStaticFields blk1)
                  (blkStaticFields blk2)
            | isNothing eidM1 -> blkStaticFields blk1
            | isNothing eidM2 -> blkStaticFields blk2
            | otherwise -> Map.empty
      , blkDynFields = combinedPendSubs
      , blkCnstrs = combinedPatterns
      , blkValue =
          BlockStruct $
            emptyStruct
              { stcFields = Map.fromList fields
              , stcClosed = stcClosed st1 || stcClosed st2
              , stcPerms =
                  let neitherEmbedded = isNothing eidM1 && isNothing eidM2
                   in -- st1 and st2 could be both closed.
                      stcPerms st1
                        ++ stcPerms st2
                        -- st2 as an opposite struct of st1
                        ++ [mkPermItem blk1 blk2 | neitherEmbedded && stcClosed st1]
                        -- st1 as an opposite struct of st2
                        ++ [mkPermItem blk2 blk1 | neitherEmbedded && stcClosed st2]
              }
      }
 where
  combinedPendSubs = IntMap.union (blkDynFields blk1) (blkDynFields blk2)
  -- The combined patterns are the patterns of the first struct and the patterns of the second struct.
  combinedPatterns = IntMap.union (blkCnstrs blk1) (blkCnstrs blk2)

  mkPermItem :: Block -> Block -> PermItem
  mkPermItem blk opBlk =
    PermItem
      { piCnstrs = Set.fromList $ IntMap.keys $ blkCnstrs blk
      , -- TODO: exclude let bindings
        piLabels = Set.fromList $ blkOrdLabels blk
      , -- TODO: exclude let bindings
        piOpLabels = Set.fromList $ blkOrdLabels opBlk
      }

{- | Merge two fields.

The structs can not be both embedded.
-}
unionFields :: (Struct, Maybe Int) -> (Struct, Maybe Int) -> [(T.Text, Field)]
unionFields (st1, eidM1) (st2, eidM2) =
  foldr
    ( \label acc ->
        let
          f1M = lookupStructField label st1
          f2M = lookupStructField label st2
         in
          if
            | label `Set.member` l1Set && label `Set.member` l2Set
            , Just sf1 <- f1M
            , Just sf2 <- f2M ->
                (label, _mkUnifiedField sf1 sf2) : acc
            | label `Set.member` l1Set, Just sf1 <- f1M -> (label, _toDisjoinedField eidM1 sf1) : acc
            | label `Set.member` l2Set, Just sf2 <- f2M -> (label, _toDisjoinedField eidM2 sf2) : acc
            | otherwise -> acc
    )
    []
    (Set.toList $ Set.union l1Set l2Set)
 where
  fields1 = stcFields st1
  fields2 = stcFields st2
  l1Set = Map.keysSet fields1
  l2Set = Map.keysSet fields2

-- Put the static field labels in the order of the first struct and append the labels that are not in the first
-- struct.
-- For dynamic fields, we just append them to the end of the list.
unionLabels :: Block -> Block -> [BlockLabel]
unionLabels blk1 blk2 =
  blkOrdLabels blk1
    ++ foldr
      ( \l acc -> case l of
          BlockFieldLabel fl -> if fl `Set.member` l1Set then acc else l : acc
          BlockDynFieldOID _ -> l : acc
      )
      []
      (blkOrdLabels blk2)
 where
  l1Set = Map.keysSet (blkStaticFields blk1)

_toDisjoinedField :: Maybe Int -> Field -> Field
_toDisjoinedField eidM sf = sf{ssfObjects = maybe Set.empty (\i -> Set.fromList [i]) eidM `Set.union` ssfObjects sf}

-- | Merge two fields by creating a unify node with merged attributes.
_mkUnifiedField :: Field -> Field -> Field
_mkUnifiedField sf1 sf2 =
  let
    -- No original node exists yet
    unifyValOp = mkUnifyOp [ssfValue sf1, ssfValue sf2]
   in
    Field
      { ssfValue = mkMutableTree unifyValOp
      , ssfAttr = mergeAttrs (ssfAttr sf1) (ssfAttr sf2)
      , ssfObjects = ssfObjects sf1 `Set.union` ssfObjects sf2
      }

{- | Preprocess the block.

It does the followings:

1. Validate if the identifier of the any reference in the sub tree is in the scope.
2. Rewrite the identifier of the let bindings in the block with the sid.

According to spec, A block is a possibly empty sequence of declarations.

The scope of a declared identifier is the extent of source text in which the identifier denotes the specified field,
alias, or package.
-}
preprocessBlock :: (ResolveMonad s r m) => TrCur -> Block -> m (Either Tree Block)
preprocessBlock blockTC block = do
  rM <- validateRefIdents blockTC
  maybe
    ( do
        let
          bid = blkID block
          blockAddr = tcAddr blockTC
        appended <- _appendSIDToLetRef blockAddr bid blockTC
        -- rewrite all ident keys of the let bindings map with the sid.
        case treeNode appended of
          TNBlock blk -> do
            let
              lets =
                Map.fromList $
                  map
                    (\(k, v) -> (T.append k (T.pack $ "_" ++ show bid), v))
                    (Map.toList $ blkBindings blk)
              newBlock = blk{blkBindings = lets}
            let newBlockTC = setTCFocusTN (TNBlock newBlock) blockTC
            concrete <- consolidateRefs newBlockTC
            case treeNode concrete of
              TNBlock b -> return $ Right b
              _ -> throwErrSt $ printf "consolidated block is not a block: %s" (show concrete)
          _ -> throwErrSt $ printf "tree must be struct, but got %s" (show appended)
    )
    (return . Left)
    rM

{- | Validate if the identifier of the any reference in the sub tree is in the scope.

This is needed because after merging two blocks, some not found references could become valid because the merged block
could have the identifier. Because we are destroying the block and replace it with the merged block, we need to check
all sub references to make sure later reducing them will not cause them to find newly created identifiers.
-}
validateRefIdents :: (ResolveMonad s r m) => TrCur -> m (Maybe Tree)
validateRefIdents _tc =
  snd <$> traverseTC _extAllSubNodes find (_tc, Nothing)
 where
  find (tc, acc) = do
    case tc of
      TCFocus (IsRef _ (Reference{refArg = RefPath ident _})) -> do
        m <- searchTCIdent ident tc
        maybe
          (return (tc, Just $ mkBottomTree $ printf "identifier %s is not found" ident))
          (const $ return (tc, acc))
          m
      _ -> return (tc, acc)

{- | Append the ident of all references in the tree cursor with the sid if the ident references a let binding which is
declared in the block specified by the block address.

This makes sure after merging two structs, two same references from two different structs referencing the same let name
will not conflict with each other.
-}
_appendSIDToLetRef :: (ResolveMonad s r m) => TreeAddr -> Int -> TrCur -> m Tree
_appendSIDToLetRef blockAddr sid _tc =
  tcFocus <$> traverseTCSimple _extAllSubNodes rewrite _tc
 where
  rewrite tc =
    let focus = tcFocus tc
     in case focus of
          IsRef mut ref@(Reference{refArg = RefPath ident _}) -> do
            m <- searchTCIdent ident tc
            maybe
              (return focus)
              ( \(addr, isLB) -> do
                  if isLB && (Just blockAddr == initTreeAddr addr)
                    then do
                      let newFocus = setTN focus (TNMutable $ setMutOp (Ref $ append ref) mut)
                      return newFocus
                    else return focus
              )
              ( do
                  (x, y) <- m
                  return (tcAddr x, y)
              )
          _ -> return focus

  append :: Reference -> Reference
  append ref@(Reference{refArg = RefPath ident sels}) =
    ref{refArg = RefPath (T.append ident (T.pack $ '_' : show sid)) sels}
  append r = r

-- | Extended version of all sub nodes of the tree, including patterns, dynamic fields and let bindings.
_extAllSubNodes :: Tree -> [(TASeg, Tree)]
_extAllSubNodes x = subNodes x ++ rawNodes x

mergeLeftDisj :: (ResolveMonad s r m) => (Disj, UTree) -> UTree -> TrCur -> m Tree
mergeLeftDisj (dj1, ut1) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t2 = tcFocus tc2
  case treeNode t2 of
    TNMutable _ -> mergeLeftOther ut2 ut1 unifyTC
    TNAtomCnstr _ -> mergeLeftOther ut2 ut1 unifyTC
    TNRefCycle{} -> mergeLeftOther ut2 ut1 unifyTC
    TNDisj dj2 -> mergeDisjWithDisj (dj1, ut1) (dj2, ut2) unifyTC
    -- this is the case for a disjunction unified with a value.
    _ -> mergeDisjWithVal (dj1, ut1) ut2 unifyTC

-- Note: isEmbedded is still required. Think about the following values,
-- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
-- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
-- In current CUE's implementation, CUE puts the fields of the single value first.
mergeDisjWithVal :: (ResolveMonad s r m) => (Disj, UTree) -> UTree -> TrCur -> m Tree
mergeDisjWithVal (dj1, _ut1@(UTree{utDir = fstDir})) _ut2 unifyTC =
  debugSpanTreeRM "mergeDisjWithVal" unifyTC $ do
    uts1 <- utsFromDisjs (length $ dsjDisjuncts dj1) _ut1
    let defIdxes1 = dsjDefIndexes dj1
    if fstDir == L
      -- uts1 & ut2 generates a m x 1 matrix.
      then do
        matrix <- mapM (\ut1 -> unifyForNewBinConjs ut1 _ut2 unifyTC) uts1
        treeFromMatrix (defIdxes1, []) (length uts1, 1) [matrix]
      -- ut2 & uts1 generates a 1 x m matrix.
      else do
        matrix <- mapM (\ut1 -> unifyForNewBinConjs ut1 _ut2 unifyTC) uts1
        treeFromMatrix ([], defIdxes1) (1, length uts1) (map (: []) matrix)

{- | Unify two disjuncts.

We do not need to compute the unification of default values since they are already unified in the disjuncts. We just
need to pick the correct indexes of the default values from the matrix.

Some rules for unifying disjuncts:

U0: ⟨v1⟩ & ⟨v2⟩         => ⟨v1&v2⟩
U1: ⟨v1, d1⟩ & ⟨v2⟩     => ⟨v1&v2, d1&v2⟩
U2: ⟨v1, d1⟩ & ⟨v2, d2⟩ => ⟨v1&v2, d1&d2⟩
-}
mergeDisjWithDisj :: (ResolveMonad s r m) => (Disj, UTree) -> (Disj, UTree) -> TrCur -> m Tree
mergeDisjWithDisj (dj1, _ut1@(UTree{utDir = fstDir})) (dj2, _ut2) unifyTC =
  debugSpanTreeRM "mergeDisjWithDisj" unifyTC $ do
    uts1 <- utsFromDisjs (length $ dsjDisjuncts dj1) _ut1
    uts2 <- utsFromDisjs (length $ dsjDisjuncts dj2) _ut2
    let
      defIdxes1 = dsjDefIndexes dj1
      defIdxes2 = dsjDefIndexes dj2

    if fstDir == L
      -- uts1 & uts2 generates a m x n matrix.
      then do
        matrix <- mapM (\ut1 -> mapM (\ut2 -> unifyForNewBinConjs ut1 ut2 unifyTC) uts2) uts1
        treeFromMatrix (defIdxes1, defIdxes2) (length uts1, length uts2) matrix
      -- uts2 & uts1 generates a n x m matrix.
      else do
        matrix <- mapM (\ut2 -> mapM (\ut1 -> unifyForNewBinConjs ut2 ut1 unifyTC) uts1) uts2
        treeFromMatrix (defIdxes2, defIdxes1) (length uts2, length uts1) matrix

utsFromDisjs :: (EnvIO r s m) => Int -> UTree -> m [UTree]
utsFromDisjs n ut@(UTree{utTC = tc}) = do
  mapM
    ( \i -> do
        djTC <- goDownTCSegMust (DisjRegTASeg i) tc
        return $ ut{utTC = djTC}
    )
    [0 .. (n - 1)]

treeFromMatrix :: (EnvIO r s m) => ([Int], [Int]) -> (Int, Int) -> [[Maybe Tree]] -> m Tree
treeFromMatrix (lDefIndexes, rDefIndexes) (m, n) matrix = do
  let defIndexes = case (lDefIndexes, rDefIndexes) of
        ([], []) -> []
        -- For each i in the left default indexes, we have a list of default values, x<i,0>, x<i,1>, ..., x<i,(n-1)>
        (ls, []) -> concatMap (\i -> map (+ (i * n)) [0 .. n - 1]) ls
        -- For each j in the right default indexes, we have a list of default values, x<0,j>, x<1,j>, ..., x<(m-1),j>
        ([], rs) -> concatMap (\j -> map (\i -> (i * n) + j) [0 .. m - 1]) rs
        -- For each i in the left default indexes, we have one default value, x<i,j>.
        (ls, rs) -> concatMap (\i -> map (+ (i * n)) rs) ls
      disjuncts = concat matrix
      (newDefIndexes, newDisjuncts) = removeIncompleteDisjuncts defIndexes disjuncts
  return $ mkDisjTree $ emptyDisj{dsjDefIndexes = newDefIndexes, dsjDisjuncts = newDisjuncts}

-- | TODO: efficient implementation
removeIncompleteDisjuncts :: [Int] -> [Maybe Tree] -> ([Int], [Tree])
removeIncompleteDisjuncts defIdxes ts =
  let (x, y, _) =
        foldl
          ( \(accIdxes, accDjs, removeCnt) (i, dj) -> case dj of
              Nothing -> (accIdxes, accDjs, removeCnt + 1)
              Just v ->
                ( if i `elem` defIdxes then accIdxes ++ [i - removeCnt] else accIdxes
                , accDjs ++ [v]
                , removeCnt
                )
          )
          ([], [], 0)
          (zip [0 ..] ts)
   in (x, y)

consolidateRefs :: (ResolveMonad s r m) => TrCur -> m Tree
consolidateRefs ptc = do
  let blockAddr = Cursor.tcAddr ptc
  utc <- traverseTCSimple subNodes (consolidate blockAddr) ptc
  return $ Cursor.tcFocus utc
 where
  -- Mark the outer references with the original value address.
  consolidate :: (ResolveMonad s r m) => TreeAddr -> TrCur -> m Tree
  consolidate blockAddr tc = do
    let focus = Cursor.tcFocus tc
    case focus of
      IsRef mut rf
        | Just fieldPath <- fieldPathFromRef rtrAtom rf -> do
            tarIdentAddrM <- searchIdent fieldPath tc
            (r, isInner) <-
              maybe
                (return (setTN focus TNNoValRef, False))
                ( \tarIdentAddr -> do
                    let isInner = isPrefix blockAddr tarIdentAddr && blockAddr /= tarIdentAddr
                    return $
                      if
                        -- If the reference is an inner reference, we set the tree version to 0 to mark it
                        -- un-reduced and set the mutable value to Nothing.
                        | isInner -> (invalidateMutable focus, True)
                        | Just v <- getMutVal mut -> (v, False)
                        | otherwise -> (setTN focus TNNoValRef, False)
                )
                tarIdentAddrM
            debugInstantRM
              "consolidateRefs"
              ( printf
                  "fieldPath: %s, blockAddr: %s, tarIdentAddrM: %s, isInner: %s"
                  (show fieldPath)
                  (show blockAddr)
                  (show tarIdentAddrM)
                  (show isInner)
              )
              tc
            return r
      _ -> return focus

  -- Search the first identifier of the reference and convert it to absolute tree addr if it exists.
  searchIdent :: (ResolveMonad s r m) => FieldPath -> TrCur -> m (Maybe TreeAddr)
  searchIdent ref xtc = do
    let fstSel = fromJust $ headSel ref
    ident <- selToIdent fstSel
    resM <- searchTCIdent ident xtc
    return $ tcAddr . fst <$> resM
