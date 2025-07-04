{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.UnifyOp where

import qualified AST
import Common (
  Config (..),
  Env,
  HasConfig (..),
  RuntimeParams (RuntimeParams, rpCreateCnstr),
 )
import Control.Monad (foldM, forM, when)
import Control.Monad.Reader (asks)
import Cursor
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isNothing)
import qualified Data.Set as Set
import qualified Data.Text as T
import Exception (throwErrSt)
import Path
import Reduce.RMonad (
  ReduceMonad,
  allocRMObjID,
  debugInstantRM,
  debugSpanArgsRM,
  debugSpanRM,
 )
import Reduce.RefSys (searchTCIdent)
import {-# SOURCE #-} Reduce.Root (reduceToNonMut, reduceUnifyConj)
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
      <> show (tcCanAddr tc)
      <> ","
      <> show (tcFocus tc)

{- | Get the embedded object ID of the tree. The embedded object ID is the last embedded object ID in the tree address.

Because unification is a top down operation, no nested embedded object ID has been found yet. So we can just return the
last embedded object ID in the tree address.
-}
getEmbeddedOID :: UTree -> Maybe Int
getEmbeddedOID ut =
  let TreeAddr segs = tcCanAddr (utTC ut)
      getEID (StructTASeg (EmbedTASeg i)) = Just i
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

-- | Call the unify operator.
unify :: (ReduceMonad s r m) => [Tree] -> TrCur -> m (Maybe Tree)
unify ts tc = do
  tcs <-
    mapM
      (\(i, _) -> goDownTCSegMust (MutArgTASeg i) tc)
      (zip [0 ..] ts)
  unifyTCs tcs tc

{- | Unify a list of trees.

It handles the following cases:
1. If all trees are structurally cyclic, return a bottom tree.
2. Reference cycle.

The order of the unification is the same as the order of the trees.

The tree cursor is only used to know where the unification is happening.
-}
unifyTCs :: (ReduceMonad s r m) => [TrCur] -> TrCur -> m (Maybe Tree)
unifyTCs tcs unifyTC = debugSpanArgsRM "unifyTCs" (showTCList tcs) id unifyTC $ do
  let
    unifyAddr = tcCanAddr unifyTC
    isAllCyclic = all (treeIsCyclic . tcFocus) tcs

  if isAllCyclic
    then return $ Just $ mkBottomTree "structural cycle"
    else do
      normalized <-
        foldM
          ( \acc ut -> do
              r <- normalizeConjunct ut
              return $ acc ++ r
          )
          []
          tcs

      case sequence normalized of
        Nothing -> return Nothing
        Just readies -> do
          debugInstantRM "unifyTCs" (printf "normalized: %s" (show normalized)) unifyTC
          -- Remove the reference cycle.
          let (regs, rcs, subRCs) =
                foldr
                  ( \tc (accRegs, accRCs, accSubRCs) -> case (treeNode . tcFocus) tc of
                      TNRefCycle rcAddr
                        -- This is the case where the operand is a reference cycle, even though the operand could be a
                        -- conjunct in a disjunction. For example, x: x&{a:1} | {b:1}
                        --
                        -- According to the spec, A field value of the form r & v, where r evaluates to a reference
                        -- cycle and v is a concrete value, evaluates to v. Unification is idempotent and unifying a
                        -- value with itself ad infinitum, which is what the cycle represents, results in this value.
                        -- Implementations should detect cycles of this kind, ignore r, and take v as the result of
                        -- unification.
                        | rcAddr == trimToReferable unifyAddr -> (accRegs, tc : accRCs, accSubRCs)
                        -- This is the case where the conjunct is referecing the sub field value,
                        -- e.g. x: x.z & {z: a: 1}
                        -- or
                        -- x: x.z & {z: a: 1} | {y: 1}
                        | let rfbUnifyAddr = trimToReferable unifyAddr
                        , isPrefix rfbUnifyAddr rcAddr
                        , rfbUnifyAddr /= rcAddr ->
                            (accRegs, accRCs, trimPrefixTreeAddr rfbUnifyAddr rcAddr : accSubRCs)
                      _ -> (tc : accRegs, accRCs, accSubRCs)
                  )
                  ([], [], [])
                  readies

          debugInstantRM "unifyTCs" (printf "regs: %s, subRCs: %s" (show regs) (show subRCs)) unifyTC

          case (regs, rcs, subRCs) of
            ([], _, _ : _) -> return Nothing
            ([], _, []) -> return $ Just $ tcFocus (head rcs)
            _ -> do
              r <- mergeTCs regs unifyTC
              -- Unify the sub reference cycles.
              foldM
                ( \acc relRCAddr ->
                    maybe
                      (return Nothing)
                      (\(vTC, subVTC) -> unifyBinUTrees (UTree L vTC) (UTree R subVTC) unifyTC)
                      ( do
                          v <- acc
                          let vTC = v `setTCFocus` unifyTC
                          subVTC <- goDownTCAddr relRCAddr vTC
                          return (vTC, subVTC)
                      )
                )
                r
                subRCs

{- | Normalize the unify operation tree.

It does the following:
1. Flatten the unify operation tree because unification is associative.
2. Reduce ref and disjoin mutable to basic form.
3. For the struct, it ignores the non-struct embedded value and build conjuncts for embeds if they exist.
-}
normalizeConjunct :: (ReduceMonad s r m) => TrCur -> m [Maybe TrCur]
normalizeConjunct tc = debugSpanRM "normalizeConjunct" (const Nothing) tc $ do
  conjM <- reduceUnifyConj tc
  case conjM of
    Nothing -> return [Nothing]
    Just conj -> do
      let conjTC = conj `setTCFocus` tc
      case treeNode conj of
        TNMutable (MutOp (UOp u)) ->
          foldM
            ( \acc (i, _) -> do
                subConjTC <- goDownTCSegMust (MutArgTASeg i) conjTC
                subs <- normalizeConjunct subConjTC
                return $ acc ++ subs
            )
            []
            (zip [0 ..] (toList $ ufConjuncts u))
        TNBlock es@(Block{blkStruct = struct}) -> do
          -- If the struct is a sole conjunct of a unify operation, it will have its embedded values as newly discovered
          -- conjuncts. For example, x: {a: 1, b} -> x: {a: 1} & b
          -- If it is not, it can still have embedded values. For example, x: {a: 1, b} & {} -> x: {a:1} & b & {}
          -- Either way, we try to normalize the embedded values.
          embeds <-
            foldM
              ( \acc i -> do
                  subConjTC <- goDownTCSegMust (StructTASeg (EmbedTASeg i)) conjTC
                  subs <- normalizeConjunct subConjTC
                  return $ acc ++ subs
              )
              []
              (IntMap.keys $ blkEmbeds es)

          if hasEmptyFields struct && not (null $ blkEmbeds es)
            -- If the struct is an empty struct with only embedded values, we can just return the embedded values.
            then return embeds
            else do
              -- Since we have normalized the embedded values, we need to remove them from the struct to prevent
              -- normalizing them again, causing infinite loop.
              let pureStructTC = setTCFocusTN (TNBlock $ es{blkEmbeds = IntMap.empty}) conjTC
              return $ Just pureStructTC : embeds
        _ -> return [Just conjTC]

{- | Unify two UTrees.

It is called in the mergeBin functions so that the order of the operands can be preserved.
-}
unifyBinUTrees :: (ReduceMonad s r m) => UTree -> UTree -> TrCur -> m (Maybe Tree)
unifyBinUTrees ut1@(UTree{utDir = L}) ut2 tc = unifyTCs (map utTC [ut1, ut2]) tc
unifyBinUTrees ut1@(UTree{utDir = R}) ut2 tc = unifyTCs (map utTC [ut2, ut1]) tc

mergeTCs :: (ReduceMonad s r m) => [TrCur] -> TrCur -> m (Maybe Tree)
mergeTCs tcs unifyTC = debugSpanArgsRM "mergeTCs" (showTCList tcs) id unifyTC $ do
  when (null tcs) $ throwErrSt "not enough arguments"
  rM <-
    foldM
      ( \accM tc -> case accM of
          Nothing -> return Nothing
          Just acc -> do
            rM <- mergeBinUTrees (acc{utDir = L}) (UTree{utDir = R, utTC = tc}) unifyTC
            maybe
              (return Nothing)
              (\r -> return $ Just $ acc{utTC = r `setTCFocus` utTC acc})
              rM
      )
      (Just $ UTree{utDir = L, utTC = head tcs})
      (tail tcs)
  maybe (return Nothing) (\r -> return $ Just $ tcFocus (utTC r)) rM

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
mergeBinUTrees :: (ReduceMonad s r m) => UTree -> UTree -> TrCur -> m (Maybe Tree)
mergeBinUTrees ut1@(UTree{utTC = tc1}) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t1 = tcFocus tc1
      t2 = tcFocus tc2
  debugSpanArgsRM
    "mergeBinUTrees"
    ( printf
        ("merging %s, %s" ++ "\n" ++ "with %s, %s")
        (show $ utDir ut1)
        (show t1)
        (show $ utDir ut2)
        (show t2)
    )
    id
    unifyTC
    $ do
      -- Each case should handle embedded case when the left value is embedded.
      rM <- case (treeNode t1, treeNode t2) of
        (TNBottom _, _) -> retTr t1
        (_, TNBottom _) -> retTr t2
        (TNTop, _) -> mergeLeftTop ut1 ut2
        (_, TNTop) -> mergeLeftTop ut2 ut1
        (TNAtom a1, _) -> mergeLeftAtom (a1, ut1) ut2 unifyTC
        -- Below is the earliest time to create a constraint
        (_, TNAtom a2) -> mergeLeftAtom (a2, ut2) ut1 unifyTC
        (TNDisj dj1, _) -> mergeLeftDisj (dj1, ut1) ut2 unifyTC
        (_, TNDisj dj2) -> mergeLeftDisj (dj2, ut2) ut1 unifyTC
        (TNBlock es1, _) -> mergeLeftBlock (es1, ut1) ut2 unifyTC
        (_, TNBlock es2) -> mergeLeftBlock (es2, ut2) ut1 unifyTC
        (TNBounds b1, _) -> mergeLeftBound (b1, ut1) ut2 unifyTC
        (_, TNBounds b2) -> mergeLeftBound (b2, ut2) ut1 unifyTC
        _ -> mergeLeftOther ut1 ut2 unifyTC

      -- close the merged tree
      maybe
        (return Nothing)
        (\r -> retTr (r{treeRecurClosed = treeRecurClosed t1 || treeRecurClosed t2}))
        rM

retTr :: (ReduceMonad s r m) => Tree -> m (Maybe Tree)
retTr = return . Just

mergeLeftTop :: (ReduceMonad s r m) => UTree -> UTree -> m (Maybe Tree)
mergeLeftTop _ ut2 = do
  let t2 = tcFocus (utTC ut2)
  retTr t2

mergeLeftAtom :: (ReduceMonad s r m) => (Atom, UTree) -> UTree -> TrCur -> m (Maybe Tree)
mergeLeftAtom (v1, ut1@(UTree{utDir = d1})) ut2@(UTree{utTC = tc2, utDir = d2}) unifyTC =
  debugSpanRM "mergeLeftAtom" id unifyTC $ do
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
        -- logDebugStrRM $ printf "mergeLeftAtom, %s with Bounds: %s" (show v1) (show t2)
        return $ Just $ mergeAtomBounds (d1, v1) (d2, bdsList b)
      (_, TNAtomCnstr c) ->
        if v1 == cnsAtom c
          then retTr t2
          else retTr $ mkBottomTree $ printf "values mismatch: %s != %s" (show v1) (show $ cnsAtom c)
      (_, TNDisj dj2) -> do
        -- logDebugStrRM $ printf "mergeLeftAtom: TNDisj %s, %s" (show t2) (show v1)
        mergeLeftDisj (dj2, ut2) ut1 unifyTC
      (_, TNMutable mut2)
        -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
        -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
        -- marked disjunction.
        | (MutOp (DisjOp _)) <- mut2 -> mergeLeftOther ut2 ut1 unifyTC
        | otherwise -> mkCnstrOrOther t2
      (_, TNRefCycle _) -> mkCnstrOrOther t2
      (_, TNBlock s2) -> mergeLeftBlock (s2, ut2) ut1 unifyTC
      _ -> mergeLeftOther ut1 ut2 unifyTC
 where
  rtn :: (ReduceMonad s r m) => TreeNode -> m (Maybe Tree)
  rtn = return . Just . mkNewTree

  amismatch :: (Show a) => a -> a -> TreeNode
  amismatch x y = TNBottom . Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

  mkCnstrOrOther :: (ReduceMonad s r m) => Tree -> m (Maybe Tree)
  mkCnstrOrOther t2 = do
    RuntimeParams{rpCreateCnstr = cc} <- asks (cfRuntimeParams . getConfig)
    -- logDebugStrRM $ printf "mergeLeftAtom: cc: %s, procOther: %s, %s" (show cc) (show ut1) (show ut2)
    if cc
      then do
        c <- mkCnstr v1 t2
        -- logDebugStrRM $ printf "mergeLeftAtom: constraint created, %s" (show c)
        retTr c
      else mergeLeftOther ut2 ut1 unifyTC

mkCnstr :: (ReduceMonad s r m) => Atom -> Tree -> m Tree
mkCnstr a cnstr = do
  let op = mkMutableTree $ mkUnifyOp [mkAtomTree a, cnstr]
  e <- buildASTExpr op
  return $ mkCnstrTree a e

mergeLeftBound :: (ReduceMonad s r m) => (Bounds, UTree) -> UTree -> TrCur -> m (Maybe Tree)
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
              Nothing -> retTr (mkBoundsTree (fst r))
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
  conflict = let conv x = AST.exprStr $ buildBoundASTExpr x in printf "bounds %s and %s conflict" (conv b1) (conv b2)

  newOrdBounds :: [Bound]
  newOrdBounds = if d1 == L then [b1, b2] else [b2, b1]

-- | mergeLeftOther is the sink of the unification process.
mergeLeftOther :: (ReduceMonad s r m) => UTree -> UTree -> TrCur -> m (Maybe Tree)
mergeLeftOther ut1@(UTree{utTC = tc1}) ut2 unifyTC = do
  let t1 = tcFocus tc1
  case treeNode t1 of
    TNRefCycle _ -> throwErrSt "ref cycle should not be used in merge"
    (TNMutable (Mutable mop _)) -> case mop of
      Ref _ -> throwErrSt "ref should not be used in merge"
      DisjOp _ -> throwErrSt "disjoin should not be used in merge"
      _ -> do
        case mop of
          RegOp _ -> return ()
          Compreh _ -> return ()
          _ -> throwErrSt (printf "unexpected tree node: %s" (showTreeSymbol t1))
        -- The tc1 should be be a regular op or comprehension tree. We need to reduce it to get the non-mutable result.
        r1M <- reduceToNonMut tc1
        maybe
          (return Nothing)
          (\r1 -> unifyBinUTrees (ut1{utTC = r1 `setTCFocus` tc1}) ut2 unifyTC)
          r1M

    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    (TNAtomCnstr c1) -> do
      naM <- unifyBinUTrees (ut1{utTC = mkNewTree (TNAtom $ cnsAtom c1) `setTCFocus` tc1}) ut2 unifyTC
      maybe
        (return Nothing)
        ( \na -> case treeNode na of
            TNBottom _ -> retTr na
            _ -> retTr t1
        )
        naM
    _ -> returnNotUnifiable ut1 ut2

returnNotUnifiable :: (ReduceMonad s r m) => UTree -> UTree -> m (Maybe Tree)
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

mergeLeftBlock :: (ReduceMonad s r m) => (Block, UTree) -> UTree -> TrCur -> m (Maybe Tree)
mergeLeftBlock (s1, ut1) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t2 = tcFocus tc2
  if
    -- When the left struct is an empty struct with non empty embedded fields, meaning it is an embedded value, we can
    -- just return the right value because embedded value has been added as conjunct.
    -- For example, {int} & 1 -> {} & 1 & int
    -- The 1 and int are re-ordered, but the result should be the same.
    -- \| hasEmptyFields s1 && not (null $ stcEmbeds s1) -> retTr t2
    -- -- When the left is an empty struct and the right value is an embedded value of type non-struct, meaning we are
    -- -- using the embedded value to replace the struct.
    -- -- For example, the parent struct is {a: 1, b}, and the function is {a: 1} & b.
    -- \| hasEmptyFields s1 && isJust (utEmbedID ut2) -> case treeNode t2 of
    --     TNBlock s2 -> mergeBlocks (s1, ut1) (s2, ut2)
    --     _ -> retTr t2
    | otherwise -> case treeNode t2 of
        TNBlock s2 -> mergeBlocks (s1, ut1) (s2, ut2) unifyTC
        _ -> mergeLeftOther ut2 ut1 unifyTC

{- | unify two structs.

The s1 is made the left struct, and s2 is made the right struct.

For closedness, unification only generates a closed struct but not a recursively closed struct since to close a struct
recursively, the only way is to reference the struct via a #ident.
-}
mergeBlocks ::
  (ReduceMonad s r m) =>
  (Block, UTree) ->
  (Block, UTree) ->
  TrCur ->
  m (Maybe Tree)
mergeBlocks (s1, ut1@UTree{utDir = L}) (s2, ut2) unifyTC =
  let
    eidM1 = getEmbeddedOID ut1
    utAddr1 = tcCanAddr . utTC $ ut1
    eidM2 = getEmbeddedOID ut2
    utAddr2 = tcCanAddr . utTC $ ut2
   in
    debugSpanArgsRM
      "mergeBlocks"
      (printf "eidM1: %s, addr1: %s, eidM2: %s, addr2: %s" (show eidM1) (show utAddr1) (show eidM2) (show utAddr2))
      id
      unifyTC
      $ do
        checkRes <- do
          rE1 <- _preprocessBlock (utTC ut1) s1
          rE2 <- _preprocessBlock (utTC ut2) s2
          return $ do
            r1 <- rE1
            r2 <- rE2
            return (r1, r2)
        case checkRes of
          Left err -> retTr err
          Right (r1, r2) -> mergeStructsInner (eidM1, r1) (eidM2, r2)
mergeBlocks dt1@(_, UTree{utDir = R}) dt2 unifyTC = mergeBlocks dt2 dt1 unifyTC

mergeStructsInner ::
  (ReduceMonad s r m) =>
  (Maybe Int, Struct) ->
  (Maybe Int, Struct) ->
  m (Maybe Tree)
mergeStructsInner (eidM1, s1) (eidM2, s2) = do
  -- when (isJust eidM1 && isJust eidM2) $ throwErrSt "both structs are embedded, not allowed"

  sid <- allocRMObjID
  let merged = fieldsToStruct sid (_unionFields (s1, eidM1) (s2, eidM2)) (s1, eidM1) (s2, eidM2)
  -- in reduce, the new combined fields will be checked by the combined patterns.
  retTr merged

fieldsToStruct ::
  Int -> [(T.Text, Field)] -> (Struct, Maybe Int) -> (Struct, Maybe Int) -> Tree
fieldsToStruct sid fields (st1, eidM1) (st2, eidM2) =
  mkStructTree $
    emptyStruct
      { stcID = sid
      , stcOrdLabels = map fst fields
      , stcBlockIdents = case (eidM1, eidM2) of
          (Nothing, Nothing) -> stcBlockIdents st1 `Set.union` stcBlockIdents st2
          (Just _, Nothing) -> stcBlockIdents st2
          (Nothing, Just _) -> stcBlockIdents st1
          (Just _, Just _) -> Set.empty
      , stcFields = Map.fromList fields
      , stcLets = stcLets st1 `Map.union` stcLets st2
      , stcDynFields = combinedPendSubs
      , stcCnstrs = combinedPatterns
      , stcClosed = stcClosed st1 || stcClosed st2
      , stcPerms =
          let neitherEmbedded = isNothing eidM1 && isNothing eidM2
           in -- st1 and st2 could be both closed.
              stcPerms st1
                ++ stcPerms st2
                -- st2 as an opposite struct of st1
                ++ [mkPermItem st1 st2 | neitherEmbedded && stcClosed st1]
                -- st1 as an opposite struct of st2
                ++ [mkPermItem st2 st1 | neitherEmbedded && stcClosed st2]
      }
 where
  combinedPendSubs = IntMap.union (stcDynFields st1) (stcDynFields st2)
  -- The combined patterns are the patterns of the first struct and the patterns of the second struct.
  combinedPatterns = IntMap.union (stcCnstrs st1) (stcCnstrs st2)

  mkPermItem :: Struct -> Struct -> PermItem
  mkPermItem struct opStruct =
    PermItem
      { piCnstrs = Set.fromList $ IntMap.keys $ stcCnstrs struct
      , -- TODO: exclude let bindings
        piLabels = Set.fromList $ stcOrdLabels struct
      , piDyns = Set.fromList $ IntMap.keys $ stcDynFields struct
      , -- TODO: exclude let bindings
        piOpLabels = Set.fromList $ stcOrdLabels opStruct
      , piOpDyns = Set.fromList $ IntMap.keys $ stcDynFields opStruct
      }

{- | Merge two fields.

The structs can not be both embedded.
-}
_unionFields :: (Struct, Maybe Int) -> (Struct, Maybe Int) -> [(T.Text, Field)]
_unionFields (st1, eidM1) (st2, eidM2) =
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
                (label, _mkUnifiedField (sf1, eidM1) (sf2, eidM2)) : acc
            | label `Set.member` l1Set, Just sf1 <- f1M -> (label, _toDisjoinedField eidM1 sf1) : acc
            | label `Set.member` l2Set, Just sf2 <- f2M -> (label, _toDisjoinedField eidM2 sf2) : acc
            | otherwise -> acc
    )
    []
    unionLabels
 where
  fields1 = stcFields st1
  fields2 = stcFields st2
  l1Set = Map.keysSet fields1
  l2Set = Map.keysSet fields2

  -- Put the labels in the order of the first struct and append the labels that are not in the first struct.
  unionLabels =
    stcOrdLabels st1
      ++ foldr (\l acc -> if l `Set.member` l1Set then acc else l : acc) [] (stcOrdLabels st2)

getBaseRaw :: Maybe Int -> Field -> Maybe Tree
getBaseRaw eidM sf =
  if isNothing eidM
    then ssfBaseRaw sf
    else Nothing

_toDisjoinedField :: Maybe Int -> Field -> Field
_toDisjoinedField eidM sf =
  sf
    { ssfBaseRaw = getBaseRaw eidM sf
    , ssfObjects = maybe Set.empty (\i -> Set.fromList [i]) eidM `Set.union` ssfObjects sf
    }

-- | Merge two fields by creating a unify node with merged attributes.
_mkUnifiedField :: (Field, Maybe Int) -> (Field, Maybe Int) -> Field
_mkUnifiedField (sf1, eidM1) (sf2, eidM2) =
  let
    -- No original node exists yet
    unifyValOp = mkUnifyOp [ssfValue sf1, ssfValue sf2]
    -- The field is raw only if it is not of an embedded struct and it has raw base.
    unifiedBaseRaw = case catMaybes [getBaseRaw eidM1 sf1, getBaseRaw eidM2 sf2] of
      [br1, br2] -> Just $ mkMutableTree $ mkUnifyOp [br1, br2]
      [br] -> Just br
      _ -> Nothing
   in
    Field
      { ssfValue = mkMutableTree unifyValOp
      , ssfBaseRaw = unifiedBaseRaw
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
_preprocessBlock ::
  (ReduceMonad s r m) =>
  TrCur ->
  Block ->
  m (Either Tree Struct)
_preprocessBlock blockTC block = do
  rM <- _validateRefIdents blockTC
  -- logDebugStrRM $ printf "_preprocessBlock: rM: %s" (show rM)
  maybe
    ( do
        let
          sid = stcID . blkStruct $ block
          blockAddr = tcCanAddr blockTC
        appended <- _appendSIDToLetRef blockAddr sid blockTC
        -- rewrite all ident keys of the let bindings map with the sid.
        case treeNode appended of
          TNBlock (Block{blkStruct = struct}) -> do
            let
              blockIdents =
                Set.fromList $
                  map
                    ( \k ->
                        if k `Map.member` stcLets struct
                          then T.append k (T.pack $ "_" ++ show sid)
                          else k
                    )
                    (Set.toList $ stcBlockIdents struct)
              lets = Map.fromList $ map (\(k, v) -> (T.append k (T.pack $ "_" ++ show sid), v)) (Map.toList $ stcLets struct)
              newStruct = struct{stcBlockIdents = blockIdents, stcLets = lets}
            -- logDebugStrRM $ printf "_preprocessBlock: newStruct: %s" (show $ mkStructTree newStruct)
            return $ Right newStruct
          _ -> throwErrSt $ printf "tree must be struct, but got %s" (show appended)
    )
    (return . Left)
    rM

{- | Validate if the identifier of the any reference in the sub tree is in the scope.

This is needed because after merging two blocks, some not found references could become valid because the merged block
could have the identifier. Because we are destroying the block and replace it with the merged block, we need to check
all sub references to make sure later reducing them will not cause them to find newly created identifiers.
-}
_validateRefIdents :: (ReduceMonad s r m) => TrCur -> m (Maybe Tree)
_validateRefIdents _tc =
  snd <$> traverseTC _extAllSubNodes find (_tc, Nothing)
 where
  find (tc, acc) = do
    case tc of
      TCFocus (IsRef _ (Reference{refArg = RefPath ident _})) -> do
        m <- searchTCIdent ident tc
        -- logDebugStrRM $ printf "_validateRefIdents: ident: %s, m: %s" ident (show m)
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
_appendSIDToLetRef :: (ReduceMonad s r m) => TreeAddr -> Int -> TrCur -> m Tree
_appendSIDToLetRef blockAddr sid _tc =
  tcFocus <$> traverseTCSimple _extAllSubNodes rewrite _tc
 where
  rewrite tc =
    let focus = tcFocus tc
     in case focus of
          IsRef mut ref@(Reference{refArg = RefPath ident _}) -> do
            m <- searchTCIdent ident tc
            -- logDebugStrRM $ printf "_appendSIDToLetRef: ident: %s, m: %s" ident (show m)

            maybe
              (return focus)
              ( \(addr, isLB) -> do
                  -- logDebugStrRM $
                  --   printf
                  --     "_appendSIDToLetRef: rewrite %s, blockAddr: %s, addr: %s"
                  --     ident
                  --     (show blockAddr)
                  --     (show addr)
                  if isLB && (Just blockAddr == initTreeAddr addr)
                    then do
                      let newFocus = setTN focus (TNMutable $ setMutOp (Ref $ append ref) mut)
                      return newFocus
                    else return focus
              )
              ( do
                  (x, y) <- m
                  return (tcCanAddr x, y)
              )
          _ -> return focus

  append :: Reference -> Reference
  append ref@(Reference{refArg = RefPath ident sels}) =
    ref{refArg = RefPath (T.append ident (T.pack $ '_' : show sid)) sels}
  append r = r

-- | Extended version of all sub nodes of the tree, including patterns, dynamic fields and let bindings.
_extAllSubNodes :: Tree -> [(TASeg, Tree)]
_extAllSubNodes x = subNodes x ++ rawNodes x

mergeLeftDisj :: (ReduceMonad s r m) => (Disj, UTree) -> UTree -> TrCur -> m (Maybe Tree)
mergeLeftDisj (dj1, ut1) ut2@(UTree{utTC = tc2}) unifyTC = do
  -- withAddrAndFocus $ \addr _ ->
  --   logDebugStrRM $ printf "mergeLeftDisj: addr: %s, dj: %s, right: %s" (show addr) (show ut1) (show ut2)
  let t2 = tcFocus tc2
  case treeNode t2 of
    TNMutable _ -> mergeLeftOther ut2 ut1 unifyTC
    TNAtomCnstr _ -> mergeLeftOther ut2 ut1 unifyTC
    TNRefCycle _ -> mergeLeftOther ut2 ut1 unifyTC
    TNDisj dj2 -> mergeDisjWithDisj (dj1, ut1) (dj2, ut2) unifyTC
    -- this is the case for a disjunction unified with a value.
    _ -> mergeDisjWithVal (dj1, ut1) ut2 unifyTC

-- Note: isEmbedded is still required. Think about the following values,
-- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
-- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
-- In current CUE's implementation, CUE puts the fields of the single value first.
mergeDisjWithVal :: (ReduceMonad s r m) => (Disj, UTree) -> UTree -> TrCur -> m (Maybe Tree)
mergeDisjWithVal (dj1, _ut1@(UTree{utDir = fstDir})) _ut2 unifyTC =
  debugSpanRM "mergeDisjWithVal" id unifyTC $ do
    uts1 <- utsFromDisjs (length $ dsjDisjuncts dj1) _ut1
    let defIdxes1 = dsjDefIndexes dj1
    if fstDir == L
      -- uts1 & ut2 generates a m x 1 matrix.
      then do
        matrix <- mapM (\ut1 -> unifyBinUTrees ut1 _ut2 unifyTC) uts1
        treeFromMatrix (defIdxes1, []) (length uts1, 1) [matrix]
      -- ut2 & uts1 generates a 1 x m matrix.
      else do
        matrix <- mapM (\ut1 -> unifyBinUTrees ut1 _ut2 unifyTC) uts1
        treeFromMatrix ([], defIdxes1) (1, length uts1) (map (: []) matrix)

{- | Unify two disjuncts.

We do not need to compute the unification of default values since they are already unified in the disjuncts. We just
need to pick the correct indexes of the default values from the matrix.

Some rules for unifying disjuncts:

U0: ⟨v1⟩ & ⟨v2⟩         => ⟨v1&v2⟩
U1: ⟨v1, d1⟩ & ⟨v2⟩     => ⟨v1&v2, d1&v2⟩
U2: ⟨v1, d1⟩ & ⟨v2, d2⟩ => ⟨v1&v2, d1&d2⟩
-}
mergeDisjWithDisj :: (ReduceMonad s r m) => (Disj, UTree) -> (Disj, UTree) -> TrCur -> m (Maybe Tree)
mergeDisjWithDisj (dj1, _ut1@(UTree{utDir = fstDir})) (dj2, _ut2) unifyTC =
  debugSpanRM "mergeDisjWithDisj" id unifyTC $ do
    uts1 <- utsFromDisjs (length $ dsjDisjuncts dj1) _ut1
    uts2 <- utsFromDisjs (length $ dsjDisjuncts dj2) _ut2
    let
      defIdxes1 = dsjDefIndexes dj1
      defIdxes2 = dsjDefIndexes dj2

    if fstDir == L
      -- uts1 & uts2 generates a m x n matrix.
      then do
        matrix <- mapM (\ut1 -> mapM (\ut2 -> unifyBinUTrees ut1 ut2 unifyTC) uts2) uts1
        treeFromMatrix (defIdxes1, defIdxes2) (length uts1, length uts2) matrix
      -- uts2 & uts1 generates a n x m matrix.
      else do
        matrix <- mapM (\ut2 -> mapM (\ut1 -> unifyBinUTrees ut2 ut1 unifyTC) uts1) uts2
        treeFromMatrix (defIdxes2, defIdxes1) (length uts2, length uts1) matrix

utsFromDisjs :: (Env r s m) => Int -> UTree -> m [UTree]
utsFromDisjs n ut@(UTree{utTC = tc}) = do
  mapM
    ( \i -> do
        djTC <- goDownTCSegMust (DisjRegTASeg i) tc
        return $ ut{utTC = djTC}
    )
    [0 .. (n - 1)]

treeFromMatrix :: (Env r s m) => ([Int], [Int]) -> (Int, Int) -> [[Maybe Tree]] -> m (Maybe Tree)
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
        return $ Just $ mkDisjTree $ emptyDisj{dsjDefIndexes = defIndexes, dsjDisjuncts = disjuncts}
    )
    (sequence disjunctsM)
