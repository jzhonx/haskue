{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.UnifyOp where

import qualified AST
import Control.Monad (foldM, forM, when)
import Control.Monad.Except (modifyError)
import Control.Monad.Reader (local)
import Cursor
import Data.Aeson (object, toJSON)
import qualified Data.IntMap.Strict as IntMap
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, isJust, listToMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import Feature
import Reduce.RMonad (
  Error (..),
  RM,
  allocRMObjID,
  createCnstr,
  debugInstantRM,
  liftEitherRM,
  mapParams,
  preVisitTree,
  preVisitTreeSimple,
  throwFatal,
  traceSpanAdaptRM,
  traceSpanArgsRMTC,
  traceSpanRMTC,
 )
import Reduce.RefSys (IdentType (..), searchTCIdent)
import StringIndex (ShowWTIndexer (..), TextIndex, TextIndexerMonad, ToJSONWTIndexer (ttoJSON))
import Text.Printf (printf)
import Value
import Value.Util.TreeRep (treeToRepString)

-- | UTree is a tree with a direction.
data UTree = UTree
  { dir :: BinOpDirect
  , utTC :: TrCur
  -- ^ This tree cursor of the conjunct.
  -- , isLatest :: !Bool
  -- ^ Whether the tree cursor is the latest version due to merging with other conjuncts. This is used in preparing
  -- struct, so that structs can see the latest version of other conjuncts.
  , embType :: EmbedType
  }

instance Show UTree where
  show (UTree d tc emb) =
    printf
      "(dir: %s, addr: %s, focus: %s:, embedded: %s)"
      (show d)
      (show $ tcAddr tc)
      (show $ tcFocus tc)
      (show emb)

-- | Check if the first tree is embedded in the second tree.
isEmbeddedOf :: UTree -> UTree -> Bool
isEmbeddedOf ut1 ut2 = case (ut1.embType, ut2.utTC) of
  (ETEmbedded sid1, TCFocus (IsStruct struct)) -> sid1 == struct.stcID
  _ -> False

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

{- | Unify a list of non-noval trees that are ready.

Unification is always done in a pre-order manner.

It handles the following cases:
1. If all trees are structurally cyclic, return a bottom tree.
2. Reference cycle.
3. Make all regular trees immutable because blocks or mutables should not be involved in unification in general.

If RC can not be cancelled, then the result is Nothing.

The order of the unification is the same as the order of the trees.
-}
unifyNormalizedTCs :: [TrCur] -> TrCur -> RM (Maybe Tree)
unifyNormalizedTCs tcs unifyTC = traceSpanAdaptRM
  "unifyNormalizedTCs"
  ( \a -> case a of
      Nothing -> return $ object []
      Just t -> treeToRepString t >>= return . toJSON
  )
  unifyTC
  $ do
    when (length tcs < 2) $ throwFatal "not enough arguments for unification"

    let isAllCyclic = all (isSCyclic . tcFocus) tcs
    if isAllCyclic
      then return $ Just $ mkBottomTree "structural cycle"
      else do
        debugInstantRM "unifyNormalizedTCs" (printf "normalized: %s" (show tcs)) unifyTC
        let (regs, rcs) =
              foldr
                ( \tc (accRegs, accRCs) ->
                    let
                      t = tcFocus tc
                      immutTC = makeTreeImmutable t `setTCFocus` tc
                     in
                      case t of
                        IsRefCycle -> (accRegs, accRCs + 1)
                        IsUnifiedWithRC True -> (immutTC : accRegs, accRCs + 1)
                        _ -> (immutTC : accRegs, accRCs)
                )
                ([], 0 :: Int)
                tcs

        if
          | null regs, rcs == 0 -> throwFatal "no trees to unify"
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
                else return $ Just $ r{isUnifiedWithRC = True}

{- | Check if the reference cycle can be cancelled.

A reference cycle can be cancelled if
* in the form of f: RC & v
-}
canCancelRC :: TrCur -> Bool
canCancelRC unifyTC = isJust $ addrIsRfbAddr (tcAddr unifyTC)

{- | Unify two UTrees that are discovered in the merging process.

The new conjuncts are not necessarily ready.

The order of the operands is preserved.
-}
unifyForNewBinConjs :: UTree -> UTree -> TrCur -> RM (Maybe Tree)
unifyForNewBinConjs ut1@(UTree{dir = L}) ut2 tc = unifyForNewConjs [ut1, ut2] tc
unifyForNewBinConjs ut1@(UTree{dir = R}) ut2 tc = unifyForNewConjs [ut2, ut1] tc

unifyForNewConjs :: [UTree] -> TrCur -> RM (Maybe Tree)
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

mergeTCs :: [TrCur] -> TrCur -> RM Tree
mergeTCs tcs unifyTC = traceSpanArgsRMTC "mergeTCs" (showTCList tcs) unifyTC $ do
  when (null tcs) $ throwFatal "not enough arguments"
  let headTC = head tcs
  -- TODO: does the first tree need to be not embedded?
  r <-
    foldM
      ( \acc tc -> do
          r <-
            mergeBinUTrees
              (acc{dir = L})
              (UTree{dir = R, utTC = tc, embType = (tcFocus tc).embType})
              unifyTC
          return $ acc{utTC = r `setTCFocus` acc.utTC}
      )
      (UTree{dir = L, utTC = headTC, embType = headTC.tcFocus.embType})
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
mergeBinUTrees :: UTree -> UTree -> TrCur -> RM Tree
mergeBinUTrees ut1@(UTree{utTC = tc1}) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t1 = tcFocus tc1
      t2 = tcFocus tc2

  t1Str <- tshow t1
  t2Str <- tshow t2
  traceSpanArgsRMTC
    "mergeBinUTrees"
    ( printf
        ("merging %s, %s" ++ "\n" ++ "with %s, %s")
        (show $ dir ut1)
        t1Str
        (show $ dir ut2)
        t2Str
    )
    unifyTC
    $ do
      -- Each case should handle embedded case where the left value is embedded and the right value is a struct.
      -- The embedded case skips the merging of the embedded value with the struct and just embeds the left value.
      r <- case (treeNode t1, treeNode t2) of
        (TNBottom _, _) -> return t1
        (_, TNBottom _) -> return t2
        (TNTop, _) -> mergeLeftTop ut1 ut2 unifyTC
        (_, TNTop) -> mergeLeftTop ut2 ut1 unifyTC
        (TNAtom a1, _) -> mergeLeftAtom (a1, ut1) ut2 unifyTC
        (_, TNAtom a2) -> mergeLeftAtom (a2, ut2) ut1 unifyTC
        (TNDisj dj1, _) -> mergeLeftDisj (dj1, ut1) ut2 unifyTC
        (_, TNDisj dj2) -> mergeLeftDisj (dj2, ut2) ut1 unifyTC
        (TNBounds b1, _) -> mergeLeftBound (b1, ut1) ut2 unifyTC
        (_, TNBounds b2) -> mergeLeftBound (b2, ut2) ut1 unifyTC
        (TNStruct es1, _) -> mergeLeftStruct (es1, ut1) ut2 unifyTC
        (_, TNStruct es2) -> mergeLeftStruct (es2, ut2) ut1 unifyTC
        _ -> mergeLeftOther ut1 ut2 unifyTC

      -- close the merged tree
      return (r{isRecurClosed = isRecurClosed t1 || isRecurClosed t2})

mergeLeftTop :: UTree -> UTree -> TrCur -> RM Tree
mergeLeftTop ut1 ut2 unifyTC = do
  let t2 = tcFocus (utTC ut2)
  case t2 of
    IsStruct s2 | ut1 `isEmbeddedOf` ut2 -> mergeLeftStruct (s2, ut2) ut1 unifyTC
    _ -> return t2

mergeLeftAtom :: (Atom, UTree) -> UTree -> TrCur -> RM Tree
mergeLeftAtom (v1, ut1@(UTree{dir = d1})) ut2@(UTree{utTC = tc2, dir = d2}) unifyTC =
  traceSpanRMTC "mergeLeftAtom" unifyTC $ do
    let t2 = tcFocus tc2
    case (v1, t2) of
      (String x, IsAtom s)
        | String y <- s -> rtn $ if x == y then TNAtom v1 else amismatch x y
      (Int x, IsAtom s)
        | Int y <- s -> rtn $ if x == y then TNAtom v1 else amismatch x y
      (Float x, IsAtom s)
        | Float y <- s -> rtn $ if x == y then TNAtom v1 else amismatch x y
      (Bool x, IsAtom s)
        | Bool y <- s -> rtn $ if x == y then TNAtom v1 else amismatch x y
      (Null, IsAtom s) | Null <- s -> rtn $ TNAtom v1
      (_, IsBounds b) -> return $ mergeAtomBounds (d1, v1) (d2, bdsList b)
      (_, IsAtomCnstr c) ->
        if v1 == c.value
          then return t2
          else return $ mkBottomTree $ printf "values mismatch: %s != %s" (show v1) (show c.value)
      (_, IsDisj dj2) -> mergeLeftDisj (dj2, ut2) ut1 unifyTC
      (_, IsTGenOp mut2)
        -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
        -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
        -- marked disjunction.
        | (MutOp (DisjOp _)) <- mut2 -> mergeLeftOther ut2 ut1 unifyTC
        | otherwise -> mergeLeftOther ut2 ut1 unifyTC
      (_, IsStruct s2) -> mergeLeftStruct (s2, ut2) ut1 unifyTC
      _ -> mergeLeftOther ut1 ut2 unifyTC
 where
  rtn :: TreeNode -> RM Tree
  rtn = return . mkNewTree

  amismatch :: (Show a) => a -> a -> TreeNode
  amismatch x y = TNBottom . Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

mergeLeftBound :: (Bounds, UTree) -> UTree -> TrCur -> RM Tree
mergeLeftBound (b1, ut1@(UTree{dir = d1})) ut2@(UTree{utTC = tc2, dir = d2}) unifyTC = do
  let t2 = tcFocus tc2
  case treeNode t2 of
    TNAtom ta2 -> do
      return $ mergeAtomBounds (d2, ta2) (d1, bdsList b1)
    TNBounds b2 -> do
      let res = mergeBoundList (d1, bdsList b1) (d2, bdsList b2)
      case res of
        Left err -> return (mkBottomTree err)
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
              Just a -> return (mkAtomTree a)
              Nothing -> return (mkBoundsTreeFromList (fst r))
    TNStruct s2 -> mergeLeftStruct (s2, ut2) ut1 unifyTC
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
mergeLeftOther :: UTree -> UTree -> TrCur -> RM Tree
mergeLeftOther ut1@(UTree{utTC = tc1}) ut2 unifyTC = do
  let t1 = tcFocus tc1
  case t1 of
    IsRefCycle -> throwFatal "ref cycle should not be used in merge"
    IsTGenOp (Mutable mop _) -> throwFatal $ printf "mutable op %s should not be used in merge" (show mop)
    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    IsAtomCnstr c1 -> do
      na <- unifyForNewBinConjs (ut1{utTC = mkNewTree (TNAtom c1.value) `setTCFocus` tc1}) ut2 unifyTC
      -- Because the ut2 has been guaranteed to be a concrete tree cursor and the ut1 is an atom, so there must be a
      -- result.
      case treeNode (fromJust na) of
        TNBottom _ -> return (fromJust na)
        _ -> return t1
    _ -> returnNotUnifiable ut1 ut2

returnNotUnifiable :: UTree -> UTree -> RM Tree
returnNotUnifiable (UTree{utTC = tc1, dir = d1}) (UTree{utTC = tc2}) = do
  let t1 = tcFocus tc1
      t2 = tcFocus tc2
  case d1 of
    L -> f t1 t2
    R -> f t2 t1
 where
  f x y = do
    tx <- modifyError FatalErr $ showValueType x
    ty <- modifyError FatalErr $ showValueType y
    return $ mkBottomTree $ printf "%s can not be unified with %s" tx ty

mergeLeftStruct :: (Struct, UTree) -> UTree -> TrCur -> RM Tree
mergeLeftStruct (s1, ut1) ut2 unifyTC
  -- If the left struct is an empty struct with an embedded value, we merge the embedded value with the right value.
  | hasEmptyFields s1
  , Just ev <- stcEmbedVal s1 = do
      r <- unifyForNewBinConjs ut1{utTC = setTCFocus ev ut1.utTC} ut2 unifyTC
      case r of
        Just t -> return t
        Nothing -> return $ mkNewTree TNNoVal
-- The left struct is a struct without an embedded value. The struct can be empty or non-empty.
mergeLeftStruct (s1, ut1) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t2 = tcFocus tc2
  case t2 of
    -- Even if s2 is embedded, we still merge the two structs because some of the hidden fields may be in conflict.
    IsStruct s2 -> mergeStructs (s1, ut1) (s2, ut2) unifyTC
    _
      -- This handles the case where the right value is embedded, but not a struct.
      | ut2 `isEmbeddedOf` ut1 ->
          if hasEmptyFields s1
            then return $ mkStructTree $ s1{stcEmbedVal = Just t2}
            -- Left struct is a non-empty struct. We make the right value non-embedded. For example, {#OneOf, c: int} ->
            -- {c: int} & #OnfOf.
            else case t2 of
              IsDisj dj2 -> mergeDisjWithVal (dj2, ut2) ut1 unifyTC
              _ -> mergeLeftOther ut2 ut1 unifyTC
      | otherwise -> mergeLeftOther ut2 ut1 unifyTC

{- | unify two structs.

The s1 is made the left struct, and s2 is made the right struct.

For closedness, unification only generates a closed struct but not a recursively closed struct since to close a struct
recursively, the only way is to reference the struct via a #ident.
-}
mergeStructs :: (Struct, UTree) -> (Struct, UTree) -> TrCur -> RM Tree
mergeStructs (s1, ut1@UTree{dir = L}) (s2, ut2) unifyTC = traceSpanArgsRMTC
  "mergeStructs"
  (printf "ut1: %s\nut2: %s" (show ut1) (show ut2))
  unifyTC
  $ do
    let
      neitherEmbedded = not (ut1 `isEmbeddedOf` ut2 || ut2 `isEmbeddedOf` ut1)
    -- Consider: {a: _, s1|s2} -> {a: _} & s1
    (rtc1, rtc2) <-
      do
        let blockSufMap1 = Map.fromList $ (tcAddr ut1.utTC, stcID s1) : [(tcAddr ut2.utTC, stcID s2) | ut1 `isEmbeddedOf` ut2]
            blockSufMap2 = Map.fromList $ (tcAddr ut2.utTC, stcID s2) : [(tcAddr ut1.utTC, stcID s1) | ut2 `isEmbeddedOf` ut1]
        utc1 <- prepStruct blockSufMap1 ut1.utTC
        utc2 <- prepStruct blockSufMap2 ut2.utTC
        return (utc1, utc2)

    case (rtc1.tcFocus, rtc2.tcFocus) of
      (IsStruct rs1, IsStruct rs2) -> do
        newID <-
          if
            | ut1 `isEmbeddedOf` ut2 -> return (stcID s2)
            | ut2 `isEmbeddedOf` ut1 -> return (stcID s1)
            | otherwise -> allocRMObjID

        let s = mergeStructsInner rs1 rs2 neitherEmbedded
        renamedLets1 <- renameLets (stcID s1) (stcBindings s1)
        renamedLets2 <- renameLets (stcID s2) (stcBindings s2)
        return $
          mkStructTree
            s
              { stcID = newID
              , stcBindings = Map.union renamedLets1 renamedLets2
              }
      (IsBottom _, _) -> return rtc1.tcFocus
      (_, IsBottom _) -> return rtc2.tcFocus
      _ ->
        throwFatal $
          printf "structs expected after preparation, got %s and %s" (showTreeSymbol rtc1.tcFocus) (showTreeSymbol rtc2.tcFocus)
mergeStructs dt1@(_, UTree{dir = R}) dt2 unifyTC = mergeStructs dt2 dt1 unifyTC

mergeStructsInner :: Struct -> Struct -> Bool -> Struct
mergeStructsInner s1 s2 neitherEmbedded = do
  let merged = fieldsToStruct s1 s2
   in merged
        { stcPerms =
            stcPerms merged
              ++ [mkPermItem s1 s2 | neitherEmbedded && stcClosed s1]
              ++ [mkPermItem s2 s1 | neitherEmbedded && stcClosed s2]
        }

fieldsToStruct :: Struct -> Struct -> Struct
fieldsToStruct st1 st2 =
  emptyStruct
    { stcClosed = stcClosed st1 || stcClosed st2
    , stcFields = Map.fromList (unionFields (stcFields st1) (stcFields st2))
    , stcDynFields = IntMap.union (stcDynFields st1) (stcDynFields st2)
    , -- The combined patterns are the patterns of the first struct and the patterns of the second struct.
      stcCnstrs = IntMap.union (stcCnstrs st1) (stcCnstrs st2)
    , stcStaticFieldBases = Map.fromList (unionFields (stcStaticFieldBases st1) (stcStaticFieldBases st2))
    , stcOrdLabels = unionLabels st1 st2
    , stcPerms = stcPerms st1 ++ stcPerms st2
    }

renameLets :: (TextIndexerMonad s m) => Int -> Map.Map TextIndex Binding -> m (Map.Map TextIndex Binding)
renameLets suffix m = do
  foldM
    ( \acc (k, v) -> do
        nk <- mkLetFeature k (Just suffix)
        let nidx = getTextIndexFromFeature nk
        return $ Map.insert nidx v acc
    )
    Map.empty
    (Map.toList m)

-- Map.mapKeys
--   ( \case
--       RefIdent n -> RefIdentWithOID n suffix
--       RefIdentWithOID n old -> RefIdentWithOID n old
--   )

mkPermItem :: Struct -> Struct -> PermItem
mkPermItem st opSt =
  PermItem
    { piCnstrs = Set.fromList $ IntMap.keys $ stcCnstrs st
    , piLabels = Set.fromList $ stcOrdLabels st
    , piOpLabels = Set.fromList $ stcOrdLabels opSt
    }

{- | Merge two fields.

The structs can not be both embedded.
-}
unionFields :: Map.Map TextIndex Field -> Map.Map TextIndex Field -> [(TextIndex, Field)]
unionFields fields1 fields2 =
  foldr
    ( \label acc ->
        let
          f1M = Map.lookup label fields1
          f2M = Map.lookup label fields2
         in
          if
            | label `Set.member` l1Set && label `Set.member` l2Set
            , Just sf1 <- f1M
            , Just sf2 <- f2M ->
                (label, _mkUnifiedField sf1 sf2) : acc
            | label `Set.member` l1Set, Just sf1 <- f1M -> (label, sf1) : acc
            | label `Set.member` l2Set, Just sf2 <- f2M -> (label, sf2) : acc
            | otherwise -> acc
    )
    []
    (Set.toList $ Set.union l1Set l2Set)
 where
  l1Set = Map.keysSet fields1
  l2Set = Map.keysSet fields2

{- | Put the static field labels in the order of the first struct and append the labels that are not in the first
struct.
For dynamic fields, we just append them to the end of the list.
-}
unionLabels :: Struct -> Struct -> [StructFieldLabel]
unionLabels s1 s2 =
  stcOrdLabels s1
    ++ foldr
      ( \l acc -> case l of
          StructStaticFieldLabel fl -> if fl `Set.member` l1Set then acc else l : acc
          StructDynFieldOID _ -> l : acc
      )
      []
      (stcOrdLabels s2)
 where
  l1Set =
    foldr
      ( \l acc -> case l of
          StructStaticFieldLabel fl -> Set.insert fl acc
          StructDynFieldOID _ -> acc
      )
      Set.empty
      (stcOrdLabels s1)

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

{- | Preprocess the struct for merging.

It does the followings:
1. Invalidate references that reference static fields of the struct. This makes operations that have the reference as
   operand to be invalidated too.
2. Validate if the identifier of any reference in the sub tree is in the scope.
3. Rewrite let variables to make sure they do not conflict with other let variables in the other struct.

The reason we need to do these is because after merging two structs, we effectively create a new block that contains
new identifiers that some of the references would not have seen before merging.

According to spec, a block is a possibly empty sequence of declarations.

The scope of a declared identifier is the extent of source text in which the identifier denotes the specified field,
alias, or package.
-}
prepStruct :: Map.Map TreeAddr Int -> TrCur -> RM TrCur
prepStruct blockSufMap structTC@(TCFocus (IsStruct _)) = traceSpanAdaptRM "prepStruct" ttoJSON structTC $ do
  (updatedTC, updatedPSS) <- preVisitTree (subNodes True) firstPass (structTC, emptyPSS)
  debugInstantRM
    "prepStruct"
    (printf "blockSufMap: %s, after first pass: %s" (show blockSufMap) (show updatedPSS))
    updatedTC
  case updatedPSS.error of
    Just err -> return $ err `setTCFocus` updatedTC
    Nothing -> do
      let origAddr = tcAddr structTC
      foldM
        (\acc addr -> liftEitherRM (goTCAbsAddrMust addr acc) >>= preVisitTreeSimple (subNodes True) invalidate)
        updatedTC
        (Set.toList $ invAddrs updatedPSS)
        >>= ( \x ->
                foldM
                  (\acc (addr, suffix) -> liftEitherRM (goTCAbsAddrMust addr acc) >>= rewrite suffix)
                  x
                  (rwLetIdents updatedPSS)
            )
        >>= liftEitherRM . goTCAbsAddrMust origAddr
 where
  -- First pass records the invalidated addresses and rewrites let variables.
  -- It also records the last ident not found error it encounters.
  firstPass (tc, acc) = do
    case tc of
      TCFocus (IsRef _ (Reference{refArg = RefPath ident _})) -> do
        m <- searchTCIdent ident tc
        case m of
          -- Return the last error if there are multiple errors.
          Nothing -> do
            idStr <- tshow ident
            return
              ( tc
              , emptyPSS
                  { error =
                      Just $ mkBottomTree $ printf "identifier %s is not found" (show idStr)
                  }
              )
          Just (dstTC, typ) -> do
            let dstAddr = tcAddr dstTC
            if
              -- The ident points to a specified static field.
              | Just prefix <- initTreeAddr dstAddr
              , prefix `Map.member` blockSufMap && typ == ITField -> do
                  let newAcc =
                        acc
                          { invAddrs =
                              Set.insert
                                (sufIrredToAddr . trimAddrToSufIrred $ tcAddr tc)
                                (invAddrs acc)
                          }
                  return (tc, newAcc)
              | Just prefix <- initTreeAddr dstAddr
              , Just suffix <- prefix `Map.lookup` blockSufMap
              , typ /= ITField -> do
                  debugInstantRM
                    "prepStruct.firstPass"
                    (printf "rewriting ref %s that references a let var with suffix %d. dstAddr: %s" (show ident) suffix (show dstAddr))
                    tc
                  let newAcc = acc{rwLetIdents = (tcAddr tc, suffix) : rwLetIdents acc}
                  return (tc, newAcc)
              | otherwise -> return (tc, acc)
      _ -> return (tc, acc)

  invalidate tc = do
    let focus = tcFocus tc
    return $ case focus of
      IsTGenImmutable -> tc
      _ -> setTN focus TNNoVal `setTCFocus` tc

  rewrite suffix tc = case tc of
    TCFocus t@(IsRef mut ref@(Reference{refArg = RefPath ident xs})) -> do
      newIdentF <- mkLetFeature ident (Just suffix)
      let newIdx = getTextIndexFromFeature newIdentF
      identStr <- tshow ident
      newIdentStr <- tshow newIdentF
      debugInstantRM
        "prepStruct.rewrite"
        ( printf "rewriting ref ident %s to %s with suffix %d, newidx: %s" (show identStr) (show newIdentStr) suffix (show newIdx)
        )
        tc
      let
        newRef = ref{refArg = RefPath newIdx xs}
        newMut = setMutOp (Ref newRef) mut
      return (t{valGenEnv = TGenOp newMut} `setTCFocus` tc)
    _ -> return tc
prepStruct _ tc = do
  debugInstantRM "prepStruct" (printf "none struct focus: %s" (show tc.tcFocus)) tc
  return tc

data PrepStructState = PrepStructState
  { error :: Maybe Tree
  , invAddrs :: Set.Set TreeAddr
  , rwLetIdents :: [(TreeAddr, Int)]
  }
  deriving (Show)

emptyPSS :: PrepStructState
emptyPSS = PrepStructState{error = Nothing, invAddrs = Set.empty, rwLetIdents = []}

{- | Extended version of all sub nodes of the tree, including patterns, dynamic fields and let bindings.

If a node is a mutable node, we do not return its tree node sub nodes, instead, return the sub nodes of the mutable.
This is because the sub nodes of the tree node is not reduced and will be rewritten by the mutable.
-}
mergeLeftDisj :: (Disj, UTree) -> UTree -> TrCur -> RM Tree
mergeLeftDisj (dj1, ut1) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t2 = tcFocus tc2
  case treeNode t2 of
    TNAtomCnstr _ -> mergeLeftOther ut2 ut1 unifyTC
    TNRefCycle{} -> mergeLeftOther ut2 ut1 unifyTC
    TNDisj dj2 -> mergeDisjWithDisj (dj1, ut1) (dj2, ut2) unifyTC
    -- If the disjunction is an embedded value of a struct.
    TNStruct s2 | ut1 `isEmbeddedOf` ut2 -> mergeLeftStruct (s2, ut2) ut1 unifyTC
    -- this is the case for a disjunction unified with a value.
    _ -> mergeDisjWithVal (dj1, ut1) ut2 unifyTC

-- Note: embType is still required. Think about the following values,
-- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
-- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
-- In current CUE's implementation, CUE puts the fields of the single value first.
mergeDisjWithVal :: (Disj, UTree) -> UTree -> TrCur -> RM Tree
mergeDisjWithVal (dj1, _ut1@(UTree{dir = fstDir})) _ut2 unifyTC =
  traceSpanRMTC "mergeDisjWithVal" unifyTC $ do
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
mergeDisjWithDisj :: (Disj, UTree) -> (Disj, UTree) -> TrCur -> RM Tree
mergeDisjWithDisj (dj1, _ut1@(UTree{dir = fstDir})) (dj2, _ut2) unifyTC =
  traceSpanRMTC "mergeDisjWithDisj" unifyTC $ do
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

utsFromDisjs :: Int -> UTree -> RM [UTree]
utsFromDisjs n ut@(UTree{utTC = tc}) = do
  mapM
    ( \i -> do
        djTC <- liftEitherRM (goDownTCSegMust (mkDisjFeature i) tc)
        -- make disjucnt inherit the embedded property of the disjunction.
        return $ ut{utTC = modifyTCFocus (\t -> t{Value.embType = ut.embType}) djTC}
    )
    [0 .. (n - 1)]

treeFromMatrix :: ([Int], [Int]) -> (Int, Int) -> [[Maybe Tree]] -> RM Tree
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

{- | Returns whether the pattern matches the label.

The pattern is expected to be an Atom or a Bounds.
-}
patMatchLabel :: Tree -> TextIndex -> TrCur -> RM Bool
patMatchLabel pat tidx tc = traceSpanAdaptRM "patMatchLabel" (return . toJSON) tc $ do
  -- Retrieve the atom or bounds from the pattern.
  let vM = listToMaybe $ catMaybes [rtrAtom pat >>= Just . mkAtomTree, rtrBounds pat >>= Just . mkBoundsTree]
  maybe (return False) match vM
 where
  match :: Tree -> RM Bool
  match v = do
    name <- tshow tidx
    let f =
          mergeBinUTrees
            (UTree L (v `setTCFocus` tc) ETNone)
            (UTree R (mkAtomTree (String name) `setTCFocus` tc) ETNone)
            tc
    -- We should not create constraints in this context because we should not delay the evaluation of the
    -- pattern.
    r <-
      local
        (mapParams (\p -> p{createCnstr = False}))
        f
    -- Filter the strings from the results. Non-string results are ignored meaning the fields do not match the
    -- pattern.
    case rtrAtom r of
      Just (String _) -> return True
      _ -> return False