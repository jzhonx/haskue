{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Unification where

import Control.Monad (foldM, forM, when)
import Control.Monad.Except (modifyError)
import Control.Monad.Reader (asks, local)
import Cursor
import Data.Aeson (ToJSON (..), toJSON)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, isNothing, listToMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import Feature
import {-# SOURCE #-} Reduce.Core (reduce, reducePureVN, reduceToNonMut)
import Reduce.Monad (
  Error (..),
  RM,
  allocRMObjID,
  createCnstr,
  getTMAbsAddr,
  getTMCursor,
  getTMVal,
  inRemoteTM,
  inSubTM,
  liftEitherRM,
  mapParams,
  params,
  setTMVN,
  supersedeTMVN,
  throwFatal,
  unwrapTMVN,
  withNoRecalcFlag,
 )
import Reduce.TraceSpan (
  debugInstantRM,
  traceSpanAdaptRM,
  traceSpanArgsRMTC,
  traceSpanRMTC,
  traceSpanTM,
 )
import StringIndex (ShowWTIndexer (..), TextIndex, ToJSONWTIndexer (..))
import qualified Syntax.AST as AST
import Text.Printf (printf)
import Value
import Value.Export.Debug (treeToRepString)

{- | Discover conjuncts from a **unreduced** tree node that contains conjuncts as its children.

It reduces every conjunct node it finds.

It should not be directly called.
-}
partialReduceUnifyOp :: RM ResolvedPConjuncts
partialReduceUnifyOp = traceSpanTM "partialReduceUnifyOp" $ do
  t <- getTMVal
  case t of
    IsRegularUnifyOp sop _ -> go sop
    IsEmbedUnifyOp sop _ -> go sop
    _ -> throwFatal "partialReduceUnifyOp: focus is not a unify operation"
 where
  go sop = do
    conjAddrs <-
      foldM
        ( \acc (f, _) -> do
            subs <- inSubTM f discoverConjs
            return (acc ++ subs)
        )
        []
        (toList $ getSOpArgs sop)
    -- In the beginning, set the accumulating tree node to no value.
    -- TODO: remove deps
    setTMVN VNNoVal
    -- Get the original constraint node.
    cnstr <- getTMVal

    (aconjM, foundNoVal) <-
      foldM
        ( \(aconjM, foundNoVal) addr -> do
            (r, hasNoVal) <- inRemoteTM addr $ do
              vc <- getTMCursor
              case focus vc of
                -- Comprehensions conjuncts are delayed to be reduced until all other conjuncts are reduced.
                -- Comprehensions may have NoVal as their value.
                IsCompreh _ _ -> return (vc, False)
                _ -> do
                  reduceToNonMut
                  conjVC <- getTMCursor
                  return (conjVC, isNothing $ rtrVal (focus conjVC))
            if hasNoVal
              then return (aconjM, True)
              else do
                acc <- getTMCursor
                case focus acc of
                  -- The accumulating tree is NoVal, so we just set the tree node to the reduced conjunct.
                  IsNoVal -> do
                    debugInstantRM
                      "partialReduceUnifyOp"
                      ( const $
                          return $
                            printf
                              "setting accumulating conjunct to reduced conjunct %s"
                              (show $ valNode $ focus r)
                      )
                      acc
                    setTMVN (valNode $ focus r)
                  -- The accumulating tree is not NoVal, so we need to unify it with the reduced conjunct.
                  _ -> do
                    res <- unifyTCs [acc, r] acc
                    setTMVN (valNode res)
                return (rtrAtom r.focus, foundNoVal)
        )
        (Nothing, False)
        conjAddrs

    createCnstr <- asks (createCnstr . params)
    case (aconjM, foundNoVal) of
      -- If there is at least one atom conjunct and there are incomplete conjuncts, we create an atom constraint
      -- conjunction.
      (Just a, True) | createCnstr -> return $ AtomCnstrConj $ AtomCnstr a cnstr
      (_, True) -> do
        setTMVN VNNoVal
        return IncompleteConjuncts
      _ -> CompletelyResolved <$> getTMVal

  -- Discover conjuncts and preprocess them.
  discoverConjs = do
    conjTC <- getTMCursor
    case focus conjTC of
      IsRegularUnifyOp sop _ ->
        -- A conjunct can be incomplete. For example, 1 & (x + 1) resulting an atom constraint.
        foldM
          ( \acc (f, _) -> do
              subs <- inSubTM f discoverConjs
              return (acc ++ subs)
          )
          []
          (toList $ getSOpArgs sop)
      -- We do not discover conjuncts that are part of an embed unify op because they should be treated as a whole.
      _ -> do
        addr <- getTMAbsAddr
        return [addr]

data ResolvedPConjuncts
  = -- | AtomCnstrConj is created if one of the pending conjuncts is an atom and the runtime parameter
    -- 'createCnstr' is True.
    AtomCnstrConj AtomCnstr
  | CompletelyResolved Val
  | IncompleteConjuncts
  deriving (Show)

instance ToJSON ResolvedPConjuncts where
  toJSON (AtomCnstrConj _) = toJSON ("AtomCnstrConj" :: String)
  toJSON (CompletelyResolved _) = toJSON ("CompletelyResolved" :: String)
  toJSON IncompleteConjuncts = toJSON ("IncompleteConjuncts" :: String)

instance ToJSONWTIndexer ResolvedPConjuncts where
  ttoJSON = return . toJSON

data EmbedType
  = ETNone
  | ETEnclosing
  | ETEmbedded
  deriving (Eq, Show)

-- | UTree is a tree with a direction.
data UTree = UTree
  { dir :: BinOpDirect
  , utTC :: VCur
  -- ^ This tree cursor of the conjunct.
  , embType :: EmbedType
  }

instance Show UTree where
  show (UTree d vc emb) =
    printf
      "(dir: %s, addr: %s, focus: %s:, embedded: %s)"
      (show d)
      (show $ vcAddr vc)
      (show $ focus vc)
      (show emb)

instance ShowWTIndexer UTree where
  tshow (UTree d vc emb) = do
    a <- tshow (vcAddr vc)
    t <- tshow (focus vc)
    return $
      T.pack $
        printf
          "(dir: %s, addr: %s, focus: %s, embedded: %s)"
          (show d)
          a
          t
          (show emb)

-- | Check if the first tree is embedded in the second tree.
isEmbeddedIn :: UTree -> UTree -> Bool
isEmbeddedIn ut1 ut2 = case (ut1.embType, ut2.embType) of
  (ETEmbedded, ETEnclosing) -> True
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

isVCurEmbedUnify :: VCur -> Bool
isVCurEmbedUnify vc = case focus vc of
  IsEmbedUnifyOp _ _ -> True
  _ -> False

data ConjState = ConjState
  { revNormConjs :: [VCur]
  , revFixConjs :: [FixConj]
  }

emptyConjState :: ConjState
emptyConjState =
  ConjState
    { revNormConjs = []
    , revFixConjs = []
    }

{- | Unify a list of tree cursors into one tree.

Unification is always done in a pre-order manner.

It handles the following cases:
1. If all trees are structurally cyclic, return a bottom tree.
2. Reference cycle.
3. Make all regular trees immutable because mutables should not be involved in unification in general.

If RC can not be cancelled, then the result is Nothing.

The order of the unification is the same as the order of the trees.
-}
unifyTCs :: [VCur] -> VCur -> RM Val
unifyTCs tcs unifyTC = traceSpanRMTC "unifyTCs" unifyTC $ do
  when (length tcs < 2) $ throwFatal "not enough arguments for unification"

  debugInstantRM "unifyTCs" (const $ return $ printf "normalized: %s" (show tcs)) unifyTC
  s <-
    foldM
      ( \acc vc -> do
          let
            t = focus vc
            immutTC = setValImmutable t `setVCFocus` vc
          case t of
            IsFix r ->
              return $
                acc
                  { revNormConjs = mkNewVal r.val `setVCFocus` vc : acc.revNormConjs
                  , revFixConjs = r.conjs ++ acc.revFixConjs
                  }
            IsCompreh _ _ -> return $ acc{revFixConjs = FixCompreh (vcAddr vc) : acc.revFixConjs}
            -- NoVal must be put last since comprehensions may contain NoVal.
            IsNoVal -> throwFatal "unifyTCs: NoVal found in conjuncts"
            _ -> return $ acc{revNormConjs = immutTC : acc.revNormConjs}
      )
      emptyConjState
      tcs
  let norms = reverse s.revNormConjs
      fconjs = reverse s.revFixConjs
  if null norms
    then
      if null fconjs
        then throwFatal "no trees to unify"
        else return $ mkNewVal VNTop
    else do
      r <- mergeTCs norms unifyTC
      if null fconjs
        then return r
        else do
          let f = mkNewVal $ VNFix (Fix (valNode r) fconjs True)
          debugInstantRM
            "unifyTCs"
            ( const $ do
                fStr <- treeToRepString f
                return $ printf "Fix: %s" fStr
            )
            unifyTC
          return f

{- | Unify two UTrees that are discovered in the merging process.

The new conjuncts are not necessarily ready.

The order of the operands is preserved.
-}
unifyForNewBinConjs :: UTree -> UTree -> VCur -> RM (Maybe Val)
unifyForNewBinConjs ut1@(UTree{dir = L}) ut2 vc = unifyForNewConjs [ut1, ut2] vc
unifyForNewBinConjs ut1@(UTree{dir = R}) ut2 vc = unifyForNewConjs [ut2, ut1] vc

unifyForNewConjs :: [UTree] -> VCur -> RM (Maybe Val)
unifyForNewConjs uts vc = do
  let xs =
        map
          ( \x ->
              let y = utTC x
               in case rtrVal (focus y) of
                    Just v -> Just (v `setVCFocus` y)
                    Nothing -> Nothing
          )
          uts
  case sequence xs of
    Just ys -> Just <$> unifyTCs ys vc
    Nothing -> return Nothing

-- | Merge a list of processed tree cursors into one tree.
mergeTCs :: [VCur] -> VCur -> RM Val
mergeTCs tcs unifyTC = do
  let isEmbedUnify = isVCurEmbedUnify unifyTC
  traceSpanArgsRMTC
    (printf "mergeTCs %s" (if isEmbedUnify then "embed" :: String else ""))
    ( const $ do
        tcsStr <- mapM tshow tcs
        return $ show tcsStr
    )
    unifyTC
    $ do
      when (null tcs) $ throwFatal "not enough arguments"
      let
        headTC = head tcs
        accEmbedType = if isEmbedUnify then ETEnclosing else ETNone
        conjEmbedType = if isEmbedUnify then ETEmbedded else ETNone
      r <-
        foldM
          ( \acc vc -> do
              r <-
                mergeBinUTrees
                  (acc{dir = L})
                  (UTree{dir = R, utTC = vc, embType = conjEmbedType})
                  unifyTC
              return $ acc{utTC = r `setVCFocus` acc.utTC}
          )
          (UTree{dir = L, utTC = headTC, embType = accEmbedType})
          (tail tcs)
      return $ focus (utTC r)

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
mergeBinUTrees :: UTree -> UTree -> VCur -> RM Val
mergeBinUTrees ut1@(UTree{utTC = tc1}) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t1 = focus tc1
      t2 = focus tc2

  r <- traceSpanArgsRMTC
    "mergeBinUTrees"
    ( const $ do
        t1Str <- treeToRepString t1
        t2Str <- treeToRepString t2
        return $
          printf
            "merging\n%s:\n%s\nwith\n%s:\n%s"
            (show $ dir ut1)
            t1Str
            (show $ dir ut2)
            t2Str
    )
    unifyTC
    $ do
      -- Each case should handle embedded case where the left value is embedded and the right value is a struct.
      -- The embedded case skips the merging of the embedded value with the struct and just embeds the left value.
      r <- case (valNode t1, valNode t2) of
        (VNBottom _, _) -> return t1
        (_, VNBottom _) -> return t2
        (VNTop, _) -> mergeLeftTop ut1 ut2 unifyTC
        (_, VNTop) -> mergeLeftTop ut2 ut1 unifyTC
        (VNAtom a1, _) -> mergeLeftAtom (a1, ut1) ut2 unifyTC
        (_, VNAtom a2) -> mergeLeftAtom (a2, ut2) ut1 unifyTC
        (VNDisj dj1, _) -> mergeLeftDisj (dj1, ut1) ut2 unifyTC
        (_, VNDisj dj2) -> mergeLeftDisj (dj2, ut2) ut1 unifyTC
        (VNBounds b1, _) -> mergeLeftBound (b1, ut1) ut2 unifyTC
        (_, VNBounds b2) -> mergeLeftBound (b2, ut2) ut1 unifyTC
        (VNStruct es1, _) -> mergeLeftStruct (es1, ut1) ut2 unifyTC
        (_, VNStruct es2) -> mergeLeftStruct (es2, ut2) ut1 unifyTC
        _ -> mergeLeftOther ut1 ut2 unifyTC

      -- close the merged tree
      return (r{isRecurClosed = isRecurClosed t1 || isRecurClosed t2})

  debugInstantRM
    "mergeBinUTrees"
    ( const $ do
        rStr <- treeToRepString r
        return $ printf "result: %s" rStr
    )
    unifyTC
  return r

mergeLeftTop :: UTree -> UTree -> VCur -> RM Val
mergeLeftTop ut1 ut2 unifyTC = do
  let t2 = focus (utTC ut2)
  case t2 of
    IsStruct s2 | ut1 `isEmbeddedIn` ut2 -> mergeLeftStruct (s2, ut2) ut1 unifyTC
    _ -> return t2

mergeLeftAtom :: (Atom, UTree) -> UTree -> VCur -> RM Val
mergeLeftAtom (v1, ut1@(UTree{dir = d1})) ut2@(UTree{utTC = tc2, dir = d2}) unifyTC =
  traceSpanRMTC "mergeLeftAtom" unifyTC $ do
    let t2 = focus tc2
    case (v1, t2) of
      (String x, IsAtom s)
        | String y <- s -> rtn $ if x == y then VNAtom v1 else amismatch x y
      (Int x, IsAtom s)
        | Int y <- s -> rtn $ if x == y then VNAtom v1 else amismatch x y
      (Float x, IsAtom s)
        | Float y <- s -> rtn $ if x == y then VNAtom v1 else amismatch x y
      (Bool x, IsAtom s)
        | Bool y <- s -> rtn $ if x == y then VNAtom v1 else amismatch x y
      (Null, IsAtom s) | Null <- s -> rtn $ VNAtom v1
      (_, IsBounds b) -> return $ mergeAtomBounds (d1, v1) (d2, bdsList b)
      (_, IsAtomCnstr c) ->
        if v1 == c.value
          then return t2
          else return $ mkBottomVal $ printf "values mismatch: %s != %s" (show v1) (show c.value)
      (_, IsDisj dj2) -> mergeLeftDisj (dj2, ut2) ut1 unifyTC
      (_, IsValMutable mut2)
        -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
        -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
        -- marked disjunction.
        | (Op (DisjOp _)) <- mut2 -> mergeLeftOther ut2 ut1 unifyTC
        | otherwise -> mergeLeftOther ut2 ut1 unifyTC
      (_, IsStruct s2) -> mergeLeftStruct (s2, ut2) ut1 unifyTC
      _ -> mergeLeftOther ut1 ut2 unifyTC
 where
  rtn :: ValNode -> RM Val
  rtn = return . mkNewVal

  amismatch :: (Show a) => a -> a -> ValNode
  amismatch x y = VNBottom . Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

mergeLeftBound :: (Bounds, UTree) -> UTree -> VCur -> RM Val
mergeLeftBound (b1, ut1@(UTree{dir = d1})) ut2@(UTree{utTC = tc2, dir = d2}) unifyTC = do
  let t2 = focus tc2
  case valNode t2 of
    VNAtom ta2 -> do
      return $ mergeAtomBounds (d2, ta2) (d1, bdsList b1)
    VNBounds b2 -> do
      let res = mergeBoundList (d1, bdsList b1) (d2, bdsList b2)
      case res of
        Left err -> return (mkBottomVal err)
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
              Just a -> return (mkAtomVal a)
              Nothing -> return (mkBoundsValFromList (fst r))
    VNStruct s2 -> mergeLeftStruct (s2, ut2) ut1 unifyTC
    _ -> mergeLeftOther ut2 ut1 unifyTC

mergeAtomBounds :: (BinOpDirect, Atom) -> (BinOpDirect, [Bound]) -> Val
mergeAtomBounds (d1, a1) (d2, bs) =
  -- try to find the atom in the bounds list.
  foldl1 findAtom (map withBound bs)
 where
  ta1 = mkAtomVal a1

  findAtom acc x = if acc == ta1 || x == ta1 then acc else x

  withBound :: Bound -> Val
  withBound b =
    let
      r = mergeBounds (d1, BdIsAtom a1) (d2, b)
     in
      case r of
        Left s -> mkBottomVal s
        Right v -> case v of
          [x] -> case x of
            BdIsAtom a -> mkAtomVal a
            _ -> mkBottomVal $ printf "unexpected bounds unification result: %s" (show x)
          _ -> mkBottomVal $ printf "unexpected bounds unification result: %s" (show v)

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
mergeLeftOther :: UTree -> UTree -> VCur -> RM Val
mergeLeftOther ut1@(UTree{utTC = tc1}) ut2 unifyTC = do
  let t1 = focus tc1
  case t1 of
    IsFix{} -> throwFatal "Fix should not be used in merge"
    IsValMutable (SOp _ _) -> do
      tStr <- treeToRepString t1
      throwFatal $ printf "op %s should not be used in merge" tStr
    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    IsAtomCnstr c1 -> do
      na <- unifyForNewBinConjs (ut1{utTC = mkNewVal (VNAtom c1.value) `setVCFocus` tc1}) ut2 unifyTC
      -- Because the ut2 has been guaranteed to be a concrete tree cursor and the ut1 is an atom, so there must be a
      -- result.
      case valNode (fromJust na) of
        VNBottom _ -> return (fromJust na)
        _ -> return t1
    _ -> returnNotUnifiable ut1 ut2

returnNotUnifiable :: UTree -> UTree -> RM Val
returnNotUnifiable (UTree{utTC = tc1, dir = d1}) (UTree{utTC = tc2}) = do
  let t1 = focus tc1
      t2 = focus tc2
  case d1 of
    L -> f t1 t2
    R -> f t2 t1
 where
  f x y = do
    tx <- modifyError FatalErr $ showValueType x
    ty <- modifyError FatalErr $ showValueType y
    return $ mkBottomVal $ printf "%s can not be unified with %s" tx ty

mergeLeftStruct :: (Struct, UTree) -> UTree -> VCur -> RM Val
mergeLeftStruct (s1, ut1) ut2 unifyTC
  -- If the left struct is an empty struct with a non-struct embedded value, e.g. {embedded_val}.
  -- we merge the embedded value with the right value.
  | hasEmptyFields s1 = case stcEmbedVal s1 of
      Just ev -> do
        r <- unifyForNewBinConjs ut1{utTC = setVCFocus ev ut1.utTC} ut2 unifyTC
        case r of
          Just t -> return t
          Nothing -> return $ mkNewVal VNNoVal
      -- This is the case for {embedding} -> {} & embedding, where we try to evaluate a struct with an embedded value.
      Nothing | ut2 `isEmbeddedIn` ut1 -> case focus ut2.utTC of
        -- An embedded value can not be a struct, so we merge the embedded struct with its parent struct.
        IsStruct s2 -> mergeStructs (s1, ut1) (s2, ut2) unifyTC
        _ -> return $ mkStructVal s1{stcEmbedVal = Just (focus ut2.utTC)}
      -- This is the case for {} & val.
      Nothing
        | IsTop <- focus ut2.utTC -> return $ mkStructVal s1
        | IsStruct s2 <- focus ut2.utTC -> mergeStructs (s1, ut1) (s2, ut2) unifyTC
        | otherwise -> mergeLeftOther ut1 ut2 unifyTC
-- The left struct is a struct without embedded values {f:fv}.
mergeLeftStruct (s1, ut1) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t2 = focus tc2
  case t2 of
    -- If the right value is top, return the left struct. This covers two cases:
    -- 1. {f: fv, _} -> {f: fv} & _ , where _ is an embedded top.
    -- 2. {f: fv} & _
    IsTop -> return $ mkStructVal s1
    IsStruct s2 -> mergeStructs (s1, ut1) (s2, ut2) unifyTC
    _
      -- This handles the case where the right value is embedded in the left struct and the right value is not a
      -- struct. For example, {c: int, x} -> {c: int} & x.
      | ut2 `isEmbeddedIn` ut1 -> case t2 of
          IsDisj dj2 -> mergeDisjWithVal (dj2, ut2) ut1 unifyTC
          _ -> mergeLeftOther ut2 ut1 unifyTC
      | otherwise -> mergeLeftOther ut2 ut1 unifyTC

{- | unify two structs.

The s1 is made the left struct, and s2 is made the right struct.

For closedness, unification only generates a closed struct but not a recursively closed struct since to close a struct
recursively, the only way is to reference the struct via a #ident.
-}
mergeStructs :: (Struct, UTree) -> (Struct, UTree) -> VCur -> RM Val
mergeStructs (s1, ut1@UTree{dir = L}) (s2, ut2) unifyTC = do
  traceSpanArgsRMTC
    "mergeStructs"
    ( const $ do
        ut1Str <- tshow ut1
        ut2Str <- tshow ut2
        return $ printf "ut1: %s\nut2: %s" ut1Str ut2Str
    )
    unifyTC
    $ do
      let
        neitherEmbedded = not (ut1 `isEmbeddedIn` ut2 || ut2 `isEmbeddedIn` ut1)
      -- Consider: {a: _, s1|s2} -> {a: _} & s1

      let
        tc1 = utTC ut1
        tc2 = utTC ut2
      case (tc1.focus, tc2.focus) of
        (IsStruct rs1, IsStruct rs2) -> do
          newID <-
            if
              | ut1 `isEmbeddedIn` ut2 -> return (stcID s2)
              | ut2 `isEmbeddedIn` ut1 -> return (stcID s1)
              | otherwise -> allocRMObjID

          let s = mergeStructsInner rs1 rs2 neitherEmbedded
          return $ mkStructVal s{stcID = newID}
        _ ->
          throwFatal $
            printf
              "structs expected after preparation, got %s and %s"
              (showValSymbol tc1.focus)
              (showValSymbol tc2.focus)
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
    , stcBindings = Map.union (stcBindings st1) (stcBindings st2)
    }

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
      { ssfValue = mkMutableVal unifyValOp
      , ssfAttr = mergeAttrs (ssfAttr sf1) (ssfAttr sf2)
      , ssfObjects = ssfObjects sf1 `Set.union` ssfObjects sf2
      }

{- | Extended version of all sub nodes of the tree, including patterns, dynamic fields and let bindings.

If a node is a mutable node, we do not return its tree node sub nodes, instead, return the sub nodes of the mutable.
This is because the sub nodes of the tree node is not reduced and will be rewritten by the mutable.
-}
mergeLeftDisj :: (Disj, UTree) -> UTree -> VCur -> RM Val
mergeLeftDisj (dj1, ut1) ut2@(UTree{utTC = tc2}) unifyTC = do
  let t2 = focus tc2
  case valNode t2 of
    VNAtomCnstr _ -> mergeLeftOther ut2 ut1 unifyTC
    -- TODO:
    VNFix{} -> mergeLeftOther ut2 ut1 unifyTC
    VNDisj dj2 -> mergeDisjWithDisj (dj1, ut1) (dj2, ut2) unifyTC
    -- If the disjunction is an embedded value of a struct.
    VNStruct s2 | ut1 `isEmbeddedIn` ut2 -> mergeLeftStruct (s2, ut2) ut1 unifyTC
    -- this is the case for a disjunction unified with a value.
    _ -> mergeDisjWithVal (dj1, ut1) ut2 unifyTC

-- Note: embType is still required. Think about the following values,
-- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
-- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
-- In current CUE's implementation, CUE puts the fields of the single value first.
mergeDisjWithVal :: (Disj, UTree) -> UTree -> VCur -> RM Val
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
mergeDisjWithDisj :: (Disj, UTree) -> (Disj, UTree) -> VCur -> RM Val
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
utsFromDisjs n ut@(UTree{utTC = vc}) = do
  mapM
    ( \i -> do
        djTC <- liftEitherRM (goDownVCSegMust (mkDisjFeature i) vc)
        -- make disjucnt inherit the embedded property of the disjunction.
        -- return $ ut{utTC = modifyVCFocus (\t -> t{Value.embType = ut.embType}) djTC}
        return $ ut{utTC = djTC}
    )
    [0 .. (n - 1)]

treeFromMatrix :: ([Int], [Int]) -> (Int, Int) -> [[Maybe Val]] -> RM Val
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
  return $ mkDisjVal $ emptyDisj{dsjDefIndexes = newDefIndexes, dsjDisjuncts = newDisjuncts}

-- | TODO: efficient implementation
removeIncompleteDisjuncts :: [Int] -> [Maybe Val] -> ([Int], [Val])
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
patMatchLabel :: Val -> TextIndex -> VCur -> RM Bool
patMatchLabel pat tidx vc = traceSpanAdaptRM "patMatchLabel" (return . toJSON) vc $ do
  -- Retrieve the atom or bounds from the pattern.
  let vM = listToMaybe $ catMaybes [rtrAtom pat >>= Just . mkAtomVal, rtrBounds pat >>= Just . mkBoundsVal]
  maybe (return False) match vM
 where
  match :: Val -> RM Bool
  match v = do
    name <- tshow tidx
    let f =
          mergeBinUTrees
            (UTree L (v `setVCFocus` vc) ETNone)
            (UTree R (mkAtomVal (String name) `setVCFocus` vc) ETNone)
            vc
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

reduceFix :: Fix -> RM ()
reduceFix f = traceSpanTM "reduceFix" $ do
  -- Because withRCs only has one inner structure, which will have the dependency addresses as its wrapper, we
  -- can just put the inner structure first.
  supersedeTMVN f.val

  -- Calculate a temporary result first.
  reducePureVN
  -- In the intermediate steps of resolving RCs, we do not want to trigger recalculation of functions.
  unknownExists <- withNoRecalcFlag True $ runFix 0 f.conjs
  if not unknownExists
    -- reduce the sub fields again so that dependents of the sub fields of the inner value can be notified.
    -- The value of the top of the tree will not be used to notify dependents here. Because this function should be called
    -- inside a reduce. At the end of the outer reduce, the dependents of the top of the tree will be notified.
    -- TODO: optimize this step to avoid redundant reduce by recursively notifying the dependents of the fields.
    -- If there is no RCs left, no need to keep the wrapper. Make the inner value the top of the tree.
    then reducePureVN
    else unwrapTMVN (\x -> VNFix (Fix (valNode x) f.conjs unknownExists))

{- | Find the fixed point of unifying normal conjuncts and reference cycles.

During the function call, the top of the tree will be updated to the temporary result of unifying normal
conjuncts. After the function call, the tree will be updated to the reduced result.

Unify operators are normal conjuncts, reference cycles and references to sub-fields in reference cycles.
The algorithm is as follows:
1. Calculate a temporary result for normal_conjs, which is r
2. Loop to resolve the RC_subs
   - Fetch the sub value from the result
   - If the sub value is new, meaning it is not an instance of the result, unify it with the result. r' = r & r.f.
   - Terminate when no new sub values can be fetched.

Proof of why fetching sub-fields from r is correct:

let fval = r.f,

1. If r.f is a struct with {f: dsub}, the fetched sub can modify the field f in the final result by having fval' =
fval & dsub. Then we do fetch again and get fval & dsub. The value will be unified with f field again, but it is
(fval & dsub) & (fval & dsub), which is the same as fval & dsub.
2. If sub is a struct but without sub field f, then r.f is unknown.
3. If sub is not a struct, then r.f is unknown.
-}
runFix :: Int -> [FixConj] -> RM Bool
runFix count conjs = do
  (more, unknownExists) <- traceSpanTM (printf "runFix %d" count) $ do
    prevT <- getTMVal
    unifyTC <- getTMCursor
    -- find known RCs from the v
    let unifyAddr = vcAddr unifyTC
    (newConjTCs, unknownExists) <-
      foldM
        ( \(accNewConjs, accUE) conj -> case conj of
            FixSelect rcAddr ->
              if rcAddr == unifyAddr
                -- If the address is the same as the unifyTC, which means the RC refers to itself, we can skip it.
                then return (accNewConjs, accUE)
                else
                  let rest = trimPrefixAddr unifyAddr rcAddr
                      subTCM = goDownVCAddr rest unifyTC
                   in case subTCM of
                        Just subTC -> return (subTC : accNewConjs, accUE)
                        -- The sub value is not found, we treat it as unknown.
                        Nothing -> return (accNewConjs, True)
            FixCompreh ct -> inRemoteTM ct $ do
              reduce
              rtc <- getTMCursor
              case focus rtc of
                IsNoVal -> return (accNewConjs, True)
                _ -> return (rtc : accNewConjs, accUE)
        )
        ([], False)
        conjs

    newConjsStr <- mapM tshow newConjTCs
    debugInstantRM
      "runFix"
      ( const $ do
          tStr <- tshow prevT
          return $
            printf
              "resolving Fix, prev result: %s, newConjsStr: %s, unknownExists: %s"
              tStr
              (show newConjsStr)
              (show unknownExists)
      )
      unifyTC

    r <-
      if null newConjTCs
        then return $ Just $ focus unifyTC
        else Just <$> mergeTCs (unifyTC : newConjTCs) unifyTC
    setTMVN (valNode $ fromJust r)
    reducePureVN
    t <- getTMVal
    if t == prevT
      -- We have reached a fixed point.
      then return (False, unknownExists)
      -- Only update the tree node. Other parts should remain the same.
      else do
        debugInstantRM
          "runFix"
          ( const $ do
              prevTRep <- treeToRepString prevT
              newTRep <- treeToRepString t
              return $ printf "Fix iteration updated tree from: %s\nto:\n%s" prevTRep newTRep
          )
          unifyTC
        return (True, unknownExists)

  if more
    then runFix (count + 1) conjs
    else return unknownExists