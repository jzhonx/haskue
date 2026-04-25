{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Reduce.Unification where

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM, when)
import Control.Monad.Reader (asks, local)
import Cursor (getSubValByAddr)
import Data.Aeson (ToJSON (..), toJSON)
import qualified Data.ByteString.Char8 as BC
import qualified Data.DList as DList
import qualified Data.IntMap.Strict as IntMap
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, listToMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import Feature
import {-# SOURCE #-} Reduce.Core (forceReduceMut, reduce, reducePureVN)
import Reduce.Monad (
  RM,
  allocRMObjID,
  createCnstr,
  mapParams,
  params,
  throwFatal,
  withNoSignalReduced,
 )
import Reduce.Store (storeAllSubVals)
import Reduce.TraceSpan (
  debugInstStr,
  emptySpanValue,
  traceSpanAdaptTM,
  traceSpanArgsTM,
  traceSpanTM,
  valDebugRepJSON,
 )
import StringIndex (ShowWTIndexer (..), TextIndex, ToJSONWTIndexer (..), textIndexToBS)
import qualified Syntax.AST as AST
import Text.Printf (printf)
import Value
import Value.Export.Debug (valToRepString)

{- | Discover conjuncts from a **unreduced** tree node that contains conjuncts as its children.

It reduces every conjunct node it finds.
-}
partialReduceUnifyOp :: UnifyOp -> ValAddr -> Val -> RM (UnifyOp, ResolvedPConjuncts)
partialReduceUnifyOp uop addr v = traceSpanAdaptTM
  "partialReduceUnifyOp"
  addr
  (valDebugRepJSON addr v)
  ( \(a, b) -> do
      let r = mkMutableVal (withEmptyOpFrame (UOp a))
      rT <- tshow r
      bJ <- ttoJSON b
      return $ toJSON (rT, bJ)
  )
  $ do
    -- If the unification is an embed unification, we save the first struct conjunct as our knowledge base.
    -- Other conjuncts that reference fields in the struct then can be reduced.
    case uop.conjs of
      a Seq.:<| _ | uop.isEmbedUnify -> storeAllSubVals addr a
      _ -> return ()
    upduop <- reduceRegConjs uop addr
    res <- mergeRegConjs upduop addr
    createCnstr <- asks (createCnstr . params)
    return
      ( upduop
      , case (res.atomFound, res.foundNoValConj) of
          -- If there is at least one atom conjunct and there are incomplete conjuncts, we create an atom constraint
          -- conjunction.
          (Just a, True)
            | createCnstr -> AtomCnstrConj $ setVN (VNAtomCnstr $ AtomCnstr a v) res.conj
          (_, True) -> IncompleteConjuncts
          _ -> CompletelyResolved res.conj
      )

-- | Reduce the conjuncts in the pre-order manner.
reduceRegConjs :: UnifyOp -> ValAddr -> RM UnifyOp
reduceRegConjs uop topAddr = vtmapM reduceRegConjsRecur topAddr uop
 where
  reduceRegConjsRecur :: ValAddr -> Val -> RM Val
  reduceRegConjsRecur addr v
    | IsRegularUnifyOp sop _ <- v = do
        updsop <- vtmapM reduceRegConjsRecur addr sop
        return $ setTOp updsop v
    | IsCompreh _ _ <- v = return v
    | otherwise = forceReduceMut False addr v

data ConjReduceResult = ConjReduceResult
  { conj :: Val
  , conjAddr :: ValAddr
  , atomFound :: Maybe Atom
  , foundNoValConj :: Bool
  }

emptyConjReduceResult :: ConjReduceResult
emptyConjReduceResult =
  ConjReduceResult
    { conj = mkNewVal VNNoVal
    , conjAddr = emptyValAddr
    , atomFound = Nothing
    , foundNoValConj = False
    }

mergeRegConjs :: UnifyOp -> ValAddr -> RM ConjReduceResult
mergeRegConjs uop topAddr = do
  xs <- sequence (vtmapQ mergeRegConjsRecur topAddr uop)
  foldM mergeConjResults emptyConjReduceResult xs
 where
  mergeRegConjsRecur :: ValAddr -> Val -> RM ConjReduceResult
  mergeRegConjsRecur addr v = do
    let r = emptyConjReduceResult{conj = v, conjAddr = addr}
    case v of
      IsRegularUnifyOp sop _ -> do
        xs <- sequence (vtmapQ mergeRegConjsRecur addr sop)
        foldM mergeConjResults emptyConjReduceResult xs
      -- Comprehension might have NoVal as its value, but it is not considered as an incomplete conjunct since it can be
      -- further reduced.
      IsCompreh _ _ -> return r
      IsNoVal -> return $ r{foundNoValConj = True}
      IsAtom a -> return $ r{atomFound = Just a, foundNoValConj = False}
      _ -> return r

  mergeConjResults :: ConjReduceResult -> ConjReduceResult -> RM ConjReduceResult
  mergeConjResults acc x
    | x.foundNoValConj = return acc{foundNoValConj = True}
    -- The iter value is not a NoVal while the acc is still a NoVal
    | IsNoVal <- acc.conj = return acc{conj = x.conj, atomFound = fetchAtom x.conj}
    | otherwise = do
        -- The unification happens at the top level, so we use the topAddr for unification.
        r <- unifyVals [(topAddr, acc.conj), (x.conjAddr, x.conj)] topAddr uop.isEmbedUnify
        return acc{conj = r, atomFound = fetchAtom r <|> acc.atomFound}

  fetchAtom (IsAtom a) = Just a
  fetchAtom _ = Nothing

data ResolvedPConjuncts
  = -- | AtomCnstrConj is created if one of the pending conjuncts is an atom and the runtime parameter
    -- 'createCnstr' is True.
    AtomCnstrConj Val
  | CompletelyResolved Val
  | IncompleteConjuncts
  deriving (Show)

instance ToJSON ResolvedPConjuncts where
  toJSON (AtomCnstrConj _) = toJSON ("AtomCnstrConj" :: String)
  toJSON (CompletelyResolved _) = toJSON ("CompletelyResolved" :: String)
  toJSON IncompleteConjuncts = toJSON ("IncompleteConjuncts" :: String)

instance ToJSONWTIndexer ResolvedPConjuncts where
  ttoJSON (AtomCnstrConj v) = do
    vT <- tshow v
    return $ toJSON ("AtomCnstrConj: " <> vT)
  ttoJSON (CompletelyResolved v) = do
    vT <- tshow v
    return $ toJSON ("CompletelyResolved: " <> vT)
  ttoJSON IncompleteConjuncts = return $ toJSON ("IncompleteConjuncts" :: String)

data EmbedType
  = ETNone
  | ETEnclosing
  | ETEmbedded
  deriving (Eq, Show)

-- | ConjOpd is a tree with a direction.
data ConjOpd = ConjOpd
  { dir :: BinOpDirect
  , coVal :: Val
  -- ^ This tree cursor of the conjunct.
  , coAddr :: ValAddr
  , embType :: EmbedType
  }

instance Show ConjOpd where
  show (ConjOpd d v a emb) =
    printf
      "(dir: %s, addr: %s, focus: %s:, embedded: %s)"
      (show d)
      (show a)
      (show v)
      (show emb)

instance ShowWTIndexer ConjOpd where
  tshow (ConjOpd d v a emb) = do
    ta <- tshow a
    t <- tshow v
    return $
      T.pack $
        printf
          "(dir: %s, addr: %s, focus: %s, embedded: %s)"
          (show d)
          ta
          t
          (show emb)

-- | Check if the first tree is embedded in the second tree.
isEmbeddedIn :: ConjOpd -> ConjOpd -> Bool
isEmbeddedIn co1 co2 = case (co1.embType, co2.embType) of
  (ETEmbedded, ETEnclosing) -> True
  _ -> False

showUTreeList :: [ConjOpd] -> String
showUTreeList [] = "[]"
showUTreeList (x : xs) =
  show x
    <> "\n"
    <> foldl
      ( \acc y -> acc <> show y <> "\n"
      )
      ""
      xs

isVCurEmbedUnify :: Val -> Bool
isVCurEmbedUnify v = case v of
  IsEmbedUnifyOp _ _ -> True
  _ -> False

data ConjState = ConjState
  { revNormConjs :: [(ValAddr, Val)]
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
unifyVals :: [(ValAddr, Val)] -> ValAddr -> Bool -> RM Val
unifyVals ps addr isEmbedUnify = traceSpanTM "unifyVals" addr emptySpanValue $ do
  when (length ps < 2) $ throwFatal "not enough arguments for unification"
  debugInstStr
    "unifyVals"
    addr
    ( const $ do
        psT <-
          mapM
            ( \(a, b) -> do
                aT <- tshow a
                bT <- tshow b
                return (aT, bT)
            )
            ps
        return $ printf "normalized: %s" (show psT)
    )
  s <-
    foldM
      ( \acc (p, v) -> case v of
          IsFix r ->
            return $
              acc
                { revNormConjs = (p, mkNewVal r.val) : acc.revNormConjs
                , revFixConjs = r.conjs ++ acc.revFixConjs
                }
          IsCompreh _ _ -> return $ acc{revFixConjs = FixCompreh p v : acc.revFixConjs}
          -- NoVal must be put last since comprehensions may contain NoVal.
          IsNoVal -> throwFatal "unifyVals: NoVal found in conjuncts"
          _ -> return $ acc{revNormConjs = (p, setValImmutable v) : acc.revNormConjs}
      )
      emptyConjState
      ps
  let norms = reverse s.revNormConjs
      fconjs = reverse s.revFixConjs
  if null norms
    then
      if null fconjs
        then throwFatal "no trees to unify"
        else return $ mkNewVal VNTop
    else do
      r <- mergeVals norms addr isEmbedUnify
      if null fconjs
        then return r
        else do
          let f = mkNewVal $ VNFix (Fix (valNode r) fconjs True)
          debugInstStr
            "unifyVals"
            addr
            ( const $ do
                fStr <- valToRepString f
                return $ printf "Fix: %s" fStr
            )
          return f

{- | Unify two UTrees that are discovered in the merging process.

The new conjuncts are not necessarily ready.

The order of the operands is preserved.
-}
unifyConjOpds :: ConjOpd -> ConjOpd -> ValAddr -> RM (Maybe Val)
unifyConjOpds co1@(ConjOpd{dir = L}) co2 = unifyOrderedConjOpds co1 co2
unifyConjOpds co1@(ConjOpd{dir = R}) co2 = unifyOrderedConjOpds co2 co1

unifyOrderedConjOpds :: ConjOpd -> ConjOpd -> ValAddr -> RM (Maybe Val)
unifyOrderedConjOpds co1 co2 addr = do
  let xs = do
        v1 <- rtrVal co1.coVal
        v2 <- rtrVal co2.coVal
        return [(co1.coAddr, v1), (co2.coAddr, v2)]
  case xs of
    Just ys -> Just <$> unifyVals ys addr (isEmbeddedIn co2 co1)
    Nothing -> return Nothing

-- | Merge a list of processed tree cursors into one tree.
mergeVals :: [(ValAddr, Val)] -> ValAddr -> Bool -> RM Val
mergeVals tcs addr isEmbedUnify = do
  traceSpanArgsTM
    (printf "mergeVals %s" (if isEmbedUnify then "embed" :: String else ""))
    addr
    emptySpanValue
    ( const $ do
        tcsStr <- mapM tshow tcs
        return $ show tcsStr
    )
    $ do
      when (null tcs) $ throwFatal "not enough arguments"
      let
        headTC = head tcs
        accEmbedType = if isEmbedUnify then ETEnclosing else ETNone
        conjEmbedType = if isEmbedUnify then ETEmbedded else ETNone
      r <-
        foldM
          ( \acc (p, v) -> do
              r <-
                mergeBinUTrees
                  (acc{dir = L})
                  (ConjOpd{dir = R, coVal = v, embType = conjEmbedType, coAddr = p})
                  addr
              return $ acc{coVal = r}
          )
          (ConjOpd{dir = L, coVal = snd headTC, embType = accEmbedType, coAddr = addr})
          (tail tcs)
      return (coVal r)

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
mergeBinUTrees :: ConjOpd -> ConjOpd -> ValAddr -> RM Val
mergeBinUTrees co1@(ConjOpd{coVal = t1}) co2@(ConjOpd{coVal = t2}) addr = do
  r <- traceSpanArgsTM
    "mergeBinUTrees"
    addr
    emptySpanValue
    ( const $ do
        t1Str <- valToRepString t1
        t2Str <- valToRepString t2
        return $
          printf
            "merging\n%s:\n%s\nwith\n%s:\n%s"
            (show $ dir co1)
            t1Str
            (show $ dir co2)
            t2Str
    )
    $ do
      -- Each case should handle embedded case where the left value is embedded and the right value is a struct.
      -- The embedded case skips the merging of the embedded value with the struct and just embeds the left value.
      r <- case (valNode t1, valNode t2) of
        (VNBottom _, _) -> return t1
        (_, VNBottom _) -> return t2
        (VNTop, _) -> mergeLeftTop co1 co2 addr
        (_, VNTop) -> mergeLeftTop co2 co1 addr
        (VNAtom a1, _) -> mergeLeftAtom (a1, co1) co2 addr
        (_, VNAtom a2) -> mergeLeftAtom (a2, co2) co1 addr
        (VNDisj dj1, _) -> mergeLeftDisj (dj1, co1) co2 addr
        (_, VNDisj dj2) -> mergeLeftDisj (dj2, co2) co1 addr
        (VNBounds b1, _) -> mergeLeftBound (b1, co1) co2 addr
        (_, VNBounds b2) -> mergeLeftBound (b2, co2) co1 addr
        (VNStruct es1, _) -> mergeLeftStruct (es1, co1) co2 addr
        (_, VNStruct es2) -> mergeLeftStruct (es2, co2) co1 addr
        _ -> mergeLeftOther co1 co2 addr

      -- close the merged tree
      return (r{isRecurClosed = isRecurClosed t1 || isRecurClosed t2})

  debugInstStr
    "mergeBinUTrees"
    addr
    ( const $ do
        rStr <- valToRepString r
        return $ printf "result: %s" rStr
    )
  return r

mergeLeftTop :: ConjOpd -> ConjOpd -> ValAddr -> RM Val
mergeLeftTop co1 co2 addr = do
  let t2 = coVal co2
  case t2 of
    IsStruct s2 | co1 `isEmbeddedIn` co2 -> mergeLeftStruct (s2, co2) co1 addr
    _ -> return t2

mergeLeftAtom :: (Atom, ConjOpd) -> ConjOpd -> ValAddr -> RM Val
mergeLeftAtom (v1, co1@(ConjOpd{dir = d1})) co2@(ConjOpd{coVal = t2, dir = d2}) addr =
  traceSpanTM "mergeLeftAtom" addr emptySpanValue $ do
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
      (_, IsDisj dj2) -> mergeLeftDisj (dj2, co2) co1 addr
      (_, IsValMutable mut2)
        -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
        -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
        -- marked disjunction.
        | (Op (DisjOp _)) <- mut2 -> mergeLeftOther co2 co1 addr
        | otherwise -> mergeLeftOther co2 co1 addr
      (_, IsStruct s2) -> mergeLeftStruct (s2, co2) co1 addr
      _ -> mergeLeftOther co1 co2 addr
 where
  rtn :: ValNode -> RM Val
  rtn = return . mkNewVal

  amismatch :: (Show a) => a -> a -> ValNode
  amismatch x y = VNBottom . Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

mergeLeftBound :: (Bounds, ConjOpd) -> ConjOpd -> ValAddr -> RM Val
mergeLeftBound (b1, co1@(ConjOpd{dir = d1})) co2@(ConjOpd{coVal = t2, dir = d2}) addr = do
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
    VNStruct s2 -> mergeLeftStruct (s2, co2) co1 addr
    _ -> mergeLeftOther co2 co1 addr

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
reMatch :: BC.ByteString -> BC.ByteString -> Bool
reMatch = (==)

-- TODO: regex implementation
-- Second argument is the pattern.
reNotMatch :: BC.ByteString -> BC.ByteString -> Bool
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
mergeLeftOther :: ConjOpd -> ConjOpd -> ValAddr -> RM Val
mergeLeftOther co1@(ConjOpd{coVal = t1}) co2 addr = do
  case t1 of
    IsFix{} -> throwFatal "Fix should not be used in merge"
    IsValMutable (SOp _ _) -> do
      tStr <- valToRepString t1
      throwFatal $ printf "op %s should not be used in merge" tStr
    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    IsAtomCnstr c1 -> do
      na <- mergeBinUTrees (co1{coVal = mkNewVal (VNAtom c1.value)}) co2 addr
      case valNode na of
        VNBottom _ -> return na
        _ -> return t1
    _ -> returnNotUnifiable co1 co2

returnNotUnifiable :: ConjOpd -> ConjOpd -> RM Val
returnNotUnifiable (ConjOpd{coVal = t1, dir = d1}) (ConjOpd{coVal = t2}) = do
  case d1 of
    L -> f t1 t2
    R -> f t2 t1
 where
  f x y = do
    tx <- showValueType x
    ty <- showValueType y
    return $ mkBottomVal $ printf "%s can not be unified with %s" tx ty

mergeLeftStruct :: (Struct, ConjOpd) -> ConjOpd -> ValAddr -> RM Val
mergeLeftStruct (s1, co1) co2 addr
  -- If the left struct is an empty struct with a non-struct embedded value, e.g. {embedded_val}.
  -- we merge the embedded value with the right value.
  | hasEmptyFields s1 = case stcEmbedVal s1 of
      Just ev -> mergeBinUTrees co1{coVal = ev} co2 addr
      -- This is the case for {embedding} -> {} & embedding, where we try to evaluate a struct with an embedded value.
      Nothing | co2 `isEmbeddedIn` co1 -> case co2.coVal of
        -- An embedded value can not be a struct, so we merge the embedded struct with its parent struct.
        IsStruct s2 -> mergeStructs (s1, co1) (s2, co2) addr
        _ -> return $ mkStructVal s1{stcEmbedVal = Just co2.coVal}
      -- This is the case for {} & val.
      Nothing
        | IsTop <- co2.coVal -> return $ mkStructVal s1
        | IsStruct s2 <- co2.coVal -> mergeStructs (s1, co1) (s2, co2) addr
        | otherwise -> mergeLeftOther co1 co2 addr
-- The left struct is a struct without embedded values {f:fv}.
mergeLeftStruct (s1, co1) co2@(ConjOpd{coVal = t2}) addr = do
  case t2 of
    -- If the right value is top, return the left struct. This covers two cases:
    -- 1. {f: fv, _} -> {f: fv} & _ , where _ is an embedded top.
    -- 2. {f: fv} & _
    IsTop -> return $ mkStructVal s1
    IsStruct s2 -> mergeStructs (s1, co1) (s2, co2) addr
    _
      -- This handles the case where the right value is embedded in the left struct and the right value is not a
      -- struct. For example, {c: int, x} -> {c: int} & x.
      | co2 `isEmbeddedIn` co1 -> case t2 of
          IsDisj dj2 -> mergeDisjWithVal (dj2, co2) co1 addr
          _ -> mergeLeftOther co2 co1 addr
      | otherwise -> mergeLeftOther co2 co1 addr

{- | unify two structs.

The s1 is made the left struct, and s2 is made the right struct.

For closedness, unification only generates a closed struct but not a recursively closed struct since to close a struct
recursively, the only way is to reference the struct via a #ident.
-}
mergeStructs :: (Struct, ConjOpd) -> (Struct, ConjOpd) -> ValAddr -> RM Val
mergeStructs (s1, co1@ConjOpd{dir = L}) (s2, co2) addr = do
  traceSpanArgsTM
    "mergeStructs"
    addr
    emptySpanValue
    ( const $ do
        ut1Str <- tshow co1
        ut2Str <- tshow co2
        return $ printf "co1: %s\nut2: %s" ut1Str ut2Str
    )
    $ do
      let
        neitherEmbedded = not (co1 `isEmbeddedIn` co2 || co2 `isEmbeddedIn` co1)
      -- Consider: {a: _, s1|s2} -> {a: _} & s1

      let
        tc1 = coVal co1
        tc2 = coVal co2
      case (tc1, tc2) of
        (IsStruct rs1, IsStruct rs2) -> do
          newID <-
            if
              | co1 `isEmbeddedIn` co2 -> return (stcID s2)
              | co2 `isEmbeddedIn` co1 -> return (stcID s1)
              | otherwise -> allocRMObjID

          let s = mergeStructsInner rs1 rs2 neitherEmbedded
          return $ mkStructVal s{stcID = newID}
        _ ->
          throwFatal $
            printf
              "structs expected after preparation, got %s and %s"
              (showValType tc1)
              (showValType tc2)
mergeStructs dt1@(_, ConjOpd{dir = R}) dt2 addr = mergeStructs dt2 dt1 addr

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
    , piLabels = Set.fromList $ DList.toList $ stcOrdLabels st
    , piOpLabels = Set.fromList $ DList.toList $ stcOrdLabels opSt
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
unionLabels :: Struct -> Struct -> DList.DList StructFieldLabel
unionLabels s1 s2 =
  stcOrdLabels s1
    `DList.append` foldr
      ( \l acc -> case l of
          StructStaticFieldLabel fl -> if fl `Set.member` l1Set then acc else l `DList.cons` acc
          StructDynFieldOID _ -> l `DList.cons` acc
      )
      DList.empty
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
mergeLeftDisj :: (Disj, ConjOpd) -> ConjOpd -> ValAddr -> RM Val
mergeLeftDisj (dj1, co1) co2@(ConjOpd{coVal = t2}) addr = do
  case valNode t2 of
    VNAtomCnstr _ -> mergeLeftOther co2 co1 addr
    -- TODO:
    VNFix{} -> mergeLeftOther co2 co1 addr
    VNDisj dj2 -> mergeDisjWithDisj (dj1, co1) (dj2, co2) addr
    -- If the disjunction is an embedded value of a struct.
    VNStruct s2 | co1 `isEmbeddedIn` co2 -> mergeLeftStruct (s2, co2) co1 addr
    -- this is the case for a disjunction unified with a value.
    _ -> mergeDisjWithVal (dj1, co1) co2 addr

-- Note: embType is still required. Think about the following values,
-- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
-- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
-- In current CUE's implementation, CUE puts the fields of the single value first.
mergeDisjWithVal :: (Disj, ConjOpd) -> ConjOpd -> ValAddr -> RM Val
mergeDisjWithVal (dj1, _ut1@(ConjOpd{dir = fstDir})) _ut2 addr = traceSpanTM "mergeDisjWithVal" addr emptySpanValue $ do
  let
    uts1 = utsFromDisjs _ut1 dj1
    defIdxes1 = dsjDefIndexes dj1
  if fstDir == L
    -- uts1 & co2 generates a m x 1 matrix.
    then do
      matrix <- mapM (\co1 -> unifyConjOpds co1 _ut2 addr) uts1
      treeFromMatrix (defIdxes1, []) (length uts1, 1) [matrix]
    -- co2 & uts1 generates a 1 x m matrix.
    else do
      matrix <- mapM (\co1 -> unifyConjOpds co1 _ut2 addr) uts1
      treeFromMatrix ([], defIdxes1) (1, length uts1) (map (: []) matrix)

{- | Unify two disjuncts.

We do not need to compute the unification of default values since they are already unified in the disjuncts. We just
need to pick the correct indexes of the default values from the matrix.

Some rules for unifying disjuncts:

U0: ⟨v1⟩ & ⟨v2⟩         => ⟨v1&v2⟩
U1: ⟨v1, d1⟩ & ⟨v2⟩     => ⟨v1&v2, d1&v2⟩
U2: ⟨v1, d1⟩ & ⟨v2, d2⟩ => ⟨v1&v2, d1&d2⟩
-}
mergeDisjWithDisj :: (Disj, ConjOpd) -> (Disj, ConjOpd) -> ValAddr -> RM Val
mergeDisjWithDisj (dj1, _ut1@(ConjOpd{dir = fstDir})) (dj2, _ut2) addr =
  traceSpanTM "mergeDisjWithDisj" addr emptySpanValue $ do
    let
      uts1 = utsFromDisjs _ut1 dj1
      uts2 = utsFromDisjs _ut2 dj2
      defIdxes1 = dsjDefIndexes dj1
      defIdxes2 = dsjDefIndexes dj2

    if fstDir == L
      -- uts1 & uts2 generates a m x n matrix.
      then do
        matrix <- mapM (\co1 -> mapM (\co2 -> unifyConjOpds co1 co2 addr) uts2) uts1
        treeFromMatrix (defIdxes1, defIdxes2) (length uts1, length uts2) matrix
      -- uts2 & uts1 generates a n x m matrix.
      else do
        matrix <- mapM (\co2 -> mapM (\co1 -> unifyConjOpds co2 co1 addr) uts1) uts2
        treeFromMatrix (defIdxes2, defIdxes1) (length uts2, length uts1) matrix

utsFromDisjs :: ConjOpd -> Disj -> [ConjOpd]
utsFromDisjs co = vtmapQ (\p v -> co{coVal = v, coAddr = p}) co.coAddr

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
  return $ mkDisjVal $ emptyDisj{dsjDefIndexes = newDefIndexes, dsjDisjuncts = Seq.fromList newDisjuncts}

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
patMatchLabel :: Val -> TextIndex -> ValAddr -> RM Bool
patMatchLabel pat tidx addr = traceSpanAdaptTM "patMatchLabel" addr emptySpanValue (return . toJSON) $ do
  -- Retrieve the atom or bounds from the pattern.
  let vM = listToMaybe $ catMaybes [rtrAtom pat >>= Just . mkAtomVal, rtrBounds pat >>= Just . mkBoundsVal]
  maybe (return False) match vM
 where
  match :: Val -> RM Bool
  match v = do
    name <- textIndexToBS tidx
    let f =
          mergeBinUTrees
            (ConjOpd{dir = L, coVal = v, coAddr = addr, embType = ETNone})
            (ConjOpd{dir = R, coVal = mkAtomVal (String name), coAddr = addr, embType = ETNone})
            addr
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

reduceFix :: Fix -> ValAddr -> Val -> RM Val
reduceFix f addr v = traceSpanTM "reduceFix" addr (valDebugRepJSON addr v) $ do
  -- Calculate a temporary result first.
  tmpv <- reducePureVN addr (setVN f.val v)
  -- In the intermediate steps of resolving RCs, we do not want to trigger recalculation of functions.
  (r, unknownExists) <- withNoSignalReduced True $ runFix 0 f.conjs addr tmpv
  if not unknownExists
    -- reduce the sub fields again so that dependents of the sub fields of the inner value can be notified.
    -- The value of the top of the tree will not be used to notify dependents here. Because this function should be called
    -- inside a reduce. At the end of the outer reduce, the dependents of the top of the tree will be notified.
    -- TODO: optimize this step to avoid redundant reduce by recursively notifying the dependents of the fields.
    -- If there is no RCs left, no need to keep the wrapper. Make the inner value the top of the tree.
    then reducePureVN addr r
    else return r{valNode = VNFix (Fix{val = valNode r, conjs = f.conjs, unknownExists = unknownExists})}

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
runFix :: Int -> [FixConj] -> ValAddr -> Val -> RM (Val, Bool)
runFix count conjs addr prevV = do
  (r, more, unknownExists) <- traceSpanAdaptTM
    (printf "runFix %d" count)
    addr
    (valDebugRepJSON addr prevV)
    (\(r, _, _) -> valDebugRepJSON addr r)
    $ do
      (newConjTCs, unknownExists) <-
        foldM
          ( \(accNewConjs, accUE) conj -> case conj of
              FixSelect rcAddr ->
                if rcAddr == addr
                  -- If the address is the same as the unifyTC, which means the RC refers to itself, we can skip it.
                  then return (accNewConjs, accUE)
                  else
                    let rest = trimPrefixAddr addr rcAddr
                        rM = getSubValByAddr rest prevV
                     in case rM of
                          Just r -> return (r : accNewConjs, accUE)
                          -- The sub value is not found, we treat it as unknown.
                          Nothing -> return (accNewConjs, True)
              FixCompreh cphAddr cphv -> do
                r <- reduce cphAddr cphv
                case r of
                  IsNoVal -> return (accNewConjs, True)
                  _ -> return (r : accNewConjs, accUE)
          )
          ([], False)
          conjs

      newConjsStr <- mapM tshow newConjTCs
      debugInstStr
        "runFix"
        addr
        ( const $ do
            tStr <- tshow prevV
            return $
              printf
                "resolving Fix, prev result: %s, newConjsStr: %s, unknownExists: %s"
                tStr
                (show newConjsStr)
                (show unknownExists)
        )

      r <-
        ( if null newConjTCs
            then return prevV
            else mergeVals (map (addr,) (prevV : newConjTCs)) addr False
          )
          >>= reducePureVN addr
      if r == prevV
        -- We have reached a fixed point.
        then return (r, False, unknownExists)
        -- Only update the tree node. Other parts should remain the same.
        else do
          debugInstStr
            "runFix"
            addr
            ( const $ do
                prevTRep <- valToRepString prevV
                newTRep <- valToRepString r
                return $ printf "Fix iteration updated tree from: %s\nto:\n%s" prevTRep newTRep
            )
          return (r, True, unknownExists)

  if more
    then runFix (count + 1) conjs addr r
    else return (r, unknownExists)