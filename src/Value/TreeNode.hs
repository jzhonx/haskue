{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.TreeNode where

import Common (Env, TreeOp)
import Control.Monad.Except (MonadError)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromJust, isNothing)
import Exception (throwErrSt)
import GHC.Stack (HasCallStack)
import Path (
  ComprehTASeg (..),
  StructTASeg (..),
  TASeg (
    ComprehTASeg,
    DisjDefaultTASeg,
    DisjDisjunctTASeg,
    IndexTASeg,
    MutableArgTASeg,
    ParentTASeg,
    RootTASeg,
    StructTASeg,
    SubValTASeg
  ),
  TreeAddr,
 )
import Text.Printf (printf)
import Value.Atom (AtomV)
import Value.Bottom (Bottom)
import Value.Bounds (Bounds)
import Value.Comprehension
import Value.Constraint (AtomCnstr, CnstredVal (cnsedVal))
import Value.Disj (Disj (dsjDefault, dsjDisjuncts))
import Value.DisjoinOp (DisjTerm (dstValue), DisjoinOp (djoTerms))
import Value.List (List (lstSubs))
import Value.Mutable (
  Mutable (..),
  RegularOp (ropArgs),
  getMutVal,
  setMutVal,
 )
import Value.Reference (Reference (refArg), setRefArgs, subRefArgs)
import Value.Struct (
  Block (..),
  DynamicField (..),
  Embedding (..),
  Field (ssfValue),
  LetBinding (lbValue),
  Struct (..),
  StructCnstr (..),
  lookupStructField,
  lookupStructLet,
  updateFieldValue,
  updateStructField,
  updateStructLet,
 )
import Value.UnifyOp (UnifyOp (ufConjuncts))

class HasTreeNode t where
  getTreeNode :: t -> TreeNode t
  setTreeNode :: t -> TreeNode t -> t

-- | TreeNode represents a tree structure that contains values.
data TreeNode t
  = -- | TNAtom contains an atom value.
    TNAtom AtomV
  | TNBottom Bottom
  | TNBounds Bounds
  | TNTop
  | TNBlock (Block t)
  | TNList (List t)
  | TNDisj (Disj t)
  | TNAtomCnstr (AtomCnstr t)
  | -- | TNRefCycle represents the result of a field referencing itself or its sub field.
    -- It also represents recursion, which is mostly disallowed in the CUE.
    -- If a field references itself, the address is the same as the field reference. For example: x: x.
    -- If a field references its sub field, the address is the sub field address. For example: x: x.a.
    TNRefCycle TreeAddr
  | TNMutable (Mutable t)
  | TNCnstredVal (CnstredVal t)

instance (Eq t, TreeOp t, HasTreeNode t) => Eq (TreeNode t) where
  (==) (TNBlock s1) (TNBlock s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNAtom l1) (TNAtom l2) = l1 == l2
  (==) (TNAtomCnstr c1) (TNAtomCnstr c2) = c1 == c2
  (==) (TNDisj dj1) n2@(TNAtom _) =
    if isNothing (dsjDefault dj1)
      then False
      else getTreeNode (fromJust $ dsjDefault dj1) == n2
  (==) (TNAtom a1) (TNDisj dj2) = (==) (TNDisj dj2) (TNAtom a1)
  (==) (TNMutable f1) (TNMutable f2) = f1 == f2
  (==) (TNBounds b1) (TNBounds b2) = b1 == b2
  (==) (TNCnstredVal v1) (TNCnstredVal v2) = v1 == v2
  (==) (TNBottom _) (TNBottom _) = True
  (==) TNTop TNTop = True
  (==) (TNRefCycle a1) (TNRefCycle a2) = a1 == a2
  (==) _ _ = False

{- | descend into the tree with the given segment.

This should only be used by TreeCursor.
-}
subTreeTN :: (TreeOp t, HasTreeNode t, Show t, HasCallStack) => TASeg -> t -> Maybe t
subTreeTN seg t = case (seg, getTreeNode t) of
  (RootTASeg, _) -> Just t
  (StructTASeg s, TNBlock estruct@(Block{blkStruct = struct})) -> case s of
    StringTASeg name
      | Just sf <- lookupStructField name struct -> Just $ ssfValue sf
    PatternTASeg i j -> (if j == 0 then scsPattern else scsValue) <$> stcCnstrs struct IntMap.!? i
    DynFieldTASeg i j ->
      (if j == 0 then dsfLabel else dsfValue) <$> stcDynFields struct IntMap.!? i
    LetTASeg name
      | Just lb <- Value.Struct.lookupStructLet name struct -> Just (lbValue lb)
    EmbedTASeg i -> embValue <$> blkEmbeds estruct IntMap.!? i
    _ -> Nothing
  (SubValTASeg, TNBlock estruct) -> blkNonStructValue estruct
  (IndexTASeg i, TNList vs) -> lstSubs vs `indexList` i
  (_, TNMutable mut)
    | (MutableArgTASeg i, RegOp m) <- (seg, mut) -> ropArgs m `indexList` i
    | (MutableArgTASeg i, Ref ref) <- (seg, mut) -> subRefArgs (refArg ref) `indexList` i
    | (MutableArgTASeg i, DisjOp d) <- (seg, mut) -> dstValue <$> djoTerms d `indexList` i
    | (MutableArgTASeg i, UOp u) <- (seg, mut) -> ufConjuncts u `indexList` i
    -- \| (ComprehTASeg ComprehStartValTASeg, Compreh c) <- (seg, mut) -> return $ getValFromStartClause (cphStart c)
    | (ComprehTASeg (ComprehIterClauseValTASeg i), Compreh c) <- (seg, mut) ->
        getValFromIterClause <$> (cphIterClauses c `indexList` i)
    | (ComprehTASeg ComprehIterValTASeg, Compreh c) <- (seg, mut) -> cphIterVal c
    | SubValTASeg <- seg -> getMutVal mut
  (_, TNDisj d)
    | DisjDefaultTASeg <- seg -> dsjDefault d
    | DisjDisjunctTASeg i <- seg -> dsjDisjuncts d `indexList` i
  -- CnstredVal is just a wrapper of a value. If we have additional segments, we should descend into the value.
  (_, TNCnstredVal cv)
    | SubValTASeg <- seg -> Just (cnsedVal cv)
  _ -> Nothing

-- | Set the sub tree with the given segment and new tree.
setSubTreeTN ::
  forall r s t m. (Env r s m, TreeOp t, Show t, HasTreeNode t) => TASeg -> t -> t -> m t
setSubTreeTN seg subT parT = do
  n <- case (seg, getTreeNode parT) of
    (StructTASeg s, TNBlock estruct) -> updateParStruct estruct s
    (SubValTASeg, TNBlock estruct) -> return $ TNBlock estruct{blkNonStructValue = Just subT}
    (IndexTASeg i, TNList vs) ->
      let subs = lstSubs vs
          l = TNList $ vs{lstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return l
    (_, TNMutable mut)
      | MutableArgTASeg i <- seg
      , RegOp f <- mut -> do
          let
            args = ropArgs f
            l = TNMutable . RegOp $ f{ropArgs = take i args ++ [subT] ++ drop (i + 1) args}
          return l
      | MutableArgTASeg i <- seg
      , Ref ref <- mut -> do
          let
            sels = subRefArgs (refArg ref)
            l = TNMutable . Ref $ ref{refArg = setRefArgs (refArg ref) $ take i sels ++ [subT] ++ drop (i + 1) sels}
          return l
      | MutableArgTASeg i <- seg
      , DisjOp d <- mut -> do
          let
            terms = djoTerms d
            l = TNMutable . DisjOp $ d{djoTerms = take i terms ++ [subT <$ terms !! i] ++ drop (i + 1) terms}
          return l
      | MutableArgTASeg i <- seg
      , UOp u <- mut -> do
          let
            conjuncts = ufConjuncts u
            l = TNMutable . UOp $ u{ufConjuncts = take i conjuncts ++ [subT] ++ drop (i + 1) conjuncts}
          return l
      | ComprehTASeg ComprehIterValTASeg <- seg
      , Compreh c <- mut ->
          return $ TNMutable $ Compreh c{cphIterVal = Just subT}
      | ComprehTASeg (ComprehIterClauseValTASeg i) <- seg
      , Compreh c <- mut -> do
          let clauses = cphIterClauses c
              clause = subT <$ (clauses !! i)
          return $ TNMutable $ Compreh c{cphIterClauses = take i clauses ++ [clause] ++ drop (i + 1) clauses}
      | SubValTASeg <- seg -> return . TNMutable $ setMutVal (Just subT) mut
    (_, TNDisj d)
      | DisjDefaultTASeg <- seg -> return (TNDisj $ d{dsjDefault = dsjDefault d})
      | DisjDisjunctTASeg i <- seg ->
          return (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)})
    (_, TNCnstredVal cv)
      | SubValTASeg <- seg -> return $ TNCnstredVal cv{cnsedVal = subT}
    (ParentTASeg, _) -> throwErrSt "setSubTreeTN: ParentTASeg is not allowed"
    (RootTASeg, _) -> throwErrSt "setSubTreeT: RootTASeg is not allowed"
    _ -> throwErrSt insertErrMsg
  return $ setTreeNode parT n
 where
  structToTN :: Struct t -> Block t -> TreeNode t
  structToTN s est = TNBlock est{blkStruct = s}

  updateParStruct :: (MonadError String m, HasCallStack) => Block t -> StructTASeg -> m (TreeNode t)
  updateParStruct parEStruct@(Block{blkStruct = parStruct}) labelSeg
    -- The label segment should already exist in the parent struct. Otherwise the description of the field will not be
    -- found.
    | StringTASeg name <- labelSeg
    , Just field <- lookupStructField name parStruct =
        let
          newField = subT `updateFieldValue` field
          newStruct = updateStructField name newField parStruct
         in
          return (structToTN newStruct parEStruct)
    | LetTASeg name <- labelSeg
    , Just oldLet <- lookupStructLet name parStruct =
        let
          newLet = subT <$ oldLet
          newStruct = updateStructLet name newLet parStruct
         in
          return (structToTN newStruct parEStruct)
    | PatternTASeg i j <- labelSeg =
        let
          psf = stcCnstrs parStruct IntMap.! i
          newPSF = if j == 0 then psf{scsPattern = subT} else psf{scsValue = subT}
          newStruct = parStruct{stcCnstrs = IntMap.insert i newPSF (stcCnstrs parStruct)}
         in
          return (structToTN newStruct parEStruct)
    | DynFieldTASeg i j <- labelSeg =
        let
          pends = stcDynFields parStruct
          psf = pends IntMap.! i
          newPSF = if j == 0 then psf{dsfLabel = subT} else psf{dsfValue = subT}
          newStruct = parStruct{stcDynFields = IntMap.insert i newPSF pends}
         in
          return (structToTN newStruct parEStruct)
    | EmbedTASeg i <- labelSeg =
        let
          oldEmbeds = blkEmbeds parEStruct
          newEmbed = subT <$ oldEmbeds IntMap.! i
         in
          return $ TNBlock parEStruct{blkEmbeds = IntMap.insert i newEmbed oldEmbeds}
  updateParStruct _ _ = throwErrSt insertErrMsg

  insertErrMsg :: String
  insertErrMsg =
    printf
      "setSubTreeTN: cannot insert child to parent, segment: %s, child:\n%s\nparent:\n%s"
      (show seg)
      (show subT)
      (show parT)

indexList :: [a] -> Int -> Maybe a
indexList xs i = if i < length xs then Just (xs !! i) else Nothing