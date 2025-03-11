{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.TreeNode where

import Class (TreeOp)
import Control.Monad.Except (MonadError)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromJust, isNothing)
import Env (Env)
import Exception (throwErrSt)
import Path (
  StructTASeg (..),
  TASeg (
    DisjDefaultTASeg,
    DisjDisjunctTASeg,
    IndexTASeg,
    MutableArgTASeg,
    ParentTASeg,
    RootTASeg,
    StructTASeg,
    SubValTASeg
  ),
  getStrFromSeg,
 )
import Text.Printf (printf)
import Value.Atom (AtomV)
import Value.Bottom (Bottom)
import Value.Bounds (Bounds)
import Value.Constraint (AtomCnstr, CnstredVal (cnsedVal))
import Value.Cycle (RefCycle, StructuralCycle)
import Value.Disj (Disj (dsjDefault, dsjDisjuncts))
import Value.List (List (lstSubs))
import Value.Mutable (
  Indexer (idxSels),
  Mutable (Index, SFunc),
  StatefulFunc (sfnArgs),
  getMutVal,
  setMutVal,
 )
import Value.Struct (
  DynamicField (dsfLabel),
  Field (ssfValue),
  LetBinding (lbValue),
  Struct (stcCnstrs, stcPendSubs),
  StructCnstr (scsPattern),
  StructVal (SField, SLet),
  lookupStructVal,
  updateStructSub,
 )

class HasTreeNode t where
  getTreeNode :: t -> TreeNode t
  setTreeNode :: t -> TreeNode t -> t

-- | TreeNode represents a tree structure that contains values.
data TreeNode t
  = -- | TNStruct is a struct that contains a value and a map of segments to Tree.
    TNStruct (Struct t)
  | TNList (List t)
  | TNDisj (Disj t)
  | -- | TNAtom contains an atom value.
    TNAtom AtomV
  | TNBounds Bounds
  | TNAtomCnstr (AtomCnstr t)
  | TNRefCycle RefCycle
  | TNStructuralCycle StructuralCycle
  | TNMutable (Mutable t)
  | TNCnstredVal (CnstredVal t)
  | TNTop
  | TNBottom Bottom
  | TNStub

instance (Eq t, TreeOp t, HasTreeNode t) => Eq (TreeNode t) where
  (==) (TNStruct s1) (TNStruct s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNAtom l1) (TNAtom l2) = l1 == l2
  (==) (TNAtomCnstr c1) (TNAtomCnstr c2) = c1 == c2
  (==) (TNRefCycle c1) (TNRefCycle c2) = c1 == c2
  (==) (TNDisj dj1) n2@(TNAtom _) =
    if isNothing (dsjDefault dj1)
      then False
      else getTreeNode (fromJust $ dsjDefault dj1) == n2
  (==) (TNAtom a1) (TNDisj dj2) = (==) (TNDisj dj2) (TNAtom a1)
  (==) (TNMutable f1) (TNMutable f2) = f1 == f2
  (==) (TNBounds b1) (TNBounds b2) = b1 == b2
  (==) (TNCnstredVal v1) (TNCnstredVal v2) = v1 == v2
  (==) (TNStructuralCycle c1) (TNStructuralCycle c2) = c1 == c2
  (==) (TNBottom _) (TNBottom _) = True
  (==) TNTop TNTop = True
  (==) TNStub TNStub = True
  (==) _ _ = False

{- | descend into the tree with the given segment.

This should only be used by TreeCursor.
-}
subTreeTN :: (TreeOp t, HasTreeNode t, Show t) => TASeg -> t -> Maybe t
subTreeTN seg t = case (seg, getTreeNode t) of
  (RootTASeg, _) -> Just t
  (StructTASeg s, TNStruct struct) -> case s of
    StringTASeg name ->
      lookupStructVal name struct
        >>= \case
          SField sf -> Just $ ssfValue sf
          _ -> Nothing
    PatternTASeg i -> scsPattern <$> stcCnstrs struct IntMap.!? i
    PendingTASeg i ->
      -- pending elements can be resolved, so the index might not be valid.
      dsfLabel <$> stcPendSubs struct IntMap.!? i
    LetTASeg name ->
      lookupStructVal name struct >>= \case
        SLet lb -> Just (lbValue lb)
        _ -> Nothing
  (IndexTASeg i, TNList vs) -> lstSubs vs `indexList` i
  (_, TNMutable mut)
    | (MutableArgTASeg i, SFunc m) <- (seg, mut) -> sfnArgs m `indexList` i
    | (MutableArgTASeg i, Index idx) <- (seg, mut) -> idxSels idx `indexList` i
    | SubValTASeg <- seg -> getMutVal mut
  (_, TNDisj d)
    | DisjDefaultTASeg <- seg -> dsjDefault d
    | DisjDisjunctTASeg i <- seg -> dsjDisjuncts d `indexList` i
  -- CnstredVal is just a wrapper of a value. If we have additional segments, we should descend into the value.
  (_, TNCnstredVal cv)
    | SubValTASeg <- seg -> Just (cnsedVal cv)
  _ -> Nothing
 where
  indexList :: [a] -> Int -> Maybe a
  indexList xs i = if i < length xs then Just (xs !! i) else Nothing

-- | Set the sub tree with the given segment and new tree.
setSubTreeTN ::
  forall m t. (Env m, TreeOp t, Show t, HasTreeNode t) => TASeg -> t -> t -> m t
setSubTreeTN seg subT parT = do
  n <- case (seg, getTreeNode parT) of
    (StructTASeg s, TNStruct struct) -> updateParStruct struct s
    (IndexTASeg i, TNList vs) ->
      let subs = lstSubs vs
          l = TNList $ vs{lstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return l
    (_, TNMutable mut)
      | MutableArgTASeg i <- seg
      , SFunc f <- mut -> do
          let
            args = sfnArgs f
            l = TNMutable . SFunc $ f{sfnArgs = take i args ++ [subT] ++ drop (i + 1) args}
          return l
      | MutableArgTASeg i <- seg
      , Index idx <- mut -> do
          let
            sels = idxSels idx
            l = TNMutable . Index $ idx{idxSels = take i sels ++ [subT] ++ drop (i + 1) sels}
          return l
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
  updateParStruct :: (MonadError String m) => Struct t -> StructTASeg -> m (TreeNode t)
  updateParStruct parStruct labelSeg
    -- The label segment should already exist in the parent struct. Otherwise the description of the field will not be
    -- found.
    | Just name <- getStrFromSeg labelSeg
    , Just sv <- lookupStructVal name parStruct =
        let
          newSV = subT <$ sv
          newStruct = updateStructSub labelSeg newSV parStruct
         in
          return (TNStruct newStruct)
    | PatternTASeg i <- labelSeg =
        let
          psf = stcCnstrs parStruct IntMap.! i
          newPSF = psf{scsPattern = subT}
          newStruct = parStruct{stcCnstrs = IntMap.insert i newPSF (stcCnstrs parStruct)}
         in
          return (TNStruct newStruct)
    | PendingTASeg i <- labelSeg =
        let
          pends = stcPendSubs parStruct
          psf = pends IntMap.! i
          newPSF = psf{dsfLabel = subT}
          newStruct = parStruct{stcPendSubs = IntMap.insert i newPSF pends}
         in
          return (TNStruct newStruct)
  updateParStruct _ _ = throwErrSt insertErrMsg

  insertErrMsg :: String
  insertErrMsg =
    printf
      "setSubTreeTN: cannot insert child to parent, segment: %s, child:\n%s\nparent:\n%s"
      (show seg)
      (show subT)
      (show parT)
