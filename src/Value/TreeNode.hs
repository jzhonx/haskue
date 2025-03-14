{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.TreeNode where

import Common (Env, TreeOp)
import Control.Monad.Except (MonadError)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromJust, isNothing)
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
  -- Indexer (idxSels),
  Mutable (Ref, SFunc),
  StatefulFunc (sfnArgs),
  getMutVal,
  setMutVal,
 )
import Value.Reference (Reference (refArg), setRefArgs, subRefArgs)
import Value.Struct (
  DynamicField (..),
  Field (ssfValue),
  LetBinding (lbValue),
  Struct (stcCnstrs, stcPendSubs),
  StructCnstr (..),
  StructVal (SField, SLet),
  getFieldFromSV,
  lookupStructField,
  lookupStructLet,
  lookupStructVal,
  updateStructField,
  updateStructLet,
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
    StringTASeg name
      | Just sf <- lookupStructField name struct -> Just $ ssfValue sf
    PatternTASeg i j -> (if j == 0 then scsPattern else scsValue) <$> stcCnstrs struct IntMap.!? i
    PendingTASeg i j ->
      -- pending elements can be resolved, so the index might not be valid.
      (if j == 0 then dsfLabel else dsfValue) <$> stcPendSubs struct IntMap.!? i
    LetTASeg name
      | Just lb <- lookupStructLet name struct -> Just (lbValue lb)
    _ -> Nothing
  (IndexTASeg i, TNList vs) -> lstSubs vs `indexList` i
  (_, TNMutable mut)
    | (MutableArgTASeg i, SFunc m) <- (seg, mut) -> sfnArgs m `indexList` i
    | (MutableArgTASeg i, Ref ref) <- (seg, mut) -> subRefArgs (refArg ref) `indexList` i
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
  forall t r m. (Env r m, TreeOp t, Show t, HasTreeNode t) => TASeg -> t -> t -> m t
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
      , Ref ref <- mut -> do
          let
            sels = subRefArgs (refArg ref)
            l = TNMutable . Ref $ ref{refArg = setRefArgs (refArg ref) $ take i sels ++ [subT] ++ drop (i + 1) sels}
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
    | StringTASeg name <- labelSeg
    , Just field <- lookupStructField name parStruct =
        let
          newField = subT <$ field
          newStruct = updateStructField name newField parStruct
         in
          return (TNStruct newStruct)
    | LetTASeg name <- labelSeg
    , Just oldLet <- lookupStructLet name parStruct =
        let
          newLet = subT <$ oldLet
          newStruct = updateStructLet name newLet parStruct
         in
          return (TNStruct newStruct)
    | PatternTASeg i j <- labelSeg =
        let
          psf = stcCnstrs parStruct IntMap.! i
          newPSF = if j == 0 then psf{scsPattern = subT} else psf{scsValue = subT}
          newStruct = parStruct{stcCnstrs = IntMap.insert i newPSF (stcCnstrs parStruct)}
         in
          return (TNStruct newStruct)
    | PendingTASeg i j <- labelSeg =
        let
          pends = stcPendSubs parStruct
          psf = pends IntMap.! i
          newPSF = if j == 0 then psf{dsfLabel = subT} else psf{dsfValue = subT}
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
