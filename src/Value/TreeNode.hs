{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.TreeNode where

import Class
import Control.Monad.Except (MonadError)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromJust, isNothing)
import Env
import Exception
import Path
import Text.Printf (printf)
import Value.Atom
import Value.Bottom
import Value.Bounds
import Value.Constraint
import Value.Cycle
import Value.Disj
import Value.List
import Value.Mutable
import Value.Struct

class HasTreeNode t where
  getTreeNode :: t -> TreeNode t
  setTreeNode :: t -> TreeNode t -> t

-- | TreeNode represents a tree structure that contains values.
data TreeNode t
  = -- | TNStruct is a struct that contains a value and a map of segments to Tree.
    TNStruct (Struct t)
  | TNList (List t)
  | TNDisj (Disj t)
  | --  TNAtom contains an atom value.
    TNAtom AtomV
  | TNBounds Bounds
  | TNConstraint (Constraint t)
  | TNRefCycle RefCycle
  | TNStructuralCycle StructuralCycle
  | TNMutable (Mutable t)
  | TNTop
  | TNBottom Bottom

instance (Eq t, TreeOp t, HasTreeNode t) => Eq (TreeNode t) where
  (==) (TNStruct s1) (TNStruct s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNAtom l1) (TNAtom l2) = l1 == l2
  (==) (TNConstraint c1) (TNConstraint c2) = c1 == c2
  (==) (TNRefCycle c1) (TNRefCycle c2) = c1 == c2
  (==) (TNDisj dj1) n2@(TNAtom _) =
    if isNothing (dsjDefault dj1)
      then False
      else getTreeNode (fromJust $ dsjDefault dj1) == n2
  (==) (TNAtom a1) (TNDisj dj2) = (==) (TNDisj dj2) (TNAtom a1)
  (==) (TNMutable f1) (TNMutable f2) = f1 == f2
  (==) (TNBounds b1) (TNBounds b2) = b1 == b2
  (==) (TNBottom _) (TNBottom _) = True
  (==) TNTop TNTop = True
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
    | (MutableTASeg (MutableArgTASeg i), SFunc m) <- (seg, mut) -> sfnArgs m `indexList` i
    | (MutableTASeg (MutableArgTASeg i), Index idx) <- (seg, mut) -> idxSels idx `indexList` i
    | MutableTASeg MutableValTASeg <- seg -> getMutVal mut
    -- This has to be the last case because the explicit function segment has the highest priority.
    | otherwise -> getMutVal mut >>= subTree seg
  -- (_, TNMutable (Ref ref)) -> refValue ref >>= subTree seg
  (_, TNDisj d)
    | DisjDefaultTASeg <- seg -> dsjDefault d
    | DisjDisjunctTASeg i <- seg -> dsjDisjuncts d `indexList` i
    -- This has to be the last case because the explicit disjunct segment has the highest priority.
    | otherwise -> dsjDefault d >>= subTree seg
  _ -> Nothing
 where
  indexList :: [a] -> Int -> Maybe a
  indexList xs i = if i < length xs then Just (xs !! i) else Nothing

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
      | (MutableTASeg (MutableArgTASeg i)) <- seg
      , SFunc f <- mut -> do
          let
            args = sfnArgs f
            l = TNMutable . SFunc $ f{sfnArgs = take i args ++ [subT] ++ drop (i + 1) args}
          return l
      | (MutableTASeg (MutableArgTASeg i)) <- seg
      , Index idx <- mut -> do
          let
            sels = idxSels idx
            l = TNMutable . Index $ idx{idxSels = take i sels ++ [subT] ++ drop (i + 1) sels}
          return l
      | MutableTASeg MutableValTASeg <- seg -> return . TNMutable $ setMutVal (Just subT) mut
      -- If the segment is not a mutable segment, then the sub value must have been the sfnValue value.
      | otherwise ->
          maybe
            (throwErrSt $ printf "setSubTreeTN: mutable value is not found for non-function segment %s" (show seg))
            ( \r -> do
                updatedR <- setSubTree seg subT r
                return (TNMutable $ setMutVal (Just updatedR) mut)
            )
            (getMutVal mut)
    (_, TNDisj d)
      | DisjDefaultTASeg <- seg -> return (TNDisj $ d{dsjDefault = dsjDefault d})
      | DisjDisjunctTASeg i <- seg ->
          return (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)})
      -- If the segment is not a disjunction segment, then the sub value must have been the default disjunction
      -- value.
      | otherwise ->
          maybe
            ( throwErrSt $
                printf
                  "setSubTreeTN: default disjunction value is not found for non-disjunction segment %s"
                  (show seg)
            )
            ( \dft -> do
                updatedDftT <- setSubTree seg subT dft
                return (TNDisj $ d{dsjDefault = Just updatedDftT})
            )
            (dsjDefault d)
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
