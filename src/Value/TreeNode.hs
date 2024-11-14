{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.TreeNode where

import Class
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isNothing)
import Env
import Path
import Text.Printf (printf)
import Value.Atom
import Value.Bottom
import Value.Bounds
import Value.Constraint
import Value.Cycle
import Value.Disj
import Value.Func
import Value.List
import Value.Struct

class HasTreeNode t where
  getTreeNode :: t -> TreeNode t
  setTreeNode :: t -> TreeNode t -> t

-- | TreeNode represents a tree structure that contains values.
data TreeNode t
  = -- | TNStruct is a struct that contains a value and a map of selectors to Tree.
    TNStruct (Struct t)
  | TNList (List t)
  | TNDisj (Disj t)
  | --  TNAtom contains an atom value.
    TNAtom AtomV
  | TNBounds Bounds
  | TNConstraint (Constraint t)
  | TNRefCycle RefCycle
  | TNFunc (Func t)
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
  (==) (TNFunc f1) (TNFunc f2) = f1 == f2
  (==) (TNBounds b1) (TNBounds b2) = b1 == b2
  (==) (TNBottom _) (TNBottom _) = True
  (==) TNTop TNTop = True
  (==) _ _ = False

-- step down the tree with the given selector.
-- This should only be used by TreeCursor.
subTreeTN :: (TreeOp t, HasTreeNode t) => Selector -> t -> Maybe t
subTreeTN sel t = case (sel, getTreeNode t) of
  (RootSelector, _) -> Just t
  (StructSelector s, TNStruct struct) -> case s of
    StringSelector _ -> ssfField <$> Map.lookup s (stcSubs struct)
    PatternSelector i -> Just (psfValue $ stcPatterns struct !! i)
    PendingSelector i -> case stcPendSubs struct !! i of
      DynamicField dsf -> Just (dsfValue dsf)
      PatternField _ val -> Just val
  (IndexSelector i, TNList vs) -> lstSubs vs `indexList` i
  (FuncSelector f, TNFunc fn) -> case f of
    FuncArgSelector i -> fncArgs fn `indexList` i
    FuncResSelector -> fncTempRes fn
  (_, TNDisj d)
    | DisjDefaultSelector <- sel -> dsjDefault d
    | DisjDisjunctSelector i <- sel -> dsjDisjuncts d `indexList` i
    -- This has to be the last case because the explicit disjunct selector has the highest priority.
    | otherwise -> dsjDefault d >>= subTree sel
  (_, TNConstraint c) | sel == unaryOpSelector -> Just (cnsValidator c)
  _ -> Nothing
 where
  indexList :: [a] -> Int -> Maybe a
  indexList xs i = if i < length xs then Just (xs !! i) else Nothing

setSubTreeTN ::
  forall m t. (Env m, TreeOp t, Show t, HasTreeNode t) => Selector -> t -> t -> m t
setSubTreeTN sel subT parT = do
  n <- case (sel, getTreeNode parT) of
    (StructSelector s, TNStruct struct) -> updateParStruct struct s
    (IndexSelector i, TNList vs) ->
      let subs = lstSubs vs
          l = TNList $ vs{lstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return l
    (FuncSelector f, TNFunc fn) -> case f of
      FuncArgSelector i -> do
        let
          args = fncArgs fn
          l = TNFunc $ fn{fncArgs = take i args ++ [subT] ++ drop (i + 1) args}
        return l
      FuncResSelector -> do
        let l = TNFunc $ fn{fncTempRes = Just subT}
        return l
    (_, TNDisj d)
      | DisjDefaultSelector <- sel -> return (TNDisj $ d{dsjDefault = dsjDefault d})
      | DisjDisjunctSelector i <- sel ->
          return (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)})
      -- If the selector is not a disjunction selector, then the sub value must have been the default disjunction
      -- value.
      | otherwise ->
          maybe
            (throwError "propValUp: default disjunction value not found for non-disjunction selector")
            ( \dft -> do
                updatedDftT <- setSubTree sel subT dft
                return (TNDisj $ d{dsjDefault = Just updatedDftT})
            )
            (dsjDefault d)
    (FuncSelector _, TNConstraint c) ->
      return (TNConstraint $ c{cnsValidator = subT})
    (ParentSelector, _) -> throwError "propValUp: ParentSelector is not allowed"
    (RootSelector, _) -> throwError "propValUp: RootSelector is not allowed"
    _ -> throwError insertErrMsg
  return $ setTreeNode parT n
 where
  updateParStruct :: (MonadError String m) => Struct t -> StructSelector -> m (TreeNode t)
  updateParStruct parStruct labelSel =
    if
      | b@(TNBottom _) <- getTreeNode subT -> return b
      -- the label selector should already exist in the parent struct.
      | Map.member labelSel (stcSubs parStruct) ->
          let
            sf = stcSubs parStruct Map.! labelSel
            newSF = sf{ssfField = subT}
            newStruct = parStruct{stcSubs = Map.insert labelSel newSF (stcSubs parStruct)}
           in
            return (TNStruct newStruct)
      | otherwise -> case labelSel of
          PatternSelector i ->
            let
              psf = stcPatterns parStruct !! i
              newPSF = psf{psfValue = subT}
              newStruct =
                parStruct
                  { stcPatterns = take i (stcPatterns parStruct) ++ [newPSF] ++ drop (i + 1) (stcPatterns parStruct)
                  }
             in
              return (TNStruct newStruct)
          PendingSelector i ->
            let
              psf = stcPendSubs parStruct !! i
              newPSF = modifyPSEValue (const subT) psf
              newStruct =
                parStruct
                  { stcPendSubs =
                      take i (stcPendSubs parStruct) ++ [newPSF] ++ drop (i + 1) (stcPendSubs parStruct)
                  }
             in
              return (TNStruct newStruct)
          _ -> throwError insertErrMsg

  insertErrMsg :: String
  insertErrMsg =
    printf
      "propValUp: cannot insert child to parent, selector: %s, child:\n%s\nparent:\n%s"
      (show sel)
      (show subT)
      (show parT)

getVarFieldTN :: (HasTreeNode t) => StructSelector -> t -> Maybe t
getVarFieldTN ssel t = case getTreeNode t of
  (TNStruct struct) -> do
    sf <- Map.lookup ssel (stcSubs struct)
    if lbAttrIsVar (ssfAttr sf)
      then Just (ssfField sf)
      else Nothing
  _ -> Nothing
