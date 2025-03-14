{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module TCursorOps where

import Common (Env, TreeOp (setSubTree, subTree))
import Control.Monad (foldM)
import Cursor
import Exception (throwErrSt)
import Path (TASeg (DisjDefaultTASeg, RootTASeg, SubValTASeg), TreeAddr (TreeAddr))
import qualified Value.Tree as VT

goDownTCAddr :: TreeAddr -> TreeCursor VT.Tree -> Maybe (TreeCursor VT.Tree)
goDownTCAddr (TreeAddr sels) = go (reverse sels)
 where
  go :: [TASeg] -> TreeCursor VT.Tree -> Maybe (TreeCursor VT.Tree)
  go [] cursor = Just cursor
  go (x : xs) cursor = do
    nextCur <- goDownTCSeg x cursor
    go xs nextCur

{- | Go down the TreeCursor with the given segment and return the new cursor.

It handles the case when the current node is a disjunction node.
-}
goDownTCSeg :: TASeg -> TreeCursor VT.Tree -> Maybe (TreeCursor VT.Tree)
goDownTCSeg seg tc = do
  let focus = vcFocus tc
  case subTree seg focus of
    Just nextTree -> return $ mkSubTC seg nextTree tc
    Nothing -> do
      (nextTree, nextSeg) <- case VT.treeNode focus of
        VT.TNMutable mut -> do
          mv <- VT.getMutVal mut
          return (mv, SubValTASeg)
        VT.TNCnstredVal cv -> return (VT.cnsedVal cv, SubValTASeg)
        VT.TNDisj d -> do
          dft <- VT.dsjDefault d
          return (dft, DisjDefaultTASeg)
        _ -> Nothing
      goDownTCSeg seg $ mkSubTC nextSeg nextTree tc

{- | Propagates the changes made to the focus to the parent nodes.

It stops at the root.
-}
propUpTC :: (Env r m) => TreeCursor VT.Tree -> m (TreeCursor VT.Tree)
propUpTC (ValCursor _ []) = throwErrSt "already at the top"
propUpTC tc@(ValCursor _ [(RootTASeg, _)]) = return tc
propUpTC (ValCursor subT ((seg, parT) : cs)) = do
  t <- setSubTree seg subT parT
  return $ ValCursor t cs

{- | Visit every node in the tree in pre-order and apply the function.

It does not re-constrain struct fields.
-}
traverseTC ::
  (Env r m) =>
  (VT.Tree -> [(TASeg, VT.Tree)]) ->
  ((TreeCursor VT.Tree, a) -> m (TreeCursor VT.Tree, a)) ->
  (TreeCursor VT.Tree, a) ->
  m (TreeCursor VT.Tree, a)
traverseTC subNodes f x = do
  y <- f x
  foldM
    ( \acc (seg, sub) -> do
        z <- traverseTC subNodes f (mkSubTC seg sub (fst acc), snd acc)
        nextTC <- propUpTC (fst z)
        return (nextTC, snd z)
    )
    y
    (subNodes $ vcFocus $ fst y)

traverseTCSimple ::
  (Env r m) =>
  (VT.Tree -> [(TASeg, VT.Tree)]) ->
  (TreeCursor VT.Tree -> m VT.Tree) ->
  TreeCursor VT.Tree ->
  m (TreeCursor VT.Tree)
traverseTCSimple subNodes f tc = do
  (r, _) <- traverseTC subNodes (\(x, _) -> f x >>= \y -> return (y <$ x, ())) (tc, ())
  return r