{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module TCursorOps where

import Class (TreeOp (setSubTree, subTree))
import Cursor
import Env
import Exception (throwErrSt)
import Path (TASeg (DisjDefaultTASeg, RootTASeg, SubValTASeg), TreeAddr (TreeAddr))
import Value.Tree

goDownTCAddr :: TreeAddr -> TreeCursor Tree -> Maybe (TreeCursor Tree)
goDownTCAddr (TreeAddr sels) = go (reverse sels)
 where
  go :: [TASeg] -> TreeCursor Tree -> Maybe (TreeCursor Tree)
  go [] cursor = Just cursor
  go (x : xs) cursor = do
    nextCur <- goDownTCSeg x cursor
    go xs nextCur

{- | Go down the TreeCursor with the given segment and return the new cursor.

It handles the case when the current node is a disjunction node.
-}
goDownTCSeg :: TASeg -> TreeCursor Tree -> Maybe (TreeCursor Tree)
goDownTCSeg seg tc = do
  let focus = vcFocus tc
  case subTree seg focus of
    Just nextTree -> return $ mkSubTC seg nextTree tc
    Nothing -> do
      (nextTree, nextSeg) <- case treeNode focus of
        TNMutable mut -> do
          mv <- getMutVal mut
          return (mv, SubValTASeg)
        TNCnstredVal cv -> return (cnsedVal cv, SubValTASeg)
        TNDisj d -> do
          dft <- dsjDefault d
          return (dft, DisjDefaultTASeg)
        _ -> Nothing
      goDownTCSeg seg $ mkSubTC nextSeg nextTree tc

{- | Propagates the changes made to the focus to the parent nodes.

It stops at the root.
-}
propUpTC :: (Env m) => TreeCursor Tree -> m (TreeCursor Tree)
propUpTC (ValCursor _ []) = throwErrSt "already at the top"
propUpTC tc@(ValCursor _ [(RootTASeg, _)]) = return tc
propUpTC (ValCursor subT ((seg, parT) : cs)) = do
  t <- setSubTree seg subT parT
  return $ ValCursor t cs