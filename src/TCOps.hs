{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module TCOps where

import Common (Env)
import Control.Monad (foldM)
import Cursor
import Exception (throwErrSt)
import Path (TASeg (DisjDefaultTASeg, RootTASeg, SubValTASeg), TreeAddr, addrToList, tailTreeAddr)
import Text.Printf (printf)
import qualified Value.Tree as VT

type TrCur = TreeCursor VT.Tree

setTCFocusTN :: VT.TreeNode -> TrCur -> TrCur
setTCFocusTN tn tc = let focus = tcFocus tc in VT.setTN focus tn `setTCFocus` tc

getTCFocusSeg :: (Env r s m) => TrCur -> m TASeg
getTCFocusSeg (TreeCursor _ []) = throwErrSt "already at the top"
getTCFocusSeg (TreeCursor _ ((seg, _) : _)) = return seg

goDownTCAddr :: TreeAddr -> TrCur -> Maybe TrCur
goDownTCAddr a = go (Path.addrToList a)
 where
  go :: [TASeg] -> TrCur -> Maybe TrCur
  go [] cursor = Just cursor
  go (x : xs) cursor = do
    nextCur <- goDownTCSeg x cursor
    go xs nextCur

goDownTAddr :: TreeAddr -> VT.Tree -> Maybe TrCur
goDownTAddr addr starT = goDownTCAddr addr (TreeCursor starT [])

goDownTCAddrMust :: (Env r s m) => TreeAddr -> TrCur -> m TrCur
goDownTCAddrMust addr tc =
  maybe
    (throwErrSt $ printf "cannot go to addr (%s) tree from %s" (show addr) (show $ tcCanAddr tc))
    return
    (goDownTCAddr addr tc)

{- | Go down the TreeCursor with the given segment and return the new cursor.

It handles the cases when a node can be accessed without segments, such as the default value of a disjunction.
-}
goDownTCSeg :: TASeg -> TrCur -> Maybe TrCur
goDownTCSeg seg tc = do
  let focus = tcFocus tc
  case VT.subTree seg focus of
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

goDownTCSegMust :: (Env r s m) => TASeg -> TrCur -> m TrCur
goDownTCSegMust seg tc =
  maybe
    (throwErrSt $ printf "cannot go to sub (%s) tree from %s" (show seg) (show $ tcCanAddr tc))
    return
    $ goDownTCSeg seg tc

{- | Go down the Tree with the given segment and return the new cursor with the visiting path.

It handles the cases when a node can be accessed without segments, such as the default value of a disjunction.
-}
goDownTSeg :: TASeg -> VT.Tree -> Maybe TrCur
goDownTSeg seg startT = goDownTCSeg seg (TreeCursor startT [])

{- | Propagates the changes made to the focus to the parent nodes.

It ensures that the version of the parent node is always greater than or equal to any of its children.

It stops at the root.
-}
propUpTC :: (Env r s m) => TrCur -> m TrCur
propUpTC (TreeCursor _ []) = throwErrSt "already at the top"
propUpTC tc@(TreeCursor _ [(RootTASeg, _)]) = return tc
propUpTC (TreeCursor subT@VT.Tree{VT.treeVersion = vers} ((seg, parT) : cs)) = do
  t <- VT.setSubTree seg subT parT
  return $ TreeCursor (t{VT.treeVersion = vers}) cs

-- Propagate the bottom value up until the root and return the updated tree cursor with the original cursor position.
syncTC :: (Env r s m) => TrCur -> m TrCur
syncTC tc = do
  let addr = tcCanAddr tc
      addrTillRootM = tailTreeAddr addr
  top <- go tc
  addrTillRoot <- maybe (throwErrSt $ printf "tail tree addr of %s does not exist" (show addr)) return addrTillRootM
  goDownTCAddrMust addrTillRoot top
 where
  go cur@(TreeCursor _ [(RootTASeg, _)]) = return cur
  go cur = propUpTC cur >>= go

-- | Get the top cursor of the tree. No propagation is involved.
topTC :: (Env r s m) => TrCur -> m TrCur
topTC (TreeCursor _ []) = throwErrSt "already at the top"
topTC tc@(TreeCursor _ ((RootTASeg, _) : _)) = return tc
topTC (TreeCursor _ ((_, parT) : cs)) = topTC $ TreeCursor parT cs

{- | Visit every node in the tree in pre-order and apply the function.

It does not re-constrain struct fields.
-}
traverseTC ::
  (Env r s m) =>
  (VT.Tree -> [(TASeg, VT.Tree)]) ->
  ((TrCur, a) -> m (TrCur, a)) ->
  (TrCur, a) ->
  m (TrCur, a)
traverseTC subNodes f x = do
  y <- f x
  foldM
    ( \acc (seg, sub) -> do
        z <- traverseTC subNodes f (mkSubTC seg sub (fst acc), snd acc)
        nextTC <- propUpTC (fst z)
        return (nextTC, snd z)
    )
    y
    (subNodes $ tcFocus $ fst y)

-- | A simple version of the traverseTC function that does not return a custom value.
traverseTCSimple ::
  (Env r s m) =>
  (VT.Tree -> [(TASeg, VT.Tree)]) ->
  (TrCur -> m VT.Tree) ->
  TrCur ->
  m TrCur
traverseTCSimple subNodes f tc = do
  (r, _) <- traverseTC subNodes (\(x, _) -> f x >>= \y -> return (y `setTCFocus` x, ())) (tc, ())
  return r

inSubTC :: (Env r s m) => TASeg -> (TrCur -> m VT.Tree) -> TrCur -> m TrCur
inSubTC seg f tc = do
  subTC <- goDownTCSegMust seg tc
  r <- f subTC
  propUpTC (r `Cursor.setTCFocus` subTC)

snapshotTC :: (Env r s m) => TrCur -> m TrCur
snapshotTC tc = do
  let
    rewrite xtc =
      let focus = tcFocus xtc
       in return $ case VT.treeNode focus of
            VT.TNBlock block
              | Just ev <- VT.blkNonStructValue block -> ev
            VT.TNMutable m -> maybe focus id (VT.getMutVal m)
            VT.TNCnstredVal c -> VT.cnsedVal c
            _ -> focus

  traverseTCSimple VT.subNodes rewrite tc