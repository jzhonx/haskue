{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module Cursor where

import Common (Env)
import Control.DeepSeq (NFData (..))
import Control.Monad (foldM)
import Data.ByteString.Builder (
  Builder,
  char7,
  string7,
  toLazyByteString,
 )
import qualified Data.ByteString.Lazy.Char8 as LBS
import qualified Data.Vector as V
import Exception (throwErrSt)
import GHC.Generics (Generic)
import Path
import Text.Printf (printf)
import Value

class HasTreeCursor s where
  getTreeCursor :: s -> TrCur
  setTreeCursor :: s -> TrCur -> s

{- | TreeCursor is a pair of a value and a list of crumbs.
For example,
{
a: {
  b: {
    c: 42
  } // struct_c
} // struct_b
} // struct_a
Suppose the cursor is at the struct that contains the value 42. The cursor is
(struct_c, [("b", struct_b), ("a", struct_a)]).
-}
data TrCur = TrCur
  { tcFocus :: Tree
  , tcCrumbs :: [TreeCrumb]
  }
  deriving (Eq, Generic, NFData)

-- | By default, only show the focus of the cursor.
instance Show TrCur where
  show = show . tcFocus

pattern TCFocus :: Tree -> TrCur
pattern TCFocus t <- TrCur{tcFocus = t}

type TreeCrumb = (TASeg, Tree)

addrFromCrumbs :: [TreeCrumb] -> TreeAddr
addrFromCrumbs crumbs = addrFromList $ go crumbs []
 where
  go :: [TreeCrumb] -> [TASeg] -> [TASeg]
  go [] acc = acc
  go ((n, _) : cs) acc = go cs (n : acc)

setTCFocus :: Tree -> TrCur -> TrCur
setTCFocus t (TrCur _ cs) = TrCur t cs

-- | Generate tree address from the tree cursor.
tcCanAddr :: TrCur -> TreeAddr
tcCanAddr c = addrFromCrumbs (tcCrumbs c)

-- | Get the parent of the cursor without propagating the value up.
parentTC :: TrCur -> Maybe TrCur
parentTC (TrCur _ []) = Nothing
parentTC (TrCur _ ((_, t) : cs)) = Just $ TrCur t cs

parentTCMust :: (Env r s m) => TrCur -> m TrCur
parentTCMust tc = maybe (throwErrSt "already top") return (parentTC tc)

-- | Get the segment paired with the focus of the cursor.
tcFocusSeg :: TrCur -> Maybe TASeg
tcFocusSeg (TrCur _ []) = Nothing
tcFocusSeg tc = return $ fst . head $ tcCrumbs tc

-- | Get the segment paired with the focus of the cursor.
tcFocusSegMust :: (Env r s m) => TrCur -> m TASeg
tcFocusSegMust tc = maybe (throwErrSt "already top") return (tcFocusSeg tc)

isTCTop :: TrCur -> Bool
isTCTop (TrCur _ []) = True
isTCTop _ = False

showCursor :: TrCur -> String
showCursor tc = LBS.unpack $ toLazyByteString $ prettyBldr tc
 where
  prettyBldr :: TrCur -> Builder
  prettyBldr (TrCur t cs) =
    string7 "-- ():\n"
      <> string7 (show t)
      <> char7 '\n'
      <> foldl
        ( \b (seg, n) ->
            b
              <> string7 "-- "
              <> string7 (show seg)
              <> char7 ':'
              <> char7 '\n'
              <> string7 (show n)
              <> char7 '\n'
        )
        mempty
        cs

mkSubTC :: TASeg -> Tree -> TrCur -> TrCur
mkSubTC seg a tc = TrCur a ((seg, tcFocus tc) : tcCrumbs tc)

modifyTCFocus :: (Tree -> Tree) -> TrCur -> TrCur
modifyTCFocus f (TrCur t cs) = TrCur (f t) cs

setTCFocusTN :: TreeNode -> TrCur -> TrCur
setTCFocusTN tn = modifyTCFocus (`setTN` tn)

goDownTCAddr :: TreeAddr -> TrCur -> Maybe TrCur
goDownTCAddr a = go (addrToList a)
 where
  go :: [TASeg] -> TrCur -> Maybe TrCur
  go [] cursor = Just cursor
  go (x : xs) cursor = do
    nextCur <- goDownTCSeg x cursor
    go xs nextCur

goDownTAddr :: TreeAddr -> Tree -> Maybe TrCur
goDownTAddr addr starT = goDownTCAddr addr (TrCur starT [])

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
  case subTree seg focus of
    Just nextTree -> return $ mkSubTC seg nextTree tc
    Nothing -> do
      (nextTree, nextSeg) <- case treeNode focus of
        TNMutable mut -> do
          mv <- getMutVal mut
          return (mv, SubValTASeg)
        TNDisj d -> do
          dft <- dsjDefault d
          return (dft, DisjDefTASeg)
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
goDownTSeg :: TASeg -> Tree -> Maybe TrCur
goDownTSeg seg startT = goDownTCSeg seg (TrCur startT [])

{- | Propagates the changes made to the focus to the parent nodes.

It stops at the root.
-}
propUpTC :: (Env r s m) => TrCur -> m TrCur
propUpTC (TrCur _ []) = throwErrSt "already at the top"
propUpTC tc@(TrCur _ [(RootTASeg, _)]) = return tc
propUpTC (TrCur subT ((seg, parT) : cs)) = do
  t <- setSubTree seg subT parT
  return $ TrCur t cs

{- | Surface evaluated values up until the root and return the updated tree cursor with the original cursor
position.
-}
syncTC :: (Env r s m) => TrCur -> m TrCur
syncTC a = go a []
 where
  go (TrCur _ []) _ = throwErrSt "already at the top"
  go tc@(TrCur _ [(RootTASeg, _)]) acc =
    -- Leftmost of the acc represents the highest processed tree.
    -- Go from the highest processed tree to the original cursor position.
    -- The accTC has the processed parent tree.
    return $ foldl (\accTC (t, seg) -> TrCur t ((seg, tcFocus accTC) : tcCrumbs accTC)) tc acc
  go (TrCur _ [_]) _ = throwErrSt "highest segment is not RootTASeg"
  go tc@(TrCur subT ((seg, _) : _)) acc = do
    parTC <- propUpTC tc
    go parTC ((subT, seg) : acc)

-- | Get the top cursor of the tree. No propagation is involved.
topTC :: (Env r s m) => TrCur -> m TrCur
topTC (TrCur _ []) = throwErrSt "already at the top"
topTC tc@(TrCur _ ((RootTASeg, _) : _)) = return tc
topTC (TrCur _ ((_, parT) : cs)) = topTC $ TrCur parT cs

{- | Visit every node in the tree in pre-order and apply the function.

It does not re-constrain struct fields.
-}
traverseTC ::
  (Env r s m) =>
  (Tree -> [(TASeg, Tree)]) ->
  ((TrCur, a) -> m (TrCur, a)) ->
  (TrCur, a) ->
  m (TrCur, a)
traverseTC subs f x = do
  y <- f x
  foldM
    ( \acc (seg, sub) -> do
        z <- traverseTC subs f (mkSubTC seg sub (fst acc), snd acc)
        nextTC <- propUpTC (fst z)
        return (nextTC, snd z)
    )
    y
    (subs $ tcFocus $ fst y)

-- | A simple version of the traverseTC function that does not return a custom value.
traverseTCSimple ::
  (Env r s m) =>
  (Tree -> [(TASeg, Tree)]) ->
  (TrCur -> m Tree) ->
  TrCur ->
  m TrCur
traverseTCSimple subs f tc = do
  (r, _) <- traverseTC subs (\(x, _) -> f x >>= \y -> return (y `setTCFocus` x, ())) (tc, ())
  return r

inSubTC :: (Env r s m) => TASeg -> (TrCur -> m Tree) -> TrCur -> m TrCur
inSubTC seg f tc = do
  subTC <- goDownTCSegMust seg tc
  r <- f subTC
  propUpTC (r `setTCFocus` subTC)

snapshotTC :: (Env r s m) => TrCur -> m TrCur
snapshotTC tc = do
  let
    rewrite xtc =
      let focus = tcFocus xtc
       in return $ case treeNode focus of
            TNBlock block
              | IsBlockEmbed ev <- block -> ev
            TNMutable m -> maybe focus id (getMutVal m)
            _ -> focus

  traverseTCSimple subNodes rewrite tc