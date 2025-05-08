{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cursor where

import Common
import Data.ByteString.Builder (
  Builder,
  char7,
  string7,
  toLazyByteString,
 )
import qualified Data.ByteString.Lazy.Char8 as LBS
import Exception (throwErrSt)
import qualified Path

class HasTreeCursor s t where
  getTreeCursor :: s -> TreeCursor t
  setTreeCursor :: s -> TreeCursor t -> s

type TreeCrumb t = (Path.TASeg, t)

addrFromCrumbs :: [TreeCrumb t] -> Path.TreeAddr
addrFromCrumbs crumbs = Path.TreeAddr . reverse $ go crumbs []
 where
  go :: [TreeCrumb t] -> [Path.TASeg] -> [Path.TASeg]
  go [] acc = acc
  go ((n, _) : cs) acc = go cs (n : acc)

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
data TreeCursor t = TreeCursor
  { tcFocus :: t
  , tcCrumbs :: [TreeCrumb t]
  }
  deriving (Eq)

-- | By default, only show the focus of the cursor.
instance (Show t) => Show (TreeCursor t) where
  show = show . tcFocus

setTCFocus :: t -> TreeCursor t -> TreeCursor t
setTCFocus t (TreeCursor _ cs) = TreeCursor t cs

-- | Generate canonical form of tree address from the tree cursor.
tcCanAddr :: TreeCursor t -> Path.TreeAddr
tcCanAddr c = trim $ addrFromCrumbs (tcCrumbs c)
 where
  trim :: Path.TreeAddr -> Path.TreeAddr
  trim (Path.TreeAddr segs) = Path.TreeAddr $ filter (not . Path.isSegNonCanonical) segs

-- | Get the parent of the cursor without propagating the value up.
parentTC :: TreeCursor t -> Maybe (TreeCursor t)
parentTC (TreeCursor _ []) = Nothing
parentTC (TreeCursor _ ((_, t) : cs)) = Just $ TreeCursor t cs

parentTCMust :: (Env r s m) => TreeCursor t -> m (TreeCursor t)
parentTCMust tc = maybe (throwErrSt "already top") return (parentTC tc)

-- | Get the segment paired with the focus of the cursor.
focusTCSeg :: (Env r s m) => TreeCursor t -> m Path.TASeg
focusTCSeg (TreeCursor _ []) = throwErrSt "already at the top"
focusTCSeg tc = return $ fst . head $ tcCrumbs tc

isTCTop :: TreeCursor t -> Bool
isTCTop (TreeCursor _ []) = True
isTCTop _ = False

showCursor :: (Show t) => TreeCursor t -> String
showCursor tc = LBS.unpack $ toLazyByteString $ prettyBldr tc
 where
  prettyBldr :: (Show t) => TreeCursor t -> Builder
  prettyBldr (TreeCursor t cs) =
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

mkSubTC :: Path.TASeg -> t -> TreeCursor t -> TreeCursor t
mkSubTC seg a tc = TreeCursor a ((seg, tcFocus tc) : tcCrumbs tc)
