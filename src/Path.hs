{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-}

module Path where

import Control.DeepSeq (NFData (..))
import qualified Data.ByteString as B
import Data.List (intercalate)
import Data.List.Split (splitOn)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Vector as V
import GHC.Generics (Generic)

data Selector = StringSel B.ByteString | IntSel !Int
  deriving (Eq, Ord, Generic, NFData)

{- FieldPath is a list of selectors.

The selectors are not stored in reverse order.
-}
newtype FieldPath = FieldPath {getRefSels :: [Selector]}
  deriving (Eq, Ord, Generic, NFData)

instance Show Selector where
  show (StringSel s) = show s
  show (IntSel i) = show i

instance Show FieldPath where
  show :: FieldPath -> String
  show (FieldPath sels) = intercalate "." (map show sels)

emptyFieldPath :: FieldPath
emptyFieldPath = FieldPath []

headSel :: FieldPath -> Maybe Selector
headSel (FieldPath []) = Nothing
headSel (FieldPath sels) = Just $ sels !! 0

tailFieldPath :: FieldPath -> Maybe FieldPath
tailFieldPath (FieldPath []) = Nothing
tailFieldPath (FieldPath sels) = Just $ FieldPath (tail sels)

appendFieldPaths ::
  -- | front
  FieldPath ->
  -- | back
  FieldPath ->
  FieldPath
appendFieldPaths (FieldPath xs) (FieldPath ys) = FieldPath (xs ++ ys)

isFieldPathEmpty :: FieldPath -> Bool
isFieldPathEmpty (FieldPath []) = True
isFieldPathEmpty _ = False

fieldPathToAddr :: FieldPath -> TreeAddr
fieldPathToAddr (FieldPath sels) = addrFromList $ map selToTASeg sels

selToTASeg :: Selector -> TASeg
selToTASeg (StringSel s) = BlockTASeg $ StringTASeg s
selToTASeg (IntSel i) = IndexTASeg i

fieldPathFromString :: String -> FieldPath
fieldPathFromString s =
  FieldPath
    { getRefSels =
        map
          ( \x ->
              case reads x of
                [(i, "")] -> IntSel i
                _ -> StringSel (TE.encodeUtf8 (T.pack x))
          )
          (splitOn "." s)
    }

-- == TASeg ==

-- | TASeg is paired with a tree node.
data TASeg
  = -- RootTASeg is a special segment that represents the root of the addr.
    -- It is crucial to distinguish between the absolute addr and the relative addr.
    RootTASeg
  | IndexTASeg !Int
  | BlockTASeg BlockTASeg
  | DisjDefTASeg
  | DisjRegTASeg !Int
  | -- | SubValTASeg is used to represent the only sub value of a value.
    SubValTASeg
  | -- | MutArgTASeg is different in that the seg would be omitted when canonicalizing the addr.
    MutArgTASeg !Int
  | -- | EphemeralTASeg is used to represent the ephemeral value, which can be temporary iteration binding.
    EphemeralTASeg
  deriving (Eq, Ord, Generic, NFData)

instance Show TASeg where
  show RootTASeg = "/"
  show (BlockTASeg s) = show s
  show (IndexTASeg i) = "i" ++ show i
  show DisjDefTASeg = "d*"
  show (DisjRegTASeg i) = "dj" ++ show i
  show (MutArgTASeg i) = "fa" ++ show i
  show SubValTASeg = "sv"
  show EphemeralTASeg = "eph"

data BlockTASeg
  = -- | StringTASeg can be used to match both StringTASeg and LetTASeg, meaning it can be used to query either field or
    -- let binding.
    StringTASeg B.ByteString
  | -- | The first is the ObjectID, the second indicates the i-th value in the constraint.
    PatternTASeg !Int !Int
  | -- | DynFieldTASeg is used to represent a dynamic field.
    -- The first is the ObjectID, the second indicates the i-th in the dynamic field.
    DynFieldTASeg !Int !Int
  | -- | A let binding is always indexed by the LetTASeg.
    LetTASeg
      -- | Identifier
      B.ByteString
  | EmbedTASeg !Int
  deriving (Eq, Ord, Generic, NFData)

instance Show BlockTASeg where
  show (StringTASeg s) = show s
  -- c stands for constraint.
  show (PatternTASeg i j) = "cns_" ++ show i ++ "_" ++ show j
  show (DynFieldTASeg i j) = "dyn_" ++ show i ++ "_" ++ show j
  show (LetTASeg s) = "let_" ++ show s
  show (EmbedTASeg i) = "emb_" ++ show i

getStrFromSeg :: BlockTASeg -> Maybe String
getStrFromSeg (StringTASeg s) = Just (show s)
getStrFromSeg (LetTASeg s) = Just (show s)
getStrFromSeg _ = Nothing

unaryOpTASeg :: TASeg
unaryOpTASeg = MutArgTASeg 0

binOpLeftTASeg :: TASeg
binOpLeftTASeg = MutArgTASeg 0

binOpRightTASeg :: TASeg
binOpRightTASeg = MutArgTASeg 1

toBinOpTASeg :: BinOpDirect -> TASeg
toBinOpTASeg L = binOpLeftTASeg
toBinOpTASeg R = binOpRightTASeg

isSegDisj :: TASeg -> Bool
isSegDisj (DisjRegTASeg _) = True
isSegDisj _ = False

data BinOpDirect = L | R deriving (Eq, Ord)

instance Show BinOpDirect where
  show L = "L"
  show R = "R"

{- | TreeAddr is full addr to a value. The segments are stored in reverse order, meaning the last segment is the first in
the list.
-}
newtype TreeAddr = TreeAddr {getTreeAddrSegs :: V.Vector TASeg}
  deriving (Eq, Ord, Generic, NFData)

instance Show TreeAddr where
  show = showTreeAddr

showTreeAddr :: TreeAddr -> String
showTreeAddr (TreeAddr a)
  | V.null a = "."
  | otherwise =
      if a V.! 0 == RootTASeg
        then "/" ++ intercalate "/" (map show (V.toList $ V.drop 1 a))
        else intercalate "/" $ map show (V.toList a)

emptyTreeAddr :: TreeAddr
emptyTreeAddr = TreeAddr V.empty

rootTreeAddr :: TreeAddr
rootTreeAddr = TreeAddr (V.singleton RootTASeg)

isTreeAddrEmpty :: TreeAddr -> Bool
isTreeAddrEmpty a = V.null (getTreeAddrSegs a)

addrFromList :: [TASeg] -> TreeAddr
addrFromList segs = TreeAddr (V.fromList segs)

-- | This is mostly used for testing purpose.
addrFromStringList :: [String] -> TreeAddr
addrFromStringList segs =
  TreeAddr (V.fromList $ map (\s -> BlockTASeg (StringTASeg (TE.encodeUtf8 (T.pack s)))) segs)

{- | This is mostly used for testing purpose.

Segments are separated by dots, such as "a.b.c".
-}
addrFromString :: String -> TreeAddr
addrFromString s = addrFromStringList (splitOn "." s)

addrToList :: TreeAddr -> [TASeg]
addrToList (TreeAddr a) = V.toList a

appendSeg :: TreeAddr -> TASeg -> TreeAddr
appendSeg (TreeAddr a) seg = TreeAddr (V.snoc a seg)

{- | Append the new addr to old addr.
new and old are reversed, such as [z, y, x] and [b, a]. The appended addr should be [z, y, x, b, a], which is
a.b.x.y.z.
-}
appendTreeAddr ::
  -- | old addr
  TreeAddr ->
  -- | new addr to be appended to the old addr
  TreeAddr ->
  TreeAddr
appendTreeAddr (TreeAddr old) (TreeAddr new) = TreeAddr (old V.++ new)

-- | Get the parent addr of a addr by removing the last segment.
initTreeAddr :: TreeAddr -> Maybe TreeAddr
initTreeAddr (TreeAddr a)
  | V.null a = Nothing
  | otherwise = Just $ TreeAddr (V.init a)

-- | Get the tail addr of a addr, excluding the head segment.
tailTreeAddr :: TreeAddr -> Maybe TreeAddr
tailTreeAddr (TreeAddr a)
  | V.null a = Nothing
  | otherwise = Just $ TreeAddr (V.tail a)

-- | Get the last segment of a addr.
lastSeg :: TreeAddr -> Maybe TASeg
lastSeg (TreeAddr a)
  | V.null a = Nothing
  | otherwise = Just $ V.last a

-- | Get the head segment of a addr.
headSeg :: TreeAddr -> Maybe TASeg
headSeg (TreeAddr a)
  | V.null a = Nothing
  | otherwise = Just $ V.head a

-- | Check if addr x is a prefix of addr y.
isPrefix ::
  -- | x
  TreeAddr ->
  -- | y
  TreeAddr ->
  Bool
isPrefix (TreeAddr x) (TreeAddr y) = V.length x <= V.length y && V.and (V.zipWith eq x y)
 where
  eq = {-# SCC "isPrefix-eq" #-} (==)

-- isPrefix (TreeAddr x) (TreeAddr y) = V.length x <= V.length y && x == V.take (V.length x) y

{- | Trim the address by cutting off the prefix.

If the second addr is not a prefix of the first addr or the first addr is shorter than the second addr, then the
first addr is returned.
-}
trimPrefixTreeAddr ::
  -- | prefix address
  TreeAddr ->
  -- | address
  TreeAddr ->
  TreeAddr
trimPrefixTreeAddr pre@(TreeAddr pa) x@(TreeAddr xa)
  | not (isPrefix pre x) = x
  | otherwise = TreeAddr (V.drop (V.length pa) xa)

isInDisj :: TreeAddr -> Bool
isInDisj (TreeAddr xs) = any isSegDisj xs

-- | Convert the addr to referable form which only contains string, int or root segments.
trimToReferable :: TreeAddr -> TreeAddr
trimToReferable (TreeAddr xs) = TreeAddr $ V.filter isSegReferable xs

{- | Get the referable address.

Referable address is the address that a value can be referred to in the CUE code. If the address contains any mutable
arg segment, then the address is not referable.
-}
getReferableAddr :: TreeAddr -> Maybe TreeAddr
getReferableAddr p =
  if not (all isSegReferable (getTreeAddrSegs p))
    then Nothing
    else Just p

isSegReferable :: TASeg -> Bool
isSegReferable (BlockTASeg (getStrFromSeg -> Just _)) = True
isSegReferable (IndexTASeg _) = True
isSegReferable RootTASeg = True
isSegReferable _ = False
