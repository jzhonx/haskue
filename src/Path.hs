{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}

module Path where

import Control.DeepSeq (NFData (..))
import Data.Aeson (ToJSON)
import Data.Aeson.Types (ToJSON (..))
import qualified Data.ByteString as B
import Data.List (intercalate)
import Data.List.Split (splitOn)
import Data.Text (unpack)
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
selToTASeg (StringSel s) = textToStringTASeg (TE.decodeUtf8 s)
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
  | DisjTASeg !Int
  | -- | MutArgTASeg is different in that the seg would be omitted when canonicalizing the addr.
    MutArgTASeg !Int
  | TempTASeg
  deriving (Eq, Ord, Generic, NFData, ToJSON)

instance Show TASeg where
  show RootTASeg = "/"
  show (BlockTASeg s) = show s
  show (IndexTASeg i) = "i" ++ show i
  show (DisjTASeg i) = "dj" ++ show i
  show (MutArgTASeg i) = "fa" ++ show i
  show TempTASeg = "tmp"

isSegReducible :: TASeg -> Bool
isSegReducible (MutArgTASeg _) = True
isSegReducible (DisjTASeg _) = True
isSegReducible _ = False

isSegIrreducible :: TASeg -> Bool
isSegIrreducible seg = not $ isSegReducible seg

isSegReferable :: TASeg -> Bool
isSegReferable (BlockTASeg (StringTASeg _)) = True
isSegReferable (BlockTASeg (LetTASeg{})) = True
isSegReferable (IndexTASeg _) = True
isSegReferable RootTASeg = True
isSegReferable _ = False

newtype StringSeg = StringSeg B.ByteString
  deriving (Eq, Ord, Generic, NFData)

instance Show StringSeg where
  show (StringSeg s) = unpack $ stringSegToText (StringSeg s)

instance ToJSON StringSeg where
  toJSON (StringSeg s) = toJSON $ show s

stringSegToText :: StringSeg -> T.Text
stringSegToText (StringSeg s) = TE.decodeUtf8 s

textToStringSeg :: T.Text -> StringSeg
textToStringSeg t = StringSeg (TE.encodeUtf8 t)

data BlockTASeg
  = StringTASeg StringSeg
  | LetTASeg StringSeg (Maybe Int)
  | -- | The first is the ObjectID, the second indicates the i-th value in the constraint.
    PatternTASeg !Int !Int
  | -- | DynFieldTASeg is used to represent a dynamic field.
    -- The first is the ObjectID, the second indicates the i-th in the dynamic field.
    DynFieldTASeg !Int !Int
  | StubFieldTASeg StringSeg
  deriving (Eq, Ord, Generic, NFData)

instance Show BlockTASeg where
  show (PatternTASeg i j) = "cns_" ++ show i ++ "_" ++ show j
  show (DynFieldTASeg i j) = "dyn_" ++ show i ++ "_" ++ show j
  show (StubFieldTASeg s) = "__" ++ show s
  show (StringTASeg s) = show s
  show (LetTASeg s m) = "let_" ++ show s ++ maybe "" (\i -> "_" ++ show i) m

instance ToJSON BlockTASeg where
  toJSON seg = toJSON $ show seg

strToStringTASeg :: String -> TASeg
strToStringTASeg s = textToStringTASeg (T.pack s)

textToStringTASeg :: T.Text -> TASeg
textToStringTASeg s = BlockTASeg $ StringTASeg $ textToStringSeg s

unaryOpTASeg :: TASeg
unaryOpTASeg = MutArgTASeg 0

binOpLeftTASeg :: TASeg
binOpLeftTASeg = MutArgTASeg 0

binOpRightTASeg :: TASeg
binOpRightTASeg = MutArgTASeg 1

toBinOpTASeg :: BinOpDirect -> TASeg
toBinOpTASeg L = binOpLeftTASeg
toBinOpTASeg R = binOpRightTASeg

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

instance ToJSON TreeAddr where
  toJSON addr = toJSON $ show addr

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
  TreeAddr (V.fromList $ map strToStringTASeg segs)

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
isPrefix :: TreeAddr -> TreeAddr -> Bool
isPrefix (TreeAddr x) (TreeAddr y) = isSegVPrefix x y

isSegVPrefix :: V.Vector TASeg -> V.Vector TASeg -> Bool
isSegVPrefix x y = V.length x <= V.length y && V.and (V.zipWith (==) x y)

-- isPrefix (TreeAddr x) (TreeAddr y) = V.length x <= V.length y && x == V.take (V.length x) y

{- | Trim the address by cutting off the prefix.

If the second addr is not a prefix of the first addr or the first addr is shorter than the second addr, then the
first addr is returned.
-}
trimPrefixTreeAddr :: TreeAddr -> TreeAddr -> TreeAddr
trimPrefixTreeAddr pre@(TreeAddr pa) x@(TreeAddr xa)
  | not (isPrefix pre x) = x
  | otherwise = TreeAddr (V.drop (V.length pa) xa)

{- | SuffixIrredAddr is an addr that ends with an irreducible segment.

Besides referrable segments, irreducible segments include dynamic field segments and pattern segments, etc..
-}
newtype SuffixIrredAddr = SuffixIrredAddr {getSuffixIrredAddr :: V.Vector TASeg}
  deriving (Eq, Ord, Generic, NFData)

instance Show SuffixIrredAddr where
  show a = show $ sufIrredToAddr a

addrIsSufIrred :: TreeAddr -> Maybe SuffixIrredAddr
addrIsSufIrred (TreeAddr xs)
  | V.null xs = Just $ SuffixIrredAddr V.empty
  | isSegIrreducible (V.last xs) = Just $ SuffixIrredAddr xs
  | otherwise = Nothing

trimAddrToSufIrred :: TreeAddr -> SuffixIrredAddr
trimAddrToSufIrred (TreeAddr xs) =
  let
    revXs = V.reverse xs
    revNonMutArgs = V.dropWhile isSegReducible revXs
   in
    SuffixIrredAddr $ V.reverse revNonMutArgs

sufIrredToAddr :: SuffixIrredAddr -> TreeAddr
sufIrredToAddr (SuffixIrredAddr xs) = TreeAddr xs

sufIrredIsSufRef :: SuffixIrredAddr -> Maybe SuffixReferableAddr
sufIrredIsSufRef (SuffixIrredAddr xs)
  | V.null xs = Just $ SuffixReferableAddr V.empty
  | isSegReferable (V.last xs) = Just $ SuffixReferableAddr xs
  | otherwise = Nothing

initSufIrred :: SuffixIrredAddr -> Maybe SuffixIrredAddr
initSufIrred (SuffixIrredAddr xs)
  | V.null xs = Nothing
  | otherwise = Just $ SuffixIrredAddr (V.init xs)

trimAddrToSufRef :: TreeAddr -> SuffixReferableAddr
trimAddrToSufRef (TreeAddr xs) =
  let
    revXs = V.reverse xs
    revYs = V.dropWhile (not . isSegReferable) revXs
   in
    SuffixReferableAddr $ V.reverse revYs

newtype SuffixReferableAddr = SuffixReferableAddr {getReferableAddr :: V.Vector TASeg}
  deriving (Eq, Ord, Generic, NFData)

instance Show SuffixReferableAddr where
  show a = show $ sufRefToAddr a

sufRefToAddr :: SuffixReferableAddr -> TreeAddr
sufRefToAddr (SuffixReferableAddr xs) = TreeAddr xs

sufRefToSufIrred :: SuffixReferableAddr -> SuffixIrredAddr
sufRefToSufIrred (SuffixReferableAddr xs) = SuffixIrredAddr xs

addrIsSufRef :: TreeAddr -> Maybe SuffixReferableAddr
addrIsSufRef (TreeAddr xs)
  | V.null xs = Just $ SuffixReferableAddr V.empty
  | isSegReferable (V.last xs) = Just $ SuffixReferableAddr xs
  | otherwise = Nothing
