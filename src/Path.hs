{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}

module Path where

import Control.DeepSeq (NFData (..))
import Control.Monad.State (MonadState)
import Data.List (intercalate)
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)
import StringIndex

data Selector = StringSel TextIndex | IntSel !Int
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
fieldPathToAddr (FieldPath sels) =
  let xs = map selToTASeg sels
   in addrFromList xs

selToTASeg :: Selector -> TASeg
selToTASeg (StringSel s) = BlockTASeg (StringTASeg s)
selToTASeg (IntSel i) = IndexTASeg i

-- fieldPathFromString :: String -> FieldPath
-- fieldPathFromString s =
--   FieldPath
--     { getRefSels =
--         map
--           ( \x ->
--               case reads x of
--                 [(i, "")] -> IntSel i
--                 _ -> StringSel (TE.encodeUtf8 (T.pack x))
--           )
--           (splitOn "." s)
--     }

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
  deriving (Eq, Ord, Generic, NFData)

-- showTASeg :: (MonadState s m, HasTextIndexer s) => TASeg -> m String
instance Show TASeg where
  show RootTASeg = "/"
  show (BlockTASeg s) = show s
  show (IndexTASeg i) = "i" ++ show i
  show (DisjTASeg i) = "dj" ++ show i
  show (MutArgTASeg i) = "fa" ++ show i
  show TempTASeg = "tmp"

instance ShowWithTextIndexer TASeg where
  tshow (BlockTASeg s) = tshow s
  tshow s = return $ show s

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

data BlockTASeg
  = StringTASeg !TextIndex
  | LetTASeg !TextIndex (Maybe Int)
  | -- | The first is the ObjectID, the second indicates the i-th value in the constraint.
    PatternTASeg !Int !Int
  | -- | DynFieldTASeg is used to represent a dynamic field.
    -- The first is the ObjectID, the second indicates the i-th in the dynamic field.
    DynFieldTASeg !Int !Int
  | StubFieldTASeg !TextIndex
  deriving (Eq, Ord, Generic, NFData)

instance Show BlockTASeg where
  show (PatternTASeg i j) = "cns_" ++ show i ++ "_" ++ show j
  show (DynFieldTASeg i j) = "dyn_" ++ show i ++ "_" ++ show j
  show (StubFieldTASeg s) = "__" ++ show s
  show (StringTASeg s) = show s
  show (LetTASeg s m) = "let_" ++ show s ++ maybe "" (\i -> "_" ++ show i) m

instance ShowWithTextIndexer BlockTASeg where
  tshow (StubFieldTASeg s) = do
    str <- tshow s
    return $ "__" ++ str
  tshow (StringTASeg s) = tshow s
  tshow (LetTASeg s m) = do
    str <- tshow s
    return $ "let_" ++ str ++ maybe "" (\i -> "_" ++ show i) m
  tshow s = return $ show s

-- toJSONBlockTASeg :: (MonadState s m, HasTextIndexer s) => BlockTASeg -> m Value
-- toJSONBlockTASeg seg = do
--   str <- showBlockTASeg seg
--   return $ toJSON str

tIdxToStringTASeg :: TextIndex -> TASeg
tIdxToStringTASeg s = BlockTASeg (StringTASeg s)

textToStringTASeg :: (MonadState s m, HasTextIndexer s) => T.Text -> m TASeg
textToStringTASeg s = tIdxToStringTASeg <$> textToTextIndex s

strToStringTASeg :: (MonadState s m, HasTextIndexer s) => String -> m TASeg
strToStringTASeg s = textToStringTASeg (T.pack s)

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
  deriving (Show, Eq, Ord, Generic, NFData)

instance ShowWithTextIndexer TreeAddr where
  tshow (TreeAddr a)
    | V.null a = return "."
    | a V.! 0 == RootTASeg = do
        x <- mapM tshow (V.toList $ V.drop 1 a)
        return $ "/" ++ intercalate "/" x
    | otherwise = do
        x <- mapM tshow (V.toList a)
        return $ intercalate "/" x

emptyTreeAddr :: TreeAddr
emptyTreeAddr = TreeAddr V.empty

rootTreeAddr :: TreeAddr
rootTreeAddr = TreeAddr (V.singleton RootTASeg)

isTreeAddrEmpty :: TreeAddr -> Bool
isTreeAddrEmpty a = V.null (getTreeAddrSegs a)

addrFromList :: [TASeg] -> TreeAddr
addrFromList segs = TreeAddr (V.fromList segs)

-- | This is mostly used for testing purpose.
addrFromStringList :: (MonadState s m, HasTextIndexer s) => [String] -> m TreeAddr
addrFromStringList segs = do
  xs <- mapM strToStringTASeg segs
  return $ TreeAddr (V.fromList xs)

-- {- | This is mostly used for testing purpose.

-- Segments are separated by dots, such as "a.b.c".
-- -}
-- addrFromString :: String -> TreeAddr
-- addrFromString s = addrFromStringList (splitOn "." s)

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
  deriving (Show, Eq, Ord, Generic, NFData)

instance ShowWithTextIndexer SuffixIrredAddr where
  tshow a = tshow $ sufIrredToAddr a

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
  deriving (Show, Eq, Ord, Generic, NFData)

instance ShowWithTextIndexer SuffixReferableAddr where
  tshow a = tshow $ sufRefToAddr a

sufRefToAddr :: SuffixReferableAddr -> TreeAddr
sufRefToAddr (SuffixReferableAddr xs) = TreeAddr xs

sufRefToSufIrred :: SuffixReferableAddr -> SuffixIrredAddr
sufRefToSufIrred (SuffixReferableAddr xs) = SuffixIrredAddr xs

addrIsSufRef :: TreeAddr -> Maybe SuffixReferableAddr
addrIsSufRef (TreeAddr xs)
  | V.null xs = Just $ SuffixReferableAddr V.empty
  | isSegReferable (V.last xs) = Just $ SuffixReferableAddr xs
  | otherwise = Nothing
