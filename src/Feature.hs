{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Feature where

import Control.DeepSeq (NFData (..))
import Control.Monad.State (MonadState)
import Data.Bits (Bits (..))
import Data.List (intercalate)
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import StringIndex
import Text.Printf (printf)

data Selector = StringSel !TextIndex | IntSel !Int
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

-- appendFieldPaths ::
--   -- | front
--   FieldPath ->
--   -- | back
--   FieldPath ->
--   FieldPath
-- appendFieldPaths (FieldPath xs) (FieldPath ys) = FieldPath (xs ++ ys)

isFieldPathEmpty :: FieldPath -> Bool
isFieldPathEmpty (FieldPath []) = True
isFieldPathEmpty _ = False

fieldPathToAddr :: FieldPath -> TreeAddr
fieldPathToAddr (FieldPath sels) =
  let xs = map selToTASeg sels
   in addrFromList xs

selToTASeg :: Selector -> Feature
selToTASeg (StringSel s) = mkStringFeature s
selToTASeg (IntSel i) = mkListIdxFeature i

newtype Feature = Feature Int
  deriving (Eq, Ord, Generic, NFData)

data LabelType
  = RootLabelType
  | ListStoreIdxLabelType
  | ListIdxLabelType
  | DisjLabelType
  | MutArgLabelType
  | TempLabelType
  | StringLabelType
  | LetLabelType
  | PatternLabelType
  | DynFieldLabelType
  | StubFieldLabelType
  deriving (Eq, Ord, Generic, NFData, Enum)

instance Show Feature where
  show f = case fetchLabelType f of
    RootLabelType -> "/"
    ListStoreIdxLabelType -> "lsi" ++ show (fetchIndex f)
    ListIdxLabelType -> "li" ++ show (fetchIndex f)
    DisjLabelType -> "dj" ++ show (fetchIndex f)
    MutArgLabelType -> "fa" ++ show (fetchIndex f)
    TempLabelType -> "tmp"
    StringLabelType -> "str_" ++ show (fetchIndex f)
    LetLabelType -> "let_" ++ show (fetchIndex f)
    PatternLabelType -> "cns_" ++ show (fetchIndex f)
    DynFieldLabelType -> "dyn_" ++ show (fetchIndex f)
    StubFieldLabelType -> "__" ++ show (fetchIndex f)

instance ShowWithTextIndexer Feature where
  tshow f = case fetchLabelType f of
    StubFieldLabelType -> do
      str <- tshow (TextIndex (fetchIndex f))
      return $ T.pack $ printf "__%s" str
    StringLabelType -> tshow (TextIndex (fetchIndex f))
    LetLabelType -> do
      str <- tshow (TextIndex (fetchIndex f))
      return $ T.pack $ printf "let_%s" str
    _ -> return $ T.pack $ show f

pattern FeatureType :: LabelType -> Feature
pattern FeatureType lType <- (fetchLabelType -> lType)

pattern IsRootFeature :: Feature
pattern IsRootFeature <- (fetchLabelType -> RootLabelType)

fetchLabelType :: Feature -> LabelType
fetchLabelType (Feature f) = toEnum $ (f `shiftR` 24) .&. 0x000000FF

fetchIndex :: Feature -> Int
fetchIndex (Feature f) = f .&. 0x00FFFFFF

-- | TODO: document the bit layout.
mkFeature :: Int -> LabelType -> Feature
mkFeature i lType = Feature $ (fromEnum lType `shiftL` 24) .|. (i .&. 0x00FFFFFF)

mkStringFeature :: TextIndex -> Feature
mkStringFeature (TextIndex i) = mkFeature i StringLabelType

mkMutArgFeature :: Int -> Feature
mkMutArgFeature i = mkFeature i MutArgLabelType

mkListStoreIdxFeature :: Int -> Feature
mkListStoreIdxFeature i = mkFeature i ListStoreIdxLabelType

mkListIdxFeature :: Int -> Feature
mkListIdxFeature i = mkFeature i ListIdxLabelType

mkDisjFeature :: Int -> Feature
mkDisjFeature i = mkFeature i DisjLabelType

{- | The first is the ObjectID, the second indicates the i-th in the dynamic field.

The selector is shifted left by 23 bits to make room for larger object IDs.
-}
mkDynFieldFeature :: Int -> Int -> Feature
mkDynFieldFeature objID selector = mkFeature combined DynFieldLabelType
 where
  shiftedSelector = selector `shiftL` 23
  combined = objID .|. shiftedSelector

mkPatternFeature :: Int -> Int -> Feature
mkPatternFeature objID selector = mkFeature combined PatternLabelType
 where
  shiftedSelector = selector `shiftL` 23
  combined = objID .|. shiftedSelector

mkLetFeature :: (TextIndexerMonad s m) => TextIndex -> Maybe Int -> m Feature
mkLetFeature (TextIndex i) Nothing = return $ mkFeature i LetLabelType
mkLetFeature (TextIndex i) (Just j) = modifyLetFeature j (mkFeature i LetLabelType)

modifyLetFeature :: (TextIndexerMonad s m) => Int -> Feature -> m Feature
modifyLetFeature oid f = do
  t <- tshow (getTextIndexFromFeature f)
  -- "." is not a valid character in identifier, so we use it to separate the let name and the index.
  case T.findIndex (== '.') t of
    Just dotIdx ->
      let prefix = T.take dotIdx t
       in append prefix
    Nothing -> append t
 where
  append prefix = do
    let str = T.unpack prefix ++ "." ++ show oid
    (TextIndex k) <- textToTextIndex (T.pack str)
    return $ mkFeature k LetLabelType

mkStubFieldFeature :: TextIndex -> Feature
mkStubFieldFeature (TextIndex i) = mkFeature i StubFieldLabelType

getTextFromFeature :: (TextIndexerMonad s m) => Feature -> m T.Text
getTextFromFeature f = case fetchLabelType f of
  StringLabelType -> tshow (TextIndex (fetchIndex f))
  LetLabelType -> tshow (TextIndex (fetchIndex f))
  StubFieldLabelType -> tshow (TextIndex (fetchIndex f))
  _ -> error $ "Feature does not have a text: " ++ show f

getTextIndexFromFeature :: (HasCallStack) => Feature -> TextIndex
getTextIndexFromFeature f = case fetchLabelType f of
  StringLabelType -> TextIndex (fetchIndex f)
  LetLabelType -> TextIndex (fetchIndex f)
  StubFieldLabelType -> TextIndex (fetchIndex f)
  _ -> error $ printf "Feature %s does not have a TextIndex" (show f)

getPatternIndexesFromFeature :: Feature -> (Int, Int)
getPatternIndexesFromFeature f = case fetchLabelType f of
  PatternLabelType ->
    let combined = fetchIndex f
        objID = combined .&. 0x007FFFFF -- lower 23 bits
        selector = (combined `shiftR` 23) .&. 1 -- next bit
     in (objID, selector)
  _ -> error $ "Feature is not a PatternLabelType: " ++ show f

getDynFieldIndexesFromFeature :: Feature -> (Int, Int)
getDynFieldIndexesFromFeature f = case fetchLabelType f of
  DynFieldLabelType ->
    let combined = fetchIndex f
        objID = combined .&. 0x007FFFFF -- lower 23 bits
        selector = (combined `shiftR` 23) .&. 1 -- next bit
     in (objID, selector)
  _ -> error $ "Feature is not a DynFieldLabelType: " ++ show f

isFeatureReducible :: Feature -> Bool
isFeatureReducible f = case fetchLabelType f of
  MutArgLabelType -> True
  DisjLabelType -> True
  _ -> False

isFeatureIrreducible :: Feature -> Bool
isFeatureIrreducible f = not $ isFeatureReducible f

isFeatureReferable :: Feature -> Bool
isFeatureReferable f = case fetchLabelType f of
  StringLabelType -> True
  LetLabelType -> True
  ListIdxLabelType -> True
  RootLabelType -> True
  _ -> False

textToStringFeature :: (MonadState s m, HasTextIndexer s) => T.Text -> m Feature
textToStringFeature s = mkStringFeature <$> textToTextIndex s

strToStringFeature :: (MonadState s m, HasTextIndexer s) => String -> m Feature
strToStringFeature s = textToStringFeature (T.pack s)

unaryOpTASeg :: Feature
unaryOpTASeg = mkMutArgFeature 0

binOpLeftTASeg :: Feature
binOpLeftTASeg = mkMutArgFeature 0

binOpRightTASeg :: Feature
binOpRightTASeg = mkMutArgFeature 1

toBinOpTASeg :: BinOpDirect -> Feature
toBinOpTASeg L = binOpLeftTASeg
toBinOpTASeg R = binOpRightTASeg

rootFeature :: Feature
rootFeature = mkFeature 0 RootLabelType

tempFeature :: Feature
tempFeature = mkFeature 0 TempLabelType

data BinOpDirect = L | R deriving (Eq, Ord)

instance Show BinOpDirect where
  show L = "L"
  show R = "R"

{- | TreeAddr is full addr to a value. The segments are stored in reverse order, meaning the last segment is the first in
the list.
-}
newtype TreeAddr = TreeAddr {getFeatures :: V.Vector Feature}
  deriving (Show, Eq, Ord, Generic, NFData)

instance ShowWithTextIndexer TreeAddr where
  tshow (TreeAddr a)
    | V.null a = return "."
    | a V.! 0 == rootFeature = do
        x <- mapM (\x -> T.unpack <$> tshow x) (V.toList $ V.drop 1 a)
        return $ T.pack $ "/" ++ intercalate "/" x
    | otherwise = do
        x <- mapM (\x -> T.unpack <$> tshow x) (V.toList a)
        return $ T.pack $ intercalate "/" x

emptyTreeAddr :: TreeAddr
emptyTreeAddr = TreeAddr V.empty

rootTreeAddr :: TreeAddr
rootTreeAddr = TreeAddr (V.singleton rootFeature)

isTreeAddrEmpty :: TreeAddr -> Bool
isTreeAddrEmpty a = V.null (getFeatures a)

addrFromList :: [Feature] -> TreeAddr
addrFromList segs = TreeAddr (V.fromList segs)

-- | This is mostly used for testing purpose.
addrFromStringList :: (MonadState s m, HasTextIndexer s) => [String] -> m TreeAddr
addrFromStringList segs = do
  xs <- mapM strToStringFeature segs
  return $ TreeAddr (V.fromList xs)

addrToList :: TreeAddr -> [Feature]
addrToList (TreeAddr a) = V.toList a

appendSeg :: TreeAddr -> Feature -> TreeAddr
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
lastSeg :: TreeAddr -> Maybe Feature
lastSeg (TreeAddr a)
  | V.null a = Nothing
  | otherwise = Just $ V.last a

-- | Get the head segment of a addr.
headSeg :: TreeAddr -> Maybe Feature
headSeg (TreeAddr a)
  | V.null a = Nothing
  | otherwise = Just $ V.head a

{- | Check if addr x is a prefix of addr y.

For example, isPrefix (a.b) (a.b.c.d) = True, isPrefix (a.b.c) (a.b) = False.
-}
isPrefix :: TreeAddr -> TreeAddr -> Bool
isPrefix (TreeAddr x) (TreeAddr y) = isSegVPrefix x y

isSegVPrefix :: V.Vector Feature -> V.Vector Feature -> Bool
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
newtype SuffixIrredAddr = SuffixIrredAddr {getSuffixIrredAddr :: V.Vector Feature}
  deriving (Show, Eq, Ord, Generic, NFData)

instance ShowWithTextIndexer SuffixIrredAddr where
  tshow a = tshow $ sufIrredToAddr a

addrIsSufIrred :: TreeAddr -> Maybe SuffixIrredAddr
addrIsSufIrred (TreeAddr xs)
  | V.null xs = Just $ SuffixIrredAddr V.empty
  | isFeatureIrreducible (V.last xs) = Just $ SuffixIrredAddr xs
  | otherwise = Nothing

addMustBeSufIrred :: (HasCallStack) => TreeAddr -> SuffixIrredAddr
addMustBeSufIrred addr = case addrIsSufIrred addr of
  Just sufIrred -> sufIrred
  Nothing -> error $ printf "Addr %s is not suffix irreducible" (show addr)

trimAddrToSufIrred :: TreeAddr -> SuffixIrredAddr
trimAddrToSufIrred (TreeAddr xs) =
  let
    revXs = V.reverse xs
    revNonMutArgs = V.dropWhile isFeatureReducible revXs
   in
    SuffixIrredAddr $ V.reverse revNonMutArgs

sufIrredToAddr :: SuffixIrredAddr -> TreeAddr
sufIrredToAddr (SuffixIrredAddr xs) = TreeAddr xs

sufIrredIsSufRef :: SuffixIrredAddr -> Maybe SuffixReferableAddr
sufIrredIsSufRef (SuffixIrredAddr xs)
  | V.null xs = Just $ SuffixReferableAddr V.empty
  | isFeatureReferable (V.last xs) = Just $ SuffixReferableAddr xs
  | otherwise = Nothing

initSufIrred :: SuffixIrredAddr -> Maybe SuffixIrredAddr
initSufIrred (SuffixIrredAddr xs)
  | V.null xs = Nothing
  | otherwise = Just $ SuffixIrredAddr (V.init xs)

{- | Trim the addr to the suffix referable addr.
trimAddrToSufRef :: TreeAddr -> SuffixReferableAddr
trimAddrToSufRef (TreeAddr xs) = SuffixReferableAddr (V.slice 0 trimmedLen xs)
 where
  -- Use fusion to find the trim size.
  trimmedLen = V.length (V.dropWhile (not . isFeatureReferable) (V.reverse xs))
-}
trimAddrToSufRef :: TreeAddr -> SuffixReferableAddr
trimAddrToSufRef (TreeAddr xs) =
  let len = V.length xs
      trimmedLen = go (len - 1)
       where
        go i
          | i < 0 = 0
          | isFeatureReferable (xs V.! i) = i + 1
          | otherwise = go (i - 1)
   in SuffixReferableAddr (V.slice 0 trimmedLen xs)

newtype SuffixReferableAddr = SuffixReferableAddr {getReferableAddr :: V.Vector Feature}
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
  | isFeatureReferable (V.last xs) = Just $ SuffixReferableAddr xs
  | otherwise = Nothing
