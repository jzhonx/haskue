{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Feature where

import Control.DeepSeq (NFData (..))
import Control.Monad.State (MonadState)
import Data.Aeson (ToJSON, toJSON)
import Data.Aeson.Types (ToJSONKey)
import Data.Bits (Bits (..))
import qualified Data.ByteString.Char8 as BC
import Data.Hashable (Hashable (..))
import Data.List (intercalate)
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import StringIndex
import Text.Printf (printf)

data Selector = StringSel !TextIndex | IntSel !Int
  deriving (Eq, Ord, Generic, NFData)

{- Selectors is a list of selectors.

The selectors are not stored in reverse order.
-}
newtype Selectors = Selectors {getSelectors :: [Selector]}
  deriving (Eq, Ord, Generic, NFData)

instance Show Selector where
  show (StringSel s) = show s
  show (IntSel i) = show i

instance Show Selectors where
  show :: Selectors -> String
  show (Selectors sels) = intercalate "." (map show sels)

instance ShowWTIndexer Selector where
  tshow (StringSel s) = tshow s
  tshow (IntSel i) = return $ T.pack $ show i

emptyFieldPath :: Selectors
emptyFieldPath = Selectors []

headSel :: Selectors -> Maybe Selector
headSel (Selectors []) = Nothing
headSel (Selectors sels) = Just $ sels !! 0

tailFieldPath :: Selectors -> Maybe Selectors
tailFieldPath (Selectors []) = Nothing
tailFieldPath (Selectors sels) = Just $ Selectors (tail sels)

isFieldPathEmpty :: Selectors -> Bool
isFieldPathEmpty (Selectors []) = True
isFieldPathEmpty _ = False

-- | TODO: can be just a list of features
fieldPathToAddr :: Selectors -> ValAddr
fieldPathToAddr (Selectors sels) =
  let xs = map selToTASeg sels
   in addrFromList xs

selToTASeg :: Selector -> Feature
selToTASeg (StringSel s) = mkStringFeature s
selToTASeg (IntSel i) = mkListIdxFeature i

newtype Feature = Feature {getFeature :: Int}
  deriving (Eq, Ord, Generic, NFData, Hashable)

data LabelType
  = FileTopLabelType
  | UniversalLabelType
  | PackageLabelType
  | ListStoreIdxLabelType
  | ListIdxLabelType
  | DisjLabelType
  | OpArgLabelType
  | StringLabelType
  | LetLabelType
  | PatternLabelType
  | DynFieldLabelType
  | EmbedValueLabelType
  | ObjectLabelType -- ObjectLabelType indicates an object value that is in the sub structure of a value.
  | ConstraintLabelType
  | DynCnstrLabelType
  deriving (Eq, Ord, Generic, NFData, Enum)

instance Show Feature where
  show f = case fetchLabelType f of
    FileTopLabelType -> "/top"
    UniversalLabelType -> "/builtin"
    PackageLabelType -> "/pkg"
    ListStoreIdxLabelType -> "lsi" ++ show (fetchIndex f)
    ListIdxLabelType -> "li" ++ show (fetchIndex f)
    DisjLabelType -> "dj" ++ show (fetchIndex f)
    OpArgLabelType -> "fa" ++ show (fetchIndex f)
    StringLabelType -> "str_" ++ show (fetchIndex f)
    LetLabelType -> "let_" ++ show (fetchIndex f)
    PatternLabelType -> "cns_" ++ showSub (getPatternIndexesFromFeature f) show
    DynFieldLabelType -> "dyn_" ++ showSub (getDynFieldIndexesFromFeature f) show
    EmbedValueLabelType -> "embedv"
    ObjectLabelType -> "o_" ++ show (fetchIndex f)
    ConstraintLabelType -> "c_" ++ show (fetchIndex f)
    DynCnstrLabelType -> "dc_" ++ show (fetchIndex f)
   where
    showSub :: (Int, a) -> (a -> String) -> String
    showSub (x, y) g = show x ++ "_" ++ g y

instance ShowWTIndexer Feature where
  tshow f = case fetchLabelType f of
    FileTopLabelType -> do
      t <- tshow (TextIndex (fetchIndex f))
      return $ "/" `T.append` t
    StringLabelType -> tshow (TextIndex (fetchIndex f))
    LetLabelType -> do
      str <- tshow (TextIndex (fetchIndex f))
      return $ T.pack $ printf "let_%s" str
    _ -> return $ T.pack $ show f

pattern FeatureType :: LabelType -> Feature
pattern FeatureType lType <- (fetchLabelType -> lType)

fetchLabelType :: Feature -> LabelType
fetchLabelType (Feature f) = toEnum $ (f `shiftR` 24) .&. 0x000000FF

fetchIndex :: Feature -> Int
fetchIndex (Feature f) = f .&. 0x00FFFFFF

-- | TODO: document the bit layout.
mkFeature :: Int -> LabelType -> Feature
mkFeature i lType = Feature $ (fromEnum lType `shiftL` 24) .|. (i .&. 0x00FFFFFF)

mkStringFeature :: TextIndex -> Feature
mkStringFeature (TextIndex i) = mkFeature i StringLabelType

mkListStoreIdxFeature :: Int -> Feature
mkListStoreIdxFeature i = mkFeature i ListStoreIdxLabelType

mkListIdxFeature :: Int -> Feature
mkListIdxFeature i = mkFeature i ListIdxLabelType

mkDisjFeature :: Int -> Feature
mkDisjFeature i = mkFeature i DisjLabelType

-- | The second argument indicates whether it is a unify operator or not.
mkOpArgFeature :: Int -> Feature
mkOpArgFeature index = mkFeature index OpArgLabelType

data CnstrType
  = RegCnstrT
  | PatternCnstrT
  deriving (Eq, Ord, Enum)

mkConstraintFeature :: Int -> CnstrType -> Int -> Feature
mkConstraintFeature i cnstrType selector = mkFeature combined ConstraintLabelType
 where
  -- The bitmap:
  --  0-18: index
  --  19-21: cnstrType
  --  22-23: selector
  -- The constrType has 8 possible values, so we can use 3 bits to store it.
  cnstrTypeBits = fromEnum cnstrType `shiftL` 19
  -- Selector has maximum 4 possible values, so we can use 2 bits to store it.
  selectorBits = selector .&. 0x00000003 `shiftL` 22
  shiftedSelector = selectorBits .|. cnstrTypeBits
  combined = i .|. shiftedSelector

mkRegCnstrFeature :: Int -> Feature
mkRegCnstrFeature i = mkConstraintFeature i RegCnstrT 0

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

mkLetFeature :: TextIndex -> Feature
mkLetFeature (TextIndex i) = mkFeature i LetLabelType

modifyLetFeature :: (TextIndexerMonad s m) => Int -> Feature -> m Feature
modifyLetFeature oid f = do
  (TextIndex k) <- modifyTISuffix oid (getTextIndexFromFeature f)
  return $ mkFeature k LetLabelType

modifyTISuffix :: (TextIndexerMonad s m) => Int -> TextIndex -> m TextIndex
modifyTISuffix oid ti = do
  b <- textIndexToBS ti
  -- "." is not a valid character in identifier, so we use it to separate the let name and the index.
  case BC.findIndex (== '.') b of
    Just dotIdx ->
      let prefix = BC.take dotIdx b
       in append prefix
    Nothing -> append b
 where
  append prefix = do
    let str = BC.unpack prefix ++ "." ++ show oid
    strToTextIndex str

removeTISuffix :: (TextIndexerMonad s m) => TextIndex -> m TextIndex
removeTISuffix ti = do
  b <- textIndexToBS ti
  case BC.findIndex (== '.') b of
    Just dotIdx -> textToTextIndex (BC.take dotIdx b)
    Nothing -> return ti

mkEmbedValueFeature :: Feature
mkEmbedValueFeature = mkFeature 0 EmbedValueLabelType

mkDynCnstrFeature :: Int -> Feature
mkDynCnstrFeature i = mkFeature i DynCnstrLabelType

mkObjectFeature :: Int -> Feature
mkObjectFeature i = mkFeature i ObjectLabelType

getTextFromFeature :: (TextIndexerMonad s m) => Feature -> m BC.ByteString
getTextFromFeature f = case fetchLabelType f of
  StringLabelType -> textIndexToBS (TextIndex (fetchIndex f))
  LetLabelType -> textIndexToBS (TextIndex (fetchIndex f))
  _ -> error $ "Feature does not have a text: " ++ show f

getTextIndexFromFeature :: (HasCallStack) => Feature -> TextIndex
getTextIndexFromFeature f = case fetchLabelType f of
  StringLabelType -> TextIndex (fetchIndex f)
  LetLabelType -> TextIndex (fetchIndex f)
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

isFeatureConstraint :: Feature -> Bool
isFeatureConstraint f = case fetchLabelType f of
  ConstraintLabelType -> True
  _ -> False

isFeatureIrreducible :: Feature -> Bool
isFeatureIrreducible f = not $ isFeatureNonCanonical f

isFeatureObject :: Feature -> Bool
isFeatureObject f = case fetchLabelType f of
  ObjectLabelType -> True
  _ -> False

isFeatureFileTop :: Feature -> Bool
isFeatureFileTop f = case fetchLabelType f of
  FileTopLabelType -> True
  _ -> False

bsToStringFeature :: (MonadState s m, HasTextIndexer s) => BC.ByteString -> m Feature
bsToStringFeature s = mkStringFeature <$> textToTextIndex s

strToStringFeature :: (MonadState s m, HasTextIndexer s) => String -> m Feature
strToStringFeature s = bsToStringFeature (BC.pack s)

-- | Unary operation can not be a unify operation.
unaryOpTASeg :: Feature
unaryOpTASeg = mkOpArgFeature 0

binOpLeftTASeg :: Feature
binOpLeftTASeg = mkOpArgFeature 0

binOpRightTASeg :: Feature
binOpRightTASeg = mkOpArgFeature 1

toBinOpTASeg :: BinOpDirect -> Feature
toBinOpTASeg L = binOpLeftTASeg
toBinOpTASeg R = binOpRightTASeg

fileTopFeature :: Feature
fileTopFeature = mkFeature 0 FileTopLabelType

universalFeature :: Feature
universalFeature = mkFeature 0 UniversalLabelType

packageFeature :: Feature
packageFeature = mkFeature 0 PackageLabelType

data BinOpDirect = L | R deriving (Eq, Ord)

instance Show BinOpDirect where
  show L = "L"
  show R = "R"

{- | ValAddr is full addr to a value. The segments are stored in reverse order, meaning the last segment is the first in
the list.
-}
newtype ValAddr = ValAddr
  { vFeatures :: V.Vector Feature
  }
  deriving (Show, Eq, Ord, Generic, NFData)

instance ShowWTIndexer ValAddr where
  tshow (ValAddr a)
    | V.null a = return "."
    | isFeatureFileTop (a V.! 0) = do
        x <- mapM (\x -> T.unpack <$> tshow x) (V.toList $ V.drop 1 a)
        return $ T.pack $ "/" ++ intercalate "/" x
    | otherwise = do
        x <- mapM (\x -> T.unpack <$> tshow x) (V.toList a)
        return $ T.pack $ intercalate "/" x

instance Hashable ValAddr where
  hashWithSalt salt (ValAddr a) = (V.foldl' (\h f -> hashWithSalt h f) salt a)

instance ToJSON ValAddr where
  toJSON a = toJSON (show a)

instance ToJSONWTIndexer ValAddr where
  ttoJSON a = do
    s <- tshow a
    return $ toJSON s

mkValAddr :: V.Vector Feature -> ValAddr
mkValAddr = ValAddr

emptyValAddr :: ValAddr
emptyValAddr = mkValAddr V.empty

fileTopValAddr :: ValAddr
fileTopValAddr = mkValAddr (V.singleton fileTopFeature)

universalValAddr :: ValAddr
universalValAddr = mkValAddr (V.singleton universalFeature)

packageValAddr :: ValAddr
packageValAddr = mkValAddr (V.singleton packageFeature)

isValAddrEmpty :: ValAddr -> Bool
isValAddrEmpty a = V.null (vFeatures a)

addrFromList :: [Feature] -> ValAddr
addrFromList segs = mkValAddr (V.fromList segs)

-- | This is mostly used for testing purpose.
addrFromStringList :: (MonadState s m, HasTextIndexer s) => [String] -> m ValAddr
addrFromStringList segs = do
  xs <- mapM strToStringFeature segs
  return $ mkValAddr (V.fromList xs)

addrToList :: ValAddr -> [Feature]
addrToList (ValAddr a) = V.toList a

appendSeg :: ValAddr -> Feature -> ValAddr
appendSeg (ValAddr a) seg = mkValAddr (V.snoc a seg)

{- | Append the new addr to old addr.
new and old are reversed, such as [z, y, x] and [b, a]. The appended addr should be [z, y, x, b, a], which is
a.b.x.y.z.
-}
appendValAddr ::
  -- | old addr
  ValAddr ->
  -- | new addr to be appended to the old addr
  ValAddr ->
  ValAddr
appendValAddr (ValAddr old) (ValAddr new) = mkValAddr (old V.++ new)

-- | Get the parent addr of a addr by removing the last segment.
initValAddr :: ValAddr -> Maybe ValAddr
initValAddr (ValAddr a)
  | V.null a = Nothing
  | otherwise = Just $ mkValAddr (V.init a)

-- | Get the tail addr of a addr, excluding the head segment.
tailValAddr :: ValAddr -> Maybe ValAddr
tailValAddr (ValAddr a)
  | V.null a = Nothing
  | otherwise = Just $ mkValAddr (V.tail a)

-- | Get the last segment of a addr.
lastSeg :: ValAddr -> Maybe Feature
lastSeg (ValAddr a)
  | V.null a = Nothing
  | otherwise = Just $ V.last a

-- | Get the head segment of a addr.
headSeg :: ValAddr -> Maybe Feature
headSeg (ValAddr a)
  | V.null a = Nothing
  | otherwise = Just $ V.head a

-- | Trim all the features that are after the first matching feature, including the matching feature.
trimFirstMatchToEnd :: (Feature -> Bool) -> ValAddr -> ValAddr
trimFirstMatchToEnd f (ValAddr xs) =
  let firstMatchIdx = V.findIndex f xs
   in case firstMatchIdx of
        Just idx -> ValAddr $ V.take idx xs
        Nothing -> ValAddr xs

-- | Trim all the features that are before the last matching feature, not including the matching feature.
trimBeginToLastMatch :: (Feature -> Bool) -> ValAddr -> ValAddr
trimBeginToLastMatch f (ValAddr xs) =
  let lastMatchIdx = V.findIndexR f xs
   in case lastMatchIdx of
        Just idx -> ValAddr $ V.drop idx xs
        Nothing -> ValAddr xs

trimFirstObjToEnd :: ValAddr -> ValAddr
trimFirstObjToEnd = trimFirstMatchToEnd isFeatureObject

trimBeginToLastObj :: ValAddr -> ValAddr
trimBeginToLastObj = trimBeginToLastMatch isFeatureObject

{- | Check if addr x is a prefix of addr y.

For example, isPrefix (a.b) (a.b.c.d) = True, isPrefix (a.b.c) (a.b) = False.
-}
isPrefix :: ValAddr -> ValAddr -> Bool
isPrefix (ValAddr x) (ValAddr y) = isSegVPrefix x y

isSegVPrefix :: V.Vector Feature -> V.Vector Feature -> Bool
isSegVPrefix x y = V.length x <= V.length y && V.and (V.zipWith (==) x y)

{- | Trim the address by cutting off the prefix.

If the second addr is not a prefix of the first addr or the first addr is shorter than the second addr, then the
first addr is returned.
-}
trimPrefixAddr :: ValAddr -> ValAddr -> ValAddr
trimPrefixAddr pre@(ValAddr pa) x@(ValAddr xa)
  | not (isPrefix pre x) = x
  | otherwise = mkValAddr (V.drop (V.length pa) xa)

isSuffix :: ValAddr -> ValAddr -> Bool
isSuffix (ValAddr x) (ValAddr y) = isSegVSuffix x y

{- | Check if the first features are a suffix of the second features.

For example, isSegVSuffix (c.d) (a.b.c.d) = True, isSegVSuffix (b.c) (a.b) = False.
-}
isSegVSuffix :: V.Vector Feature -> V.Vector Feature -> Bool
isSegVSuffix x y = isSegVPrefix (V.reverse x) (V.reverse y)

trimSuffixAddr :: ValAddr -> ValAddr -> ValAddr
trimSuffixAddr suf@(ValAddr sa) x@(ValAddr xa)
  | not (isSuffix suf x) = x
  | otherwise = mkValAddr (V.take (V.length xa - V.length sa) xa)

{- | CanonicalAddr is an addr that ends with an irreducible segment.

Besides referrable segments, irreducible segments include dynamic field segments and pattern segments, etc..

For an address to be irreducible, there is no need to make sure all segments are irreducible.
For example,
  x: ({a:1,b:a}).b | 1.

The addr of the b is /x/fa0/fa0/b, which is not all irreducible.
-}
newtype CanonicalAddr = CanonicalAddr {getCanonicalAddr :: ValAddr}
  deriving (Show, Eq, Ord, Generic, NFData, ToJSON, ToJSONWTIndexer, ToJSONKey)

instance ShowWTIndexer CanonicalAddr where
  tshow (CanonicalAddr c) = tshow c

-- | A feature is canonical if it can be present in a fully reduced value.
isFeatureNonCanonical :: Feature -> Bool
isFeatureNonCanonical f = case fetchLabelType f of
  OpArgLabelType -> True
  ConstraintLabelType -> True
  DynCnstrLabelType -> True
  ListStoreIdxLabelType -> True
  _ -> False

isFeatureCanonical :: Feature -> Bool
isFeatureCanonical = not . isFeatureNonCanonical

addrIsCanonical :: ValAddr -> Maybe CanonicalAddr
addrIsCanonical (ValAddr xs) =
  let hasReducible = V.any isFeatureNonCanonical xs
   in if hasReducible
        then Nothing
        else Just $ CanonicalAddr $ ValAddr xs

collapseToCanonical :: ValAddr -> CanonicalAddr
collapseToCanonical (ValAddr xs) = CanonicalAddr $ ValAddr (V.filter (not . isFeatureNonCanonical) xs)

collapseToCanonicalForm :: ValAddr -> ValAddr
collapseToCanonicalForm addr = canonicalToAddr $ collapseToCanonical addr

genWoObjCanonical :: ValAddr -> CanonicalAddr
genWoObjCanonical addr = CanonicalAddr (trimFirstMatchToEnd isFeatureNonCanonical addr)

genWoObjCanonicalForm :: ValAddr -> ValAddr
genWoObjCanonicalForm addr = canonicalToAddr $ genWoObjCanonical addr

canonicalToAddr :: CanonicalAddr -> ValAddr
canonicalToAddr (CanonicalAddr v) = v

initCanonical :: CanonicalAddr -> Maybe CanonicalAddr
initCanonical (CanonicalAddr v) = fmap CanonicalAddr (initValAddr v)

assembleIdentCanonical :: CanonicalAddr -> Feature -> ValAddr -> ValAddr
assembleIdentCanonical diff feat addr =
  let
    -- If the last seg is dj
    --  - the value is a struct, it is impossible.
    canAddr = collapseToCanonical addr
    canParAddrM = initCanonical canAddr
    identScopeAddr = case canParAddrM of
      Just canParAddr -> trimSuffixAddr (getCanonicalAddr diff) (getCanonicalAddr canParAddr)
      Nothing -> fileTopValAddr
    identAddr = appendSeg identScopeAddr feat
   in
    identAddr

{- | ReferableAddr is a referrable address.

A referable address must end with a referable segment.

For an address to be referable, there is no need to make sure all segments are referable.
For example,
  x: ({a:1,b:a})[b] + 1, or
  x: {a:1,b:a} | 1.

For the second expression, the addr of the a is /x/dj0/a, which is referable even though dj0 is not referable.
-}
newtype ReferableAddr = ReferableAddr {getReferableAddr :: CanonicalAddr}
  deriving (Show, Eq, Ord, Generic, NFData, ToJSON, ToJSONWTIndexer)

instance ShowWTIndexer ReferableAddr where
  tshow (ReferableAddr c) = tshow c

isFeatureReferable :: Feature -> Bool
isFeatureReferable f = case fetchLabelType f of
  StringLabelType -> True
  LetLabelType -> True
  ListIdxLabelType -> True
  FileTopLabelType -> True
  _ -> False

rfbAddrToAddr :: ReferableAddr -> ValAddr
rfbAddrToAddr (ReferableAddr c) = canonicalToAddr c

rfbAddrToCanonical :: ReferableAddr -> CanonicalAddr
rfbAddrToCanonical (ReferableAddr c) = c

rfbAddrToTopReducer :: ReferableAddr -> TopReducerAddr
rfbAddrToTopReducer (ReferableAddr c) = TopReducerAddr c

-- | VertexAddr is a subset of ReferableAddr.
rfbAddrToVertex :: ReferableAddr -> VertexAddr
rfbAddrToVertex (ReferableAddr c) = VertexAddr c

addrIsRfbAddr :: ValAddr -> Maybe ReferableAddr
addrIsRfbAddr addr = do
  c <- addrIsCanonical addr
  lseg <- lastSeg (canonicalToAddr c)
  if isFeatureReferable lseg
    then return $ ReferableAddr c
    else Nothing

trimCanonicalToRfb :: CanonicalAddr -> ReferableAddr
trimCanonicalToRfb (CanonicalAddr (ValAddr xs)) =
  let revxs = V.reverse xs
      rest = V.dropWhile (not . isFeatureReferable) revxs
   in ReferableAddr (CanonicalAddr (ValAddr $ V.reverse rest))

{- | Vertex differs from Canonical in that disjunct is not considered a legal ending. A disjunct is part of its parent
vertex.
-}
newtype VertexAddr = VertexAddr {getVertexAddr :: CanonicalAddr}
  deriving (Show, Eq, Ord, Generic, NFData, ToJSON, ToJSONWTIndexer, ToJSONKey)

instance ShowWTIndexer VertexAddr where
  tshow (VertexAddr c) = tshow c

isFeatureVertex :: Feature -> Bool
isFeatureVertex f = case fetchLabelType f of
  DisjLabelType -> False
  _ -> isFeatureCanonical f

trimCanonicalToVertex :: CanonicalAddr -> VertexAddr
trimCanonicalToVertex (CanonicalAddr (ValAddr xs)) =
  let revxs = V.reverse xs
      rest = V.dropWhile (not . isFeatureVertex) revxs
   in VertexAddr (CanonicalAddr (ValAddr $ V.reverse rest))

vertexToAddr :: VertexAddr -> ValAddr
vertexToAddr (VertexAddr c) = canonicalToAddr c

addrIsVertex :: ValAddr -> Maybe VertexAddr
addrIsVertex addr = do
  c <- addrIsCanonical addr
  lseg <- lastSeg (canonicalToAddr c)
  if isFeatureVertex lseg
    then return $ VertexAddr c
    else Nothing

initVertexAddr :: VertexAddr -> Maybe VertexAddr
initVertexAddr (VertexAddr c) = fmap VertexAddr (initCanonical c)

trimVertexToTopReducerAddr :: VertexAddr -> TopReducerAddr
trimVertexToTopReducerAddr (VertexAddr c) = trimCanonicalToTopReducer c

-- | TopReducer is the topmost value that can be called reducer on.
newtype TopReducerAddr = TopReducerAddr {getTopReducerAddr :: CanonicalAddr}
  deriving (Show, Eq, Ord, Generic, NFData, ShowWTIndexer, ToJSON, ToJSONWTIndexer)

isFeatureTopReducer :: Feature -> Bool
isFeatureTopReducer f = case fetchLabelType f of
  ObjectLabelType -> False
  DisjLabelType -> False
  _ -> isFeatureCanonical f

trimCanonicalToTopReducer :: CanonicalAddr -> TopReducerAddr
trimCanonicalToTopReducer (CanonicalAddr xs) =
  TopReducerAddr $ CanonicalAddr $ trimFirstMatchToEnd (not . isFeatureTopReducer) xs

topReducerToAddr :: TopReducerAddr -> ValAddr
topReducerToAddr (TopReducerAddr c) = canonicalToAddr c

addrIsTopReducer :: ValAddr -> Maybe TopReducerAddr
addrIsTopReducer addr = do
  c@(CanonicalAddr (ValAddr xs)) <- addrIsCanonical addr
  let isAllTopReducer = V.all isFeatureTopReducer xs
  if isAllTopReducer
    then return $ TopReducerAddr c
    else Nothing

initTopReducer :: TopReducerAddr -> Maybe TopReducerAddr
initTopReducer (TopReducerAddr c) = fmap TopReducerAddr (initCanonical c)
