{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}

module EvalAddr where

import Control.DeepSeq (NFData (..))
import Data.Aeson (ToJSON, toJSON)
import Data.Aeson.Types (ToJSONKey)
import Data.Bits (Bits (..))
import qualified Data.ByteString.Char8 as BC
import Data.Coerce (coerce)
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
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (NFData)

instance Show Selector where
  show (StringSel s) = show s
  show (IntSel i) = show i

instance Show Selectors where
  show :: Selectors -> String
  show (Selectors sels) = intercalate "." (map show sels)

instance ShowWTIndexer Selectors where
  tshow (Selectors sels) = do
    selStrs <- mapM tshow sels
    return $ T.intercalate "." selStrs

instance ShowWTIndexer Selector where
  tshow (StringSel s) = tshow s
  tshow (IntSel i) = return $ T.pack $ show i

{- | Convert concrete selectors to semantic feature segments.

TODO: rename selectorsToAddr
-}
fieldPathToAddr :: Selectors -> EvalAddr
fieldPathToAddr sels = addrFromList $ selectorsToAddrSegments sels

{- | Convert an address made only of concrete selector segments back to
selectors. Returns 'Nothing' when the address contains a root, an internal
term step, or a non-selector feature such as a let binding.
-}
addrToSelectors :: EvalAddr -> Maybe Selectors
addrToSelectors addr = Selectors <$> mapM segmentToSelector (addrToList addr)
 where
  segmentToSelector segment = do
    feature <- addrSegmentToFeature segment
    case featureTag feature of
      StringTag -> Just $ StringSel $ TextIndex $ featureIndex feature
      ListIdxTag -> Just $ IntSel $ featureIndex feature
      _ -> Nothing

selectorsToAddrSegments :: Selectors -> [AddrSegment]
selectorsToAddrSegments (Selectors sels) = map (featureToAddrSegment . selectorToFeature) sels

selectorToFeature :: Selector -> Feature
selectorToFeature (StringSel s) = mkStringFeature s
selectorToFeature (IntSel i) = mkListIdxFeature i

{- | Roots, semantic features, and internal term steps retain the same compact
integer representation that the original 'Feature' type used. The distinct
newtypes make their roles visible to the type checker without changing runtime
comparison, ordering, or hashing.
-}
newtype Root = Root {getRoot :: Int}
  deriving stock (Generic)
  deriving newtype (Eq, Ord, NFData, Hashable)

newtype Feature = Feature {getFeature :: Int}
  deriving stock (Generic)
  deriving newtype (Eq, Ord, NFData, Hashable)

newtype TermStep = TermStep {getTermStep :: Int}
  deriving stock (Generic)
  deriving newtype (Eq, Ord, NFData, Hashable)

newtype AddrSegment = AddrSegment {getAddrSegment :: Int}
  deriving stock (Generic)
  deriving newtype (Eq, Ord, NFData, Hashable)

-- | The global tags intentionally retain their old order and bit layout.
data SegmentTag
  = FileTopTag
  | UniversalTag
  | PackageTag
  | ListStoreIdxTag
  | ListIdxTag
  | DisjTag
  | OpArgTag
  | StringTag
  | LetTag
  | PatternTag
  | DynFieldTag
  | EmbedValueTag
  | ObjectTag
  | ConstraintTag
  | DynCnstrTag
  deriving (Eq, Ord, Generic, NFData, Enum)

rootToAddrSegment :: Root -> AddrSegment
rootToAddrSegment = coerce

featureToAddrSegment :: Feature -> AddrSegment
featureToAddrSegment = coerce

termStepToAddrSegment :: TermStep -> AddrSegment
termStepToAddrSegment = coerce

addrSegmentToRoot :: AddrSegment -> Maybe Root
addrSegmentToRoot seg = case addrSegmentTag seg of
  FileTopTag -> Just $ coerce seg
  UniversalTag -> Just $ coerce seg
  PackageTag -> Just $ coerce seg
  _ -> Nothing

addrSegmentToFeature :: AddrSegment -> Maybe Feature
addrSegmentToFeature seg = case addrSegmentTag seg of
  ListIdxTag -> Just $ coerce seg
  StringTag -> Just $ coerce seg
  LetTag -> Just $ coerce seg
  _ -> Nothing

addrSegmentToTermStep :: AddrSegment -> Maybe TermStep
addrSegmentToTermStep seg = case addrSegmentTag seg of
  ListStoreIdxTag -> Just $ coerce seg
  DisjTag -> Just $ coerce seg
  OpArgTag -> Just $ coerce seg
  PatternTag -> Just $ coerce seg
  DynFieldTag -> Just $ coerce seg
  EmbedValueTag -> Just $ coerce seg
  ObjectTag -> Just $ coerce seg
  ConstraintTag -> Just $ coerce seg
  DynCnstrTag -> Just $ coerce seg
  _ -> Nothing

segmentTag :: Int -> SegmentTag
segmentTag f = toEnum $ (f `shiftR` 24) .&. 0x000000FF

segmentIndex :: Int -> Int
segmentIndex f = f .&. 0x00FFFFFF

addrSegmentTag :: AddrSegment -> SegmentTag
addrSegmentTag = segmentTag . getAddrSegment

featureTag :: Feature -> SegmentTag
featureTag = segmentTag . getFeature

featureIndex :: Feature -> Int
featureIndex = segmentIndex . getFeature

termStepTag :: TermStep -> SegmentTag
termStepTag = segmentTag . getTermStep

termStepIndex :: TermStep -> Int
termStepIndex = segmentIndex . getTermStep

rootTag :: Root -> SegmentTag
rootTag = segmentTag . getRoot

encodeSegment :: Int -> SegmentTag -> Int
encodeSegment i tag = (fromEnum tag `shiftL` 24) .|. (i .&. 0x00FFFFFF)

mkRoot :: SegmentTag -> Root
mkRoot = Root . encodeSegment 0

mkFeature :: Int -> SegmentTag -> Feature
mkFeature i = Feature . encodeSegment i

mkTermStep :: Int -> SegmentTag -> TermStep
mkTermStep i = TermStep . encodeSegment i

instance Show Root where
  show r = case rootTag r of
    FileTopTag -> "/top"
    UniversalTag -> "/builtin"
    PackageTag -> "/pkg"
    tag -> error $ "invalid root tag: " ++ show (fromEnum tag)

instance Show Feature where
  show f = case featureTag f of
    ListIdxTag -> "li" ++ show (featureIndex f)
    StringTag -> "str_" ++ show (featureIndex f)
    LetTag -> "let_" ++ show (featureIndex f)
    tag -> error $ "invalid feature tag: " ++ show (fromEnum tag)

instance Show TermStep where
  show step = case termStepTag step of
    ListStoreIdxTag -> "lsi" ++ show (termStepIndex step)
    DisjTag -> "dj" ++ show (termStepIndex step)
    OpArgTag -> "fa" ++ show (termStepIndex step)
    PatternTag -> "cns_" ++ showSub (getPatternIndexesFromTermStep step) show
    DynFieldTag -> "dyn_" ++ showSub (getDynFieldIndexesFromTermStep step) show
    EmbedValueTag -> "embedv"
    ObjectTag -> "o_" ++ show (termStepIndex step)
    ConstraintTag -> "c_" ++ show (termStepIndex step)
    DynCnstrTag -> "dc_" ++ show (termStepIndex step)
    tag -> error $ "invalid term-step tag: " ++ show (fromEnum tag)
   where
    showSub :: (Int, a) -> (a -> String) -> String
    showSub (x, y) g = show x ++ "_" ++ g y

instance Show AddrSegment where
  show seg = case addrSegmentToRoot seg of
    Just r -> show r
    Nothing -> case addrSegmentToFeature seg of
      Just f -> show f
      Nothing -> case addrSegmentToTermStep seg of
        Just step -> show step
        Nothing -> error "invalid address segment"

instance ShowWTIndexer Root where
  tshow = return . T.pack . show

instance ShowWTIndexer Feature where
  tshow f = case featureTag f of
    StringTag -> tshow (TextIndex (featureIndex f))
    LetTag -> do
      str <- tshow (TextIndex (featureIndex f))
      return $ T.pack $ printf "let_%s" str
    _ -> return $ T.pack $ show f

instance ShowWTIndexer TermStep where
  tshow = return . T.pack . show

instance ShowWTIndexer AddrSegment where
  tshow seg = case addrSegmentToRoot seg of
    Just r -> tshow r
    Nothing -> case addrSegmentToFeature seg of
      Just f -> tshow f
      Nothing -> case addrSegmentToTermStep seg of
        Just step -> tshow step
        Nothing -> error "invalid address segment"

mkStringFeature :: TextIndex -> Feature
mkStringFeature (TextIndex i) = mkFeature i StringTag

mkListStoreIdxTermStep :: Int -> TermStep
mkListStoreIdxTermStep i = mkTermStep i ListStoreIdxTag

mkListIdxFeature :: Int -> Feature
mkListIdxFeature i = mkFeature i ListIdxTag

mkDisjTermStep :: Int -> TermStep
mkDisjTermStep i = mkTermStep i DisjTag

mkOpArgTermStep :: Int -> TermStep
mkOpArgTermStep index = mkTermStep index OpArgTag

mkRegCnstrTermStep :: Int -> TermStep
mkRegCnstrTermStep i = mkTermStep i ConstraintTag

{- | The first is the ObjectID, the second indicates the i-th in the dynamic field.

The selector is shifted left by 23 bits to make room for larger object IDs.
-}
mkDynFieldTermStep :: Int -> Int -> TermStep
mkDynFieldTermStep objID selector = mkTermStep combined DynFieldTag
 where
  shiftedSelector = selector `shiftL` 23
  combined = objID .|. shiftedSelector

mkPatternTermStep :: Int -> Int -> TermStep
mkPatternTermStep objID selector = mkTermStep combined PatternTag
 where
  shiftedSelector = selector `shiftL` 23
  combined = objID .|. shiftedSelector

mkLetFeature :: TextIndex -> Feature
mkLetFeature (TextIndex i) = mkFeature i LetTag

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

embedValueTermStep :: TermStep
embedValueTermStep = mkTermStep 0 EmbedValueTag

mkDynCnstrTermStep :: Int -> TermStep
mkDynCnstrTermStep i = mkTermStep i DynCnstrTag

mkObjectTermStep :: Int -> TermStep
mkObjectTermStep i = mkTermStep i ObjectTag

getTextIndexFromFeature :: (HasCallStack) => Feature -> TextIndex
getTextIndexFromFeature f = case featureTag f of
  StringTag -> TextIndex (featureIndex f)
  LetTag -> TextIndex (featureIndex f)
  _ -> error $ printf "Feature %s does not have a TextIndex" (show f)

getPatternIndexesFromTermStep :: TermStep -> (Int, Int)
getPatternIndexesFromTermStep step = case termStepTag step of
  PatternTag ->
    let combined = termStepIndex step
        objID = combined .&. 0x007FFFFF -- lower 23 bits
        selector = (combined `shiftR` 23) .&. 1 -- next bit
     in (objID, selector)
  _ -> error $ "TermStep is not a pattern step: " ++ show step

getDynFieldIndexesFromTermStep :: TermStep -> (Int, Int)
getDynFieldIndexesFromTermStep step = case termStepTag step of
  DynFieldTag ->
    let combined = termStepIndex step
        objID = combined .&. 0x007FFFFF -- lower 23 bits
        selector = (combined `shiftR` 23) .&. 1 -- next bit
     in (objID, selector)
  _ -> error $ "TermStep is not a dynamic-field step: " ++ show step

isFileTopSegment :: AddrSegment -> Bool
isFileTopSegment seg = case addrSegmentToRoot seg of
  Just r | rootTag r == FileTopTag -> True
  _ -> False

fileTopRoot :: Root
fileTopRoot = mkRoot FileTopTag

universalRoot :: Root
universalRoot = mkRoot UniversalTag

packageRoot :: Root
packageRoot = mkRoot PackageTag

data BinOpDirect = L | R deriving (Eq, Ord)

instance Show BinOpDirect where
  show L = "L"
  show R = "R"

{- | A path through the evaluator's value and term tree.

An address may be rooted or relative. Its segments may identify semantic
features, such as struct fields and list elements, or internal evaluator terms,
such as disjuncts, operation arguments, and constraints. It therefore describes
an evaluator traversal path and is not necessarily a user-visible logical
address. The more restricted address types below refine 'EvalAddr' for specific
roles.
-}
newtype EvalAddr = EvalAddr
  { evalAddrSegments :: V.Vector AddrSegment
  }
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (NFData)

instance Show EvalAddr where
  show (EvalAddr a) = "EvalAddr {evalAddrSegments = " ++ show a ++ "}"

instance ShowWTIndexer EvalAddr where
  tshow (EvalAddr a)
    | V.null a = return "."
    | isFileTopSegment (a V.! 0) = do
        x <- mapM (\x -> T.unpack <$> tshow x) (V.toList $ V.drop 1 a)
        return $ T.pack $ "/" ++ intercalate "/" x
    | otherwise = do
        x <- mapM (\x -> T.unpack <$> tshow x) (V.toList a)
        return $ T.pack $ intercalate "/" x

instance Hashable EvalAddr where
  hashWithSalt salt (EvalAddr a) = (V.foldl' (\h f -> hashWithSalt h f) salt a)

instance ToJSON EvalAddr where
  toJSON a = toJSON (show a)

instance ToJSONWTIndexer EvalAddr where
  ttoJSON a = do
    s <- tshow a
    return $ toJSON s

mkEvalAddr :: V.Vector AddrSegment -> EvalAddr
mkEvalAddr = EvalAddr

emptyEvalAddr :: EvalAddr
emptyEvalAddr = mkEvalAddr V.empty

fileTopEvalAddr :: EvalAddr
fileTopEvalAddr = mkEvalAddr (V.singleton $ rootToAddrSegment fileTopRoot)

universalEvalAddr :: EvalAddr
universalEvalAddr = mkEvalAddr (V.singleton $ rootToAddrSegment universalRoot)

packageEvalAddr :: EvalAddr
packageEvalAddr = mkEvalAddr (V.singleton $ rootToAddrSegment packageRoot)

addrFromList :: [AddrSegment] -> EvalAddr
addrFromList segs = mkEvalAddr (V.fromList segs)

addrToList :: EvalAddr -> [AddrSegment]
addrToList (EvalAddr a) = V.toList a

appendSeg :: EvalAddr -> AddrSegment -> EvalAddr
appendSeg (EvalAddr a) seg = mkEvalAddr (V.snoc a seg)

appendFeature :: EvalAddr -> Feature -> EvalAddr
appendFeature addr = appendSeg addr . featureToAddrSegment

appendTermStep :: EvalAddr -> TermStep -> EvalAddr
appendTermStep addr = appendSeg addr . termStepToAddrSegment

-- | Append the root-to-leaf segments of the new address to the old address.
appendEvalAddr ::
  -- | old addr
  EvalAddr ->
  -- | new addr to be appended to the old addr
  EvalAddr ->
  EvalAddr
appendEvalAddr (EvalAddr old) (EvalAddr new) = mkEvalAddr (old V.++ new)

-- | Get the parent addr of a addr by removing the last segment.
initEvalAddr :: EvalAddr -> Maybe EvalAddr
initEvalAddr (EvalAddr a)
  | V.null a = Nothing
  | otherwise = Just $ mkEvalAddr (V.init a)

-- | Get the last segment of a addr.
lastSeg :: EvalAddr -> Maybe AddrSegment
lastSeg (EvalAddr a)
  | V.null a = Nothing
  | otherwise = Just $ V.last a

-- | Get the head segment of a addr.
headSeg :: EvalAddr -> Maybe AddrSegment
headSeg (EvalAddr a)
  | V.null a = Nothing
  | otherwise = Just $ V.head a

-- | Trim all the segments that are after the first matching segment, including the matching segment.
trimFirstMatchToEnd :: (AddrSegment -> Bool) -> EvalAddr -> EvalAddr
trimFirstMatchToEnd f (EvalAddr xs) =
  let firstMatchIdx = V.findIndex f xs
   in case firstMatchIdx of
        Just idx -> EvalAddr $ V.take idx xs
        Nothing -> EvalAddr xs

{- | Check if addr x is a prefix of addr y.

For example, isPrefix (a.b) (a.b.c.d) = True, isPrefix (a.b.c) (a.b) = False.
-}
isPrefix :: EvalAddr -> EvalAddr -> Bool
isPrefix (EvalAddr x) (EvalAddr y) = isSegVPrefix x y

isSegVPrefix :: V.Vector AddrSegment -> V.Vector AddrSegment -> Bool
isSegVPrefix x y = V.length x <= V.length y && V.and (V.zipWith (==) x y)

{- | Trim the address by cutting off the prefix.

If the second addr is not a prefix of the first addr or the first addr is shorter than the second addr, then the
first addr is returned.
-}
trimPrefixAddr :: EvalAddr -> EvalAddr -> EvalAddr
trimPrefixAddr pre@(EvalAddr pa) x@(EvalAddr xa)
  | not (isPrefix pre x) = x
  | otherwise = mkEvalAddr (V.drop (V.length pa) xa)

isSuffix :: EvalAddr -> EvalAddr -> Bool
isSuffix (EvalAddr x) (EvalAddr y) = isSegVSuffix x y

{- | Check if the first features are a suffix of the second features.

For example, isSegVSuffix (c.d) (a.b.c.d) = True, isSegVSuffix (b.c) (a.b) = False.
-}
isSegVSuffix :: V.Vector AddrSegment -> V.Vector AddrSegment -> Bool
isSegVSuffix x y = isSegVPrefix (V.reverse x) (V.reverse y)

trimSuffixAddr :: EvalAddr -> EvalAddr -> EvalAddr
trimSuffixAddr suf@(EvalAddr sa) x@(EvalAddr xa)
  | not (isSuffix suf x) = x
  | otherwise = mkEvalAddr (V.take (V.length xa - V.length sa) xa)

{- | An evaluator address containing no non-canonical segments.

Canonicalization removes internal traversal steps that cannot remain in a fully
reduced value, such as operation arguments, constraints, dynamic constraints,
and list-store indices. Other internal steps, including disjuncts and object
terms, remain canonical. A canonical address therefore describes the physical
path retained after this traversal detail is erased; it is not necessarily a
user-visible logical address, a referable address, or a stored value node.

For example, in:

@x: ({a: 1, b: a}).b | 1@

the evaluator address of @b@ is @/x/fa0/fa0/b@. The @fa0@ operation-argument
segments are non-canonical, so collapsing the address produces the canonical
address @/x/b@.

'addrIsCanonical' checks this invariant without changing the address, whereas
'collapseToCanonical' establishes it by removing every non-canonical segment.
-}
newtype CanonicalAddr = CanonicalAddr {getCanonicalAddr :: EvalAddr}
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, ToJSON, ToJSONWTIndexer, ToJSONKey)

instance ShowWTIndexer CanonicalAddr where
  tshow (CanonicalAddr c) = tshow c

-- | A segment is canonical if it can be present in a fully reduced value.
isSegmentNonCanonical :: AddrSegment -> Bool
isSegmentNonCanonical seg = case addrSegmentTag seg of
  OpArgTag -> True
  ConstraintTag -> True
  DynCnstrTag -> True
  ListStoreIdxTag -> True
  _ -> False

isSegmentCanonical :: AddrSegment -> Bool
isSegmentCanonical = not . isSegmentNonCanonical

addrIsCanonical :: EvalAddr -> Maybe CanonicalAddr
addrIsCanonical (EvalAddr xs) =
  let hasReducible = V.any isSegmentNonCanonical xs
   in if hasReducible
        then Nothing
        else Just $ CanonicalAddr $ EvalAddr xs

collapseToCanonical :: EvalAddr -> CanonicalAddr
collapseToCanonical (EvalAddr xs) = CanonicalAddr $ EvalAddr (V.filter (not . isSegmentNonCanonical) xs)

collapseToCanonicalForm :: EvalAddr -> EvalAddr
collapseToCanonicalForm addr = canonicalToAddr $ collapseToCanonical addr

canonicalToAddr :: CanonicalAddr -> EvalAddr
canonicalToAddr (CanonicalAddr v) = v

initCanonical :: CanonicalAddr -> Maybe CanonicalAddr
initCanonical (CanonicalAddr v) = fmap CanonicalAddr (initEvalAddr v)

assembleIdentCanonical :: CanonicalAddr -> Feature -> EvalAddr -> EvalAddr
assembleIdentCanonical diff feat addr =
  let
    -- If the last seg is dj
    --  - the value is a struct, it is impossible.
    canAddr = collapseToCanonical addr
    canParAddrM = initCanonical canAddr
    identScopeAddr = case canParAddrM of
      Just canParAddr -> trimSuffixAddr (getCanonicalAddr diff) (getCanonicalAddr canParAddr)
      Nothing -> fileTopEvalAddr
    identAddr = appendFeature identScopeAddr feat
   in
    identAddr

{- | A canonical address whose final segment identifies a referable value.

String fields, let bindings, list elements, and the file root are referable.
Only the final segment must be referable; preceding canonical segments may be
internal evaluator steps. This allows references to values nested in
expressions such as @x: ({a: 1, b: a})[b] + 1@ or
@x: {a: 1, b: a} | 1@. In the second expression, the physical address of @a@
is @/x/dj0/a@, which is referable because its final segment is @a@ even though
@dj0@ is not itself referable.

Referable addresses are used as dependency targets. 'addrIsRfbAddr' checks that
an evaluator address is both canonical and referable, while
'trimCanonicalToRfb' projects a canonical address to its nearest referable
prefix.
-}
newtype ReferableAddr = ReferableAddr {getReferableAddr :: CanonicalAddr}
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, ToJSON, ToJSONWTIndexer)

instance ShowWTIndexer ReferableAddr where
  tshow (ReferableAddr c) = tshow c

isSegmentReferable :: AddrSegment -> Bool
isSegmentReferable seg = case addrSegmentTag seg of
  StringTag -> True
  LetTag -> True
  ListIdxTag -> True
  FileTopTag -> True
  _ -> False

rfbAddrToAddr :: ReferableAddr -> EvalAddr
rfbAddrToAddr (ReferableAddr c) = canonicalToAddr c

-- | Every referable address is also a vertex address.
rfbAddrToVertex :: ReferableAddr -> VertexAddr
rfbAddrToVertex (ReferableAddr c) = VertexAddr c

addrIsRfbAddr :: EvalAddr -> Maybe ReferableAddr
addrIsRfbAddr addr = do
  c <- addrIsCanonical addr
  lseg <- lastSeg (canonicalToAddr c)
  if isSegmentReferable lseg
    then return $ ReferableAddr c
    else Nothing

trimCanonicalToRfb :: CanonicalAddr -> ReferableAddr
trimCanonicalToRfb (CanonicalAddr (EvalAddr xs)) =
  let revxs = V.reverse xs
      rest = V.dropWhile (not . isSegmentReferable) revxs
   in ReferableAddr (CanonicalAddr (EvalAddr $ V.reverse rest))

{- | A non-empty canonical address identifying a value node in the evaluator.

A vertex address may contain disjunct segments, but it cannot end with one. A
terminal disjunct segment selects a value contained by its parent disjunction
rather than an independently stored node. For example, @/b/dj0@ is not a vertex
address, while @/b/dj0/x@ is one because it ends at the field @x@.

Vertex addresses are used as keys in the value store and as nodes in the
dependency graph. Every 'ReferableAddr' is a vertex address, but a vertex may
end with an internal canonical segment that is not referable.

'addrIsVertex' checks the invariant without changing the address, while
'trimCanonicalToVertex' removes trailing non-vertex segments to select the
nearest containing vertex.
-}
newtype VertexAddr = VertexAddr {getVertexAddr :: CanonicalAddr}
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, ToJSON, ToJSONWTIndexer, ToJSONKey)

instance ShowWTIndexer VertexAddr where
  tshow (VertexAddr c) = tshow c

instance Hashable VertexAddr where
  hashWithSalt salt (VertexAddr (CanonicalAddr addr)) = hashWithSalt salt addr

-- | The file root represented as a value-store and dependency-graph vertex.
fileTopVertexAddr :: VertexAddr
fileTopVertexAddr = VertexAddr (CanonicalAddr fileTopEvalAddr)

isSegmentVertex :: AddrSegment -> Bool
isSegmentVertex seg = case addrSegmentTag seg of
  DisjTag -> False
  _ -> isSegmentCanonical seg

-- | TODO: trimRight?
trimCanonicalToVertex :: CanonicalAddr -> VertexAddr
trimCanonicalToVertex (CanonicalAddr (EvalAddr xs)) =
  let revxs = V.reverse xs
      rest = V.dropWhile (not . isSegmentVertex) revxs
   in VertexAddr (CanonicalAddr (EvalAddr $ V.reverse rest))

vertexToAddr :: VertexAddr -> EvalAddr
vertexToAddr (VertexAddr c) = canonicalToAddr c

addrIsVertex :: EvalAddr -> Maybe VertexAddr
addrIsVertex addr = do
  c <- addrIsCanonical addr
  lseg <- lastSeg (canonicalToAddr c)
  if isSegmentVertex lseg
    then return $ VertexAddr c
    else Nothing

trimVertexToTopReducerAddr :: VertexAddr -> TopReducerAddr
trimVertexToTopReducerAddr (VertexAddr c) = trimCanonicalToTopReducer c

{- | The canonical address of the reduction unit that owns an evaluator path.

Disjunct and object segments enter subtrees that are reduced as part of their
containing value rather than treated as independent top-level recalculation
units. A top-reducer address therefore contains neither kind of segment;
canonical segments following the first disjunct or object are excluded as well.

For example, while reducing:

@b: *{x: *{y: 1} | 2} | {}@

the physical address of @y@ is @/b/dj0/x/dj0/y@. Its top-reducer address is
@/b@, because the first @dj0@ enters a disjunct owned by the reduction of @b@.

'trimCanonicalToTopReducer' establishes this invariant by retaining the prefix
before the first disjunct or object segment. Recalculation uses that prefix to
find the reduction unit responsible for a changed physical node.
-}
newtype TopReducerAddr = TopReducerAddr {getTopReducerAddr :: CanonicalAddr}
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, ShowWTIndexer, ToJSON, ToJSONWTIndexer)

isSegmentTopReducer :: AddrSegment -> Bool
isSegmentTopReducer seg = case addrSegmentTag seg of
  ObjectTag -> False
  DisjTag -> False
  _ -> isSegmentCanonical seg

trimCanonicalToTopReducer :: CanonicalAddr -> TopReducerAddr
trimCanonicalToTopReducer (CanonicalAddr xs) =
  TopReducerAddr $ CanonicalAddr $ trimFirstMatchToEnd (not . isSegmentTopReducer) xs

initTopReducer :: TopReducerAddr -> Maybe TopReducerAddr
initTopReducer (TopReducerAddr c) = fmap TopReducerAddr (initCanonical c)
