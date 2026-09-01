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

{- | An evaluator address containing no reduction-local segments.

Converting to a reduced address removes internal traversal steps that cannot
identify a node in the evaluator's reduced address structure, such as operation
arguments, constraints, dynamic constraints, and list-store indices. Other
internal steps, including disjuncts and object terms, remain. A reduced address
therefore describes the location retained after this traversal detail is
erased; it is not necessarily a user-visible logical address, a dependency
address, or a stored value node. It also does not assert that evaluation of the
addressed node has completed.

For example, in:

@x: ({a: 1, b: a}).b | 1@

the evaluator address of @b@ is @/x/fa0/fa0/b@. Removing the @fa0@
operation-argument segments produces the reduced address @/x/b@.

'addrIsReduced' checks this invariant without changing the address, whereas
'toReducedAddr' establishes it by removing every reduction-local
segment.
-}
newtype ReducedAddr = ReducedAddr {getReducedAddr :: EvalAddr}
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, ToJSON, ToJSONWTIndexer, ToJSONKey)

instance ShowWTIndexer ReducedAddr where
  tshow (ReducedAddr addr) = tshow addr

-- | Whether a segment is local to reduction and absent from a reduced address.
isSegmentNonReduced :: AddrSegment -> Bool
isSegmentNonReduced seg = case addrSegmentTag seg of
  OpArgTag -> True
  ConstraintTag -> True
  DynCnstrTag -> True
  ListStoreIdxTag -> True
  _ -> False

isSegmentReduced :: AddrSegment -> Bool
isSegmentReduced = not . isSegmentNonReduced

addrIsReduced :: EvalAddr -> Maybe ReducedAddr
addrIsReduced (EvalAddr xs) =
  let hasReductionLocalSegment = V.any isSegmentNonReduced xs
   in if hasReductionLocalSegment
        then Nothing
        else Just $ ReducedAddr $ EvalAddr xs

toReducedAddr :: EvalAddr -> ReducedAddr
toReducedAddr (EvalAddr xs) = ReducedAddr $ EvalAddr (V.filter (not . isSegmentNonReduced) xs)

toReducedForm :: EvalAddr -> EvalAddr
toReducedForm = getReducedAddr . toReducedAddr

initReduced :: ReducedAddr -> Maybe ReducedAddr
initReduced (ReducedAddr addr) = fmap ReducedAddr (initEvalAddr addr)

{- | Resolve a deferred identifier locator against a reference's actual address.

The difference is the reduced path from the identifier's defining scope down
to the lexical scope containing the reference. Converting the reference address
and removing its final segment gives that actual containing scope.
Removing the stored suffix then recovers the defining scope; appending the
identifier feature produces the absolute identifier address.

For a generated reference at @/x/nested/b@ with difference @nested@ and feature
@a@, this computes @/x/nested - nested + a = /x/a@.
-}
assembleIdentReduced :: EvalAddr -> Feature -> EvalAddr -> EvalAddr
assembleIdentReduced diff feat addr =
  let
    -- If the last seg is dj
    --  - the value is a struct, it is impossible.
    reducedAddr = toReducedAddr addr
    reducedParentAddrM = initReduced reducedAddr
    identScopeAddr = case reducedParentAddrM of
      Just reducedParentAddr -> trimSuffixAddr diff (getReducedAddr reducedParentAddr)
      Nothing -> fileTopEvalAddr
    identAddr = appendFeature identScopeAddr feat
   in
    identAddr

{- | A reduced address that may serve as a dependency target.

Dependency addresses end at string fields, let bindings, list elements, or the
file root. Only the final segment must identify a dependency target; preceding
reduced segments may be internal evaluator steps. This allows dependencies on
values nested in
expressions such as @x: ({a: 1, b: a})[b] + 1@ or
@x: {a: 1, b: a} | 1@. In the second expression, the physical address of @a@
is @/x/dj0/a@, which is a dependency address because its final segment is @a@
even though @dj0@ is an internal evaluator step.

'addrIsDependency' checks whether an evaluator address is already a dependency
address, while 'trimReducedToDependency' trims a reduced address to its nearest
prefix that can serve as a dependency target.
-}
newtype DependencyAddr = DependencyAddr {getDependencyAddr :: ReducedAddr}
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, ToJSON, ToJSONWTIndexer)

instance ShowWTIndexer DependencyAddr where
  tshow (DependencyAddr addr) = tshow addr

isDependencyTerminal :: AddrSegment -> Bool
isDependencyTerminal seg = case addrSegmentTag seg of
  StringTag -> True
  LetTag -> True
  ListIdxTag -> True
  FileTopTag -> True
  _ -> False

dependencyToAddr :: DependencyAddr -> EvalAddr
dependencyToAddr (DependencyAddr reducedAddr) = getReducedAddr reducedAddr

addrIsDependency :: EvalAddr -> Maybe DependencyAddr
addrIsDependency addr = do
  reducedAddr <- addrIsReduced addr
  lseg <- lastSeg (getReducedAddr reducedAddr)
  if isDependencyTerminal lseg
    then return $ DependencyAddr reducedAddr
    else Nothing

trimReducedToDependency :: ReducedAddr -> DependencyAddr
trimReducedToDependency (ReducedAddr (EvalAddr xs)) =
  let revxs = V.reverse xs
      rest = V.dropWhile (not . isDependencyTerminal) revxs
   in DependencyAddr (ReducedAddr (EvalAddr $ V.reverse rest))
