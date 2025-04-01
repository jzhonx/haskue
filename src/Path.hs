module Path where

import Data.Graph (SCC (CyclicSCC), stronglyConnComp)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isNothing)
import qualified Data.Set as Set

data Selector = StringSel String | IntSel Int
  deriving (Eq, Ord)

{- | Reference is a list of selectors.

The selectors are not stored in reverse order.
-}
newtype Reference = Reference {getRefSels :: [Selector]}
  deriving (Eq, Ord)

instance Show Selector where
  show (StringSel s) = s
  show (IntSel i) = show i

instance Show Reference where
  show (Reference sels) = intercalate "." (map show sels)

emptyRef :: Reference
emptyRef = Reference []

headSel :: Reference -> Maybe Selector
headSel (Reference []) = Nothing
headSel (Reference sels) = Just $ sels !! 0

tailRef :: Reference -> Maybe Reference
tailRef (Reference []) = Nothing
tailRef (Reference sels) = Just $ Reference (tail sels)

appendRefs ::
  -- | front
  Reference ->
  -- | back
  Reference ->
  Reference
appendRefs (Reference xs) (Reference ys) = Reference (xs ++ ys)

isRefEmpty :: Reference -> Bool
isRefEmpty (Reference []) = True
isRefEmpty _ = False

refToAddr :: Reference -> TreeAddr
refToAddr (Reference sels) = addrFromList $ map selToTASeg sels

selToTASeg :: Selector -> TASeg
selToTASeg (StringSel s) = StructTASeg $ StringTASeg s
selToTASeg (IntSel i) = IndexTASeg i

-- | TASeg is paired with a tree node.
data TASeg
  = -- RootTASeg is a special segment that represents the root of the addr.
    -- It is crucial to distinguish between the absolute addr and the relative addr.
    RootTASeg
  | StructTASeg StructTASeg
  | IndexTASeg Int
  | DisjDefaultTASeg
  | DisjDisjunctTASeg Int
  | -- | SubValTASeg is used to represent the only sub value of a value.
    SubValTASeg
  | -- | MutableArgTASeg is different in that the seg would be omitted when canonicalizing the addr.
    MutableArgTASeg Int
  | ComprehTASeg ComprehTASeg
  | ParentTASeg
  | TempTASeg
  deriving (Eq, Ord)

instance Show TASeg where
  show RootTASeg = "/"
  show (StructTASeg s) = show s
  show (IndexTASeg i) = "i" ++ show i
  show DisjDefaultTASeg = "d*"
  show (DisjDisjunctTASeg i) = "dj" ++ show i
  show (MutableArgTASeg i) = "fa" ++ show i
  show SubValTASeg = "sv"
  show ParentTASeg = ".."
  show TempTASeg = "tmp"
  show (ComprehTASeg s) = show s

data StructTASeg
  = -- | StringTASeg can be used to match both StringTASeg and LetTASeg, meaning it can be used to query either field or
    -- let binding.
    StringTASeg String
  | -- | The first is the OID, the second indicates the i-th value in the constraint.
    PatternTASeg Int Int
  | -- | DynFieldTASeg is used to represent a dynamic field.
    -- The first is the OID, the second indicates the i-th in the dynamic field.
    DynFieldTASeg Int Int
  | -- | A let binding is always indexed by the LetTASeg.
    LetTASeg
      -- | Identifier
      String
  | EmbedTASeg Int
  deriving (Eq, Ord)

instance Show StructTASeg where
  show (StringTASeg s) = s
  -- c stands for constraint.
  show (PatternTASeg i j) = "cns_" ++ show i ++ "_" ++ show j
  show (DynFieldTASeg i j) = "dyn_" ++ show i ++ "_" ++ show j
  show (LetTASeg s) = "let_" ++ s
  show (EmbedTASeg i) = "emb_" ++ show i

data ComprehTASeg
  = ComprehStartTASeg
  | ComprehIterClauseTASeg Int
  | ComprehStructTASeg
  deriving (Eq, Ord)

instance Show ComprehTASeg where
  show ComprehStartTASeg = "cph_start"
  show (ComprehIterClauseTASeg i) = "cph_iter" ++ show i
  show ComprehStructTASeg = "cph_val"

getStrFromSeg :: StructTASeg -> Maybe String
getStrFromSeg (StringTASeg s) = Just s
getStrFromSeg (LetTASeg s) = Just s
getStrFromSeg _ = Nothing

unaryOpTASeg :: TASeg
unaryOpTASeg = MutableArgTASeg 0

binOpLeftTASeg :: TASeg
binOpLeftTASeg = MutableArgTASeg 0

binOpRightTASeg :: TASeg
binOpRightTASeg = MutableArgTASeg 1

toBinOpTASeg :: BinOpDirect -> TASeg
toBinOpTASeg L = binOpLeftTASeg
toBinOpTASeg R = binOpRightTASeg

-- | Check if the segment is accessible, either by index or by field name.
isSegAccessible :: TASeg -> Bool
isSegAccessible seg = case seg of
  RootTASeg -> True
  (StructTASeg (StringTASeg _)) -> True
  (StructTASeg (LetTASeg _)) -> True
  (IndexTASeg _) -> True
  -- If a addr ends with a mutval segment, for example /p/sv, then it is accessible.
  -- It it the same as /p.
  SubValTASeg -> True
  -- If a addr ends with a disj default segment, for example /p/d*, then it is accessible.
  -- It it the same as /p.
  DisjDefaultTASeg -> True
  _ -> False

data BinOpDirect = L | R deriving (Eq, Ord)

instance Show BinOpDirect where
  show L = "L"
  show R = "R"

{- | TreeAddr is full addr to a value. The segments are stored in reverse order, meaning the last segment is the first in
the list.
-}
newtype TreeAddr = TreeAddr {getTreeSegs :: [TASeg]}
  deriving (Eq, Ord)

showTreeAddr :: TreeAddr -> String
showTreeAddr (TreeAddr []) = "."
showTreeAddr (TreeAddr segs) =
  let revSegs = reverse segs
   in if (revSegs !! 0) == RootTASeg
        then "/" ++ (intercalate "/" $ map show (drop 1 revSegs))
        else intercalate "/" $ map show (reverse segs)

instance Show TreeAddr where
  show = showTreeAddr

emptyTreeAddr :: TreeAddr
emptyTreeAddr = TreeAddr []

rootTreeAddr :: TreeAddr
rootTreeAddr = TreeAddr [RootTASeg]

isTreeAddrEmpty :: TreeAddr -> Bool
isTreeAddrEmpty (TreeAddr []) = True
isTreeAddrEmpty _ = False

addrFromList :: [TASeg] -> TreeAddr
addrFromList segs = TreeAddr (reverse segs)

-- | Convert a TreeAddr to normal order list, meaning the first segment is the first in the list.
addrToNormOrdList :: TreeAddr -> [TASeg]
addrToNormOrdList (TreeAddr segs) = reverse segs

appendSeg :: TASeg -> TreeAddr -> TreeAddr
appendSeg seg (TreeAddr xs) = TreeAddr (seg : xs)

{- | Append the new addr to old addr.
new and old are reversed, such as [z, y, x] and [b, a]. The appended addr should be [z, y, x, b, a], which is
a.b.x.y.z.
-}
appendTreeAddr :: TreeAddr -> TreeAddr -> TreeAddr
appendTreeAddr (TreeAddr new) (TreeAddr old) = TreeAddr (new ++ old)

-- | Get the parent addr of a addr by removing the last segment.
initTreeAddr :: TreeAddr -> Maybe TreeAddr
initTreeAddr (TreeAddr []) = Nothing
initTreeAddr (TreeAddr xs) = Just $ TreeAddr (drop 1 xs)

-- | Canonicalize address by removing helper segments, such as Mutable argument or subval segments.
canonicalizeAddr :: TreeAddr -> TreeAddr
canonicalizeAddr (TreeAddr xs) = TreeAddr $ filter (not . isIgnored) xs
 where
  isIgnored :: TASeg -> Bool
  isIgnored (MutableArgTASeg _) = True
  isIgnored SubValTASeg = True
  isIgnored TempTASeg = True
  isIgnored _ = False

-- | Get the tail addr of a addr, excluding the head segment.
tailTreeAddr :: TreeAddr -> Maybe TreeAddr
tailTreeAddr (TreeAddr []) = Nothing
tailTreeAddr (TreeAddr xs) = Just $ TreeAddr (init xs)

{- | Get the last segment of a addr.
>>> lastSeg (TreeAddr [StringTASeg "a", StringTASeg "b"])
-}
lastSeg :: TreeAddr -> Maybe TASeg
lastSeg (TreeAddr []) = Nothing
lastSeg (TreeAddr xs) = Just $ xs !! 0

{- | Get the head segment of a addr.
>>> headSeg (TreeAddr [StringTASeg "a", StringTASeg "b"])
Just b
-}
headSeg :: TreeAddr -> Maybe TASeg
headSeg (TreeAddr []) = Nothing
headSeg (TreeAddr xs) = Just $ last xs

mergeTreeAddrs :: [TreeAddr] -> [TreeAddr] -> [TreeAddr]
mergeTreeAddrs p1 p2 = Set.toList $ Set.fromList (p1 ++ p2)

-- | Get the common prefix of two addrs.
prefixTreeAddr :: TreeAddr -> TreeAddr -> Maybe TreeAddr
prefixTreeAddr (TreeAddr pxs) (TreeAddr pys) = TreeAddr . reverse <$> go (reverse pxs) (reverse pys)
 where
  go :: [TASeg] -> [TASeg] -> Maybe [TASeg]
  go [] _ = Just []
  go _ [] = Just []
  go (x : xs) (y : ys) =
    if x == y
      then (x :) <$> go xs ys
      else Just []

{- | Get the relative addr from the first addr to the second addr.

For example, relTreeAddr (TreeAddr [StringTASeg "a", StringTASeg "b"]) (TreeAddr [StringTASeg "a", StringTASeg "c"])
returns TreeAddr [ParentTASeg, StringTASeg "c"]
-}
relTreeAddr ::
  -- | px, first addr
  TreeAddr ->
  -- | py, second addr
  TreeAddr ->
  TreeAddr
relTreeAddr px py =
  let prefixLen = maybe 0 (\(TreeAddr xs) -> length xs) (prefixTreeAddr px py)
      upDist = length (getTreeSegs px) - prefixLen
      pySegsRest = drop prefixLen (reverse (getTreeSegs py))
   in TreeAddr $ reverse $ replicate upDist ParentTASeg ++ pySegsRest

{- | Trim the address by cutting off the prefix.

If the second addr is not a prefix of the first addr or the first addr is shorter than the second addr, then the
first addr is returned.
-}
trimPrefixTreeAddr ::
  -- | address
  TreeAddr ->
  -- | prefix address
  TreeAddr ->
  TreeAddr
trimPrefixTreeAddr x pre
  | not (isPrefix pre x) = x
  | otherwise =
      let
        segs = reverse $ getTreeSegs x
        prelen = length $ getTreeSegs pre
       in
        TreeAddr $ reverse $ drop prelen segs

-- | Check if addr x is a prefix of addr y.
isPrefix ::
  -- | x
  TreeAddr ->
  -- | y
  TreeAddr ->
  Bool
isPrefix x y =
  let TreeAddr xs = x
      TreeAddr ys = y
      rxs = reverse xs
      rys = reverse ys
   in if length rxs > length rys
        then False
        else take (length rxs) rys == rxs

depsHasCycle :: [(TreeAddr, TreeAddr)] -> Bool
depsHasCycle ps = hasCycle edges
 where
  depMap = Map.fromListWith (++) (map (\(k, v) -> (k, [v])) ps)
  edges = Map.toList depMap

hasCycle :: [(TreeAddr, [TreeAddr])] -> Bool
hasCycle edges = any isCycle (stronglyConnComp edgesForGraph)
 where
  edgesForGraph = map (\(k, vs) -> ((), k, vs)) edges

  isCycle (CyclicSCC _) = True
  isCycle _ = False

-- | Check if the addr is accessible, either by index or by field name.
isTreeAddrAccessible :: TreeAddr -> Bool
isTreeAddrAccessible (TreeAddr xs) = all isSegAccessible xs

{- | Convert the address to referable address.

Referable address is the address that a value can be referred to in the CUE code.

SubValSeg will be removed as once the value it points to become concrete, the path to the value will no longer have the
sub value segment. The referable address must be valid for both cases.

If the address contains any mutable arg segment, then the address is not referable.
-}
referableAddr :: TreeAddr -> Maybe TreeAddr
referableAddr p =
  let
    ysM =
      foldr
        ( \seg acc ->
            if isSegArg seg || isNothing acc
              then Nothing
              else Just $ seg : fromJust acc
        )
        (Just [])
        (getTreeSegs $ noSubValAddr p)
   in
    TreeAddr <$> ysM
 where
  isSegArg (MutableArgTASeg _) = True
  isSegArg _ = False

noSubValAddr :: TreeAddr -> TreeAddr
noSubValAddr (TreeAddr segs) = TreeAddr $ filter (not . isSegSV) segs
 where
  isSegSV SubValTASeg = True
  isSegSV _ = False