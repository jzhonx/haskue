module Path where

import Data.Graph (SCC (CyclicSCC), stronglyConnComp)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
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

data TASeg
  = -- RootTASeg is a special segment that represents the root of the addr.
    -- It is crucial to distinguish between the absolute addr and the relative addr.
    RootTASeg
  | StructTASeg StructTASeg
  | IndexTASeg Int
  | MutableTASeg MutableTASeg
  | DisjDefaultTASeg
  | DisjDisjunctTASeg Int
  | ParentTASeg
  | TempTASeg
  deriving (Eq, Ord)

instance Show TASeg where
  show RootTASeg = "/"
  show (StructTASeg s) = show s
  show (IndexTASeg i) = "i" ++ show i
  show (MutableTASeg f) = show f
  show DisjDefaultTASeg = "d*"
  show (DisjDisjunctTASeg i) = "dj" ++ show i
  show ParentTASeg = ".."
  show TempTASeg = "tmp"

data StructTASeg
  = -- | StringTASeg can be used to match both StringTASeg and LetTASeg, meaning it can be used to query either field or
    -- let binding.
    StringTASeg String
  | PatternTASeg Int
  | PendingTASeg Int
  | -- | A let binding is always indexed by the LetTASeg.
    LetTASeg
      -- | Identifier
      String
  deriving (Eq, Ord)

instance Show StructTASeg where
  show (StringTASeg s) = s
  show (PendingTASeg i) = "sp_" ++ show i
  -- c stands for constraint.
  show (PatternTASeg i) = "sc_" ++ show i
  show (LetTASeg s) = "let_" ++ s

getStrFromSeg :: StructTASeg -> Maybe String
getStrFromSeg (StringTASeg s) = Just s
getStrFromSeg (LetTASeg s) = Just s
getStrFromSeg _ = Nothing

-- MutableArgTASeg is different in that the seg would be omitted when canonicalizing the addr.
data MutableTASeg
  = MutableArgTASeg Int
  | MutableValTASeg
  deriving (Eq, Ord)

instance Show MutableTASeg where
  show (MutableArgTASeg i) = "fa" ++ show i
  show MutableValTASeg = "fv"

unaryOpTASeg :: TASeg
unaryOpTASeg = MutableTASeg $ MutableArgTASeg 0

binOpLeftTASeg :: TASeg
binOpLeftTASeg = MutableTASeg $ MutableArgTASeg 0

binOpRightTASeg :: TASeg
binOpRightTASeg = MutableTASeg $ MutableArgTASeg 1

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
  -- If a addr ends with a mutval segment, for example /p/fv, then it is accessible.
  -- It it the same as /p.
  (MutableTASeg MutableValTASeg) -> True
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
newtype TreeAddr = TreeAddr {getTreeAddr :: [TASeg]}
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

isTreeAddrEmpty :: TreeAddr -> Bool
isTreeAddrEmpty (TreeAddr []) = True
isTreeAddrEmpty _ = False

addrFromList :: [TASeg] -> TreeAddr
addrFromList segs = TreeAddr (reverse segs)

addrToList :: TreeAddr -> [TASeg]
addrToList (TreeAddr segs) = reverse segs

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

-- | Canonicalize a addr by removing operator segments.
canonicalizeAddr :: TreeAddr -> TreeAddr
canonicalizeAddr (TreeAddr xs) = TreeAddr $ filter (not . isIgnored) xs
 where
  isIgnored :: TASeg -> Bool
  isIgnored (MutableTASeg _) = True
  -- TODO: remove temp
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

@param px: The first addr.
@param py: The second addr.

For example, relTreeAddr (TreeAddr [StringTASeg "a", StringTASeg "b"]) (TreeAddr [StringTASeg "a", StringTASeg "c"])
returns TreeAddr [ParentTASeg, StringTASeg "c"]
-}
relTreeAddr :: TreeAddr -> TreeAddr -> TreeAddr
relTreeAddr px py =
  let prefixLen = maybe 0 (\(TreeAddr xs) -> length xs) (prefixTreeAddr px py)
      upDist = length (getTreeAddr px) - prefixLen
      pySegsRest = drop prefixLen (reverse (getTreeAddr py))
   in TreeAddr $ reverse $ replicate upDist ParentTASeg ++ pySegsRest

-- | Check if addr x is a prefix of addr y.
isPrefix :: TreeAddr -> TreeAddr -> Bool
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

hasTemp :: TreeAddr -> Bool
hasTemp (TreeAddr xs) = TempTASeg `elem` xs

-- | Check if the addr is accessible, either by index or by field name.
isTreeAddrAccessible :: TreeAddr -> Bool
isTreeAddrAccessible (TreeAddr xs) = all isSegAccessible xs

{- | Return the referable part of the addr by removing the mutable value segments.

For example, /p/fv should return /p.
-}
getReferableAddr :: TreeAddr -> TreeAddr
getReferableAddr p = TreeAddr $ filter (not . isMutValSeg) (getTreeAddr p)
 where
  isMutValSeg :: TASeg -> Bool
  isMutValSeg (MutableTASeg MutableValTASeg) = True
  isMutValSeg _ = False
