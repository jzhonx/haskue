{-# LANGUAGE ViewPatterns #-}

module Path where

import Data.List (intercalate)

data Selector = StringSel String | IntSel Int
  deriving (Eq, Ord)

{- ValPath is a list of selectors.

The selectors are not stored in reverse order.
-}
newtype ValPath = ValPath {getRefSels :: [Selector]}
  deriving (Eq, Ord)

instance Show Selector where
  show (StringSel s) = s
  show (IntSel i) = show i

instance Show ValPath where
  show (ValPath sels) = intercalate "." (map show sels)

emptyValPath :: ValPath
emptyValPath = ValPath []

headSel :: ValPath -> Maybe Selector
headSel (ValPath []) = Nothing
headSel (ValPath sels) = Just $ sels !! 0

tailValPath :: ValPath -> Maybe ValPath
tailValPath (ValPath []) = Nothing
tailValPath (ValPath sels) = Just $ ValPath (tail sels)

appendValPaths ::
  -- | front
  ValPath ->
  -- | back
  ValPath ->
  ValPath
appendValPaths (ValPath xs) (ValPath ys) = ValPath (xs ++ ys)

isValPathEmpty :: ValPath -> Bool
isValPathEmpty (ValPath []) = True
isValPathEmpty _ = False

valPathToAddr :: ValPath -> TreeAddr
valPathToAddr (ValPath sels) = addrFromList $ map selToTASeg sels

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
  | -- | The first is the ObjectID, the second indicates the i-th value in the constraint.
    PatternTASeg Int Int
  | -- | DynFieldTASeg is used to represent a dynamic field.
    -- The first is the ObjectID, the second indicates the i-th in the dynamic field.
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
  = ComprehIterClauseValTASeg Int
  | -- | Binding can not be accessed through addressing.
    ComprehIterBindingTASeg Int
  | ComprehIterValTASeg
  deriving (Eq, Ord)

instance Show ComprehTASeg where
  show (ComprehIterClauseValTASeg i) = "cph_cl" ++ show i
  show (ComprehIterBindingTASeg i) = "cph_b" ++ show i
  show ComprehIterValTASeg = "cph_v"

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

isSegDisj :: Path.TASeg -> Bool
isSegDisj (Path.DisjDisjunctTASeg _) = True
isSegDisj _ = False

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
appendTreeAddr ::
  -- | new addr to be appended to the old addr
  TreeAddr ->
  -- | old addr
  TreeAddr ->
  TreeAddr
appendTreeAddr (TreeAddr new) (TreeAddr old) = TreeAddr (new ++ old)

-- | Get the parent addr of a addr by removing the last segment.
initTreeAddr :: TreeAddr -> Maybe TreeAddr
initTreeAddr (TreeAddr []) = Nothing
initTreeAddr (TreeAddr xs) = Just $ TreeAddr (drop 1 xs)

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
trimPrefixTreeAddr pre x
  | not (isPrefix pre x) = x
  | otherwise =
      let
        segs = reverse $ getTreeSegs x
        prelen = length $ getTreeSegs pre
       in
        TreeAddr $ reverse $ drop prelen segs

-- | Check if the addr is accessible, either by index or by field name.
isTreeAddrAccessible :: TreeAddr -> Bool
isTreeAddrAccessible (TreeAddr xs) = all isSegAccessible xs

isInDisj :: Path.TreeAddr -> Bool
isInDisj (Path.TreeAddr xs) = any Path.isSegDisj xs

-- | Convert the addr to referable form which only contains string, int or root segments.
trimToReferable :: TreeAddr -> TreeAddr
trimToReferable (TreeAddr xs) = TreeAddr $ filter isSegReferable xs

isSegReferable :: TASeg -> Bool
isSegReferable (StructTASeg (getStrFromSeg -> Just _)) = True
isSegReferable (IndexTASeg _) = True
isSegReferable RootTASeg = True
-- isSegReferable (ComprehTASeg (ComprehIterBindingTASeg _)) = True
isSegReferable _ = False

{- | Get the referable address.

Referable address is the address that a value can be referred to in the CUE code. If the address contains any mutable
arg segment, then the address is not referable.
-}
getReferableAddr :: TreeAddr -> Maybe TreeAddr
getReferableAddr p =
  if not (all isSegReferable (getTreeSegs p))
    then Nothing
    else Just p

-- | A non-canonical segment is a segment that would not have to be existed to access to the value.
isSegNonCanonical :: TASeg -> Bool
isSegNonCanonical Path.SubValTASeg = True
isSegNonCanonical Path.DisjDefaultTASeg = True
isSegNonCanonical _ = False

{- | Trim the addr to a single value form.

Single value form is the addr that only contains a single value.
-}
trimToSingleValueTA :: TreeAddr -> TreeAddr
trimToSingleValueTA (TreeAddr xs) = TreeAddr $ filter isSingleVal xs
 where
  isSingleVal (MutableArgTASeg _) = False
  isSingleVal SubValTASeg = False
  isSingleVal (StructTASeg (EmbedTASeg _)) = False
  isSingleVal (DisjDisjunctTASeg _) = False
  -- \^ embed segment is a conjunct.
  isSingleVal _ = True

isSegIterBinding :: TASeg -> Bool
isSegIterBinding (ComprehTASeg (ComprehIterBindingTASeg _)) = True
isSegIterBinding _ = False

isPathIterBinding :: TreeAddr -> Bool
isPathIterBinding (TreeAddr xs) = any isSegIterBinding xs