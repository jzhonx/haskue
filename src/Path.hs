module Path where

import qualified AST
import Data.Graph (SCC (CyclicSCC), stronglyConnComp)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data Selector
  = -- RootSelector is a special selector that represents the root of the path.
    -- It is crucial to distinguish between the absolute path and the relative path.
    RootSelector
  | ScopeSelector ScopeSelector
  | IndexSelector Int
  | -- FuncArgSelector is different in that the sel would be omitted when canonicalizing the path.
    FuncArgSelector Int
  | DisjDefaultSelector
  | DisjDisjunctSelector Int
  | ParentSelector
  deriving (Eq, Ord)

instance Show Selector where
  show RootSelector = "/"
  show (ScopeSelector s) = show s
  show (IndexSelector i) = show i
  show (FuncArgSelector i) = "a" ++ show i
  show (DisjDefaultSelector) = "d*"
  show (DisjDisjunctSelector i) = "dj" ++ show i
  show ParentSelector = ".."

data ScopeSelector
  = StringSelector String
  | DynamicSelector Int AST.Expression
  deriving (Eq)

instance Ord ScopeSelector where
  compare (StringSelector s1) (StringSelector s2) = compare s1 s2
  compare (StringSelector _) _ = LT
  compare _ (StringSelector _) = GT
  compare (DynamicSelector i1 _) (DynamicSelector i2 _) = compare i1 i2

instance Show ScopeSelector where
  show (StringSelector s) = s
  show (DynamicSelector i _) = "sd" ++ show i

unaryOpSelector :: Selector
unaryOpSelector = FuncArgSelector 0

binOpLeftSelector :: Selector
binOpLeftSelector = FuncArgSelector 0

binOpRightSelector :: Selector
binOpRightSelector = FuncArgSelector 1

toBinOpSelector :: BinOpDirect -> Selector
toBinOpSelector L = binOpLeftSelector
toBinOpSelector R = binOpRightSelector

data BinOpDirect = L | R deriving (Eq, Ord)

instance Show BinOpDirect where
  show L = "L"
  show R = "R"

{- | Path is full path to a value. The selectors are stored in reverse order, meaning the last selector is the first in
the list.
-}
newtype Path = Path
  { getPath :: [Selector]
  }
  deriving (Eq, Ord)

showPath :: Path -> String
showPath (Path []) = "."
showPath (Path sels) =
  let revSels = reverse sels
   in if (revSels !! 0) == RootSelector
        then "/" ++ (intercalate "/" $ map show (drop 1 revSels))
        else intercalate "/" $ map show (reverse sels)

instance Show Path where
  show = showPath

pathFromList :: [Selector] -> Path
pathFromList sels = Path (reverse sels)

appendSel :: Selector -> Path -> Path
appendSel sel (Path xs) = Path (sel : xs)

-- | Get the parent path of a path by removing the last selector.
initPath :: Path -> Maybe Path
initPath (Path []) = Nothing
initPath (Path xs) = Just $ Path (drop 1 xs)

-- | Canonicalize a path by removing operator selectors.
canonicalizePath :: Path -> Path
canonicalizePath (Path xs) = Path $ filter (not . isOperator) xs
 where
  isOperator :: Selector -> Bool
  isOperator (FuncArgSelector _) = True
  isOperator _ = False

-- | Get the tail path of a path, excluding the head selector.
tailPath :: Path -> Maybe Path
tailPath (Path []) = Nothing
tailPath (Path xs) = Just $ Path (init xs)

{- | Get the last selector of a path.
>>> lastSel (Path [StringSelector "a", StringSelector "b"])
-}
lastSel :: Path -> Maybe Selector
lastSel (Path []) = Nothing
lastSel (Path xs) = Just $ xs !! 0

{- | Get the head selector of a path.
>>> headSel (Path [StringSelector "a", StringSelector "b"])
Just b
-}
headSel :: Path -> Maybe Selector
headSel (Path []) = Nothing
headSel (Path xs) = Just $ last xs

mergePaths :: [Path] -> [Path] -> [Path]
mergePaths p1 p2 = Set.toList $ Set.fromList (p1 ++ p2)

-- | Get the common prefix of two paths.
prefixPath :: Path -> Path -> Maybe Path
prefixPath (Path pxs) (Path pys) = Path . reverse <$> go (reverse pxs) (reverse pys)
 where
  go :: [Selector] -> [Selector] -> Maybe [Selector]
  go [] _ = Just []
  go _ [] = Just []
  go (x : xs) (y : ys) =
    if x == y
      then (x :) <$> go xs ys
      else Just []

{- | Get the relative path from the first path to the second path.

@param px The first path. @param py The second path.

For example, relPath (Path [StringSelector "a", StringSelector "b"]) (Path [StringSelector "a", StringSelector "c"])
returns Path [ParentSelector, StringSelector "c"]
-}
relPath :: Path -> Path -> Path
relPath px py =
  let prefixLen = maybe 0 (\(Path xs) -> length xs) (prefixPath px py)
      upDist = length (getPath px) - prefixLen
      pySelsRest = drop prefixLen (reverse (getPath py))
   in Path $ reverse $ replicate upDist ParentSelector ++ pySelsRest

-- | Check if path x is a prefix of path y.
isPrefix :: Path -> Path -> Bool
isPrefix x y =
  let Path xs = x
      Path ys = y
      rxs = reverse xs
      rys = reverse ys
   in if length rxs > length rys
        then False
        else take (length rxs) rys == rxs

depsHasCycle :: [(Path, Path)] -> Bool
depsHasCycle ps = hasCycle edges
 where
  depMap = Map.fromListWith (++) (map (\(k, v) -> (k, [v])) ps)
  edges = Map.toList depMap

hasCycle :: [(Path, [Path])] -> Bool
hasCycle edges = any isCycle (stronglyConnComp edgesForGraph)
 where
  edgesForGraph = map (\(k, vs) -> ((), k, vs)) edges

  isCycle (CyclicSCC _) = True
  isCycle _ = False
