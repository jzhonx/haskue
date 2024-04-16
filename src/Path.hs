module Path where

import Data.Graph (SCC (CyclicSCC), stronglyConnComp)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data Selector
  = StringSelector String
  | ListSelector Int
  | UnaryOpSelector
  | BinOpSelector BinOpDirect
  deriving (Eq, Ord)

instance Show Selector where
  show (StringSelector s) = s
  show (ListSelector i) = show i
  show UnaryOpSelector = "u"
  show (BinOpSelector d) = show d

data BinOpDirect = L | R deriving (Eq, Ord)

instance Show BinOpDirect where
  show L = "L"
  show R = "R"

-- | Path is full path to a value. The selectors are stored in reverse order, meaning the last selector is the first in
-- the list.
newtype Path = Path [Selector] deriving (Eq, Ord)

showPath :: Path -> String
showPath (Path []) = "."
showPath (Path sels) = intercalate "." $ map show (reverse sels)

instance Show Path where
  show = showPath

emptyPath :: Path
emptyPath = Path []

pathFromList :: [Selector] -> Path
pathFromList sels = Path (reverse sels)

appendSel :: Selector -> Path -> Path
appendSel sel (Path xs) = Path (sel : xs)

-- | Get the parent path of a path.
initPath :: Path -> Maybe Path
initPath (Path []) = Nothing
initPath (Path xs) = Just $ Path (tail xs)

-- | Get the last selector of a path.
lastSel :: Path -> Maybe Selector
lastSel (Path []) = Nothing
lastSel (Path xs) = Just $ head xs

mergePaths :: [Path] -> [Path] -> [Path]
mergePaths p1 p2 = Set.toList $ Set.fromList (p1 ++ p2)

-- | Get relative path from ys to xs.
relPath :: Path -> Path -> Maybe Path
relPath (Path pxs) (Path pys) = Path . reverse <$> go (reverse pxs) (reverse pys)
  where
    go [] ys = Just ys
    go (x : xs) (y : ys)
      | x == y = go xs ys
      | otherwise = Nothing
    go _ _ = Nothing

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
