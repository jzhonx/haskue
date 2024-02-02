module Path where

import Data.List (intercalate)
import qualified Data.Set as Set

data Selector = StringSelector String deriving (Eq, Ord)

instance Show Selector where
  show (StringSelector s) = s

-- | Path is full path to a value.
newtype Path = Path [Selector] deriving (Eq, Ord)

showPath :: Path -> String
showPath (Path sels) = intercalate "." $ map (\(StringSelector s) -> s) (reverse sels)

instance Show Path where
  show = showPath

emptyPath :: Path
emptyPath = Path []

pathFromList :: [Selector] -> Path
pathFromList sels = Path (reverse sels)

appendSel :: Selector -> Path -> Path
appendSel sel (Path xs) = Path (sel : xs)

initPath :: Path -> Maybe Path
initPath (Path []) = Nothing
initPath (Path xs) = Just $ Path (tail xs)

lastSel :: Path -> Maybe Selector
lastSel (Path []) = Nothing
lastSel (Path xs) = Just $ head xs

mergePaths :: [(Path, Path)] -> [(Path, Path)] -> [(Path, Path)]
mergePaths p1 p2 = Set.toList $ Set.fromList (p1 ++ p2)
