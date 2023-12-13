module Value where

import Data.ByteString.Builder (Builder, char7, integerDec, string7)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data Value
  = Top
  | String String
  | Int Integer
  | Bool Bool
  | Struct
      { orderedLabels :: [String],
        fields :: Map.Map String Value,
        identifiers :: Set.Set String,
        updaters :: [PendingUpdater]
      }
  | Disjunction
      { defaults :: [Value],
        disjuncts :: [Value]
      }
  | Null
  | Bottom String

instance Show Value where
  show (String s) = s
  show (Int i) = show i
  show (Bool b) = show b
  show Top = "_"
  show Null = "null"
  show (Struct ols fds _ _) = "{ labels:" ++ show ols ++ ", edges: " ++ show fds ++ "}"
  show (Disjunction dfs djs) = "Disjunction: " ++ show dfs ++ ", " ++ show djs
  show (Bottom msg) = "_|_: " ++ msg

instance Eq Value where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) (Struct orderedLabels1 edges1 _ _) (Struct orderedLabels2 edges2 _ _) =
    orderedLabels1 == orderedLabels2 && edges1 == edges2
  (==) (Disjunction defaults1 disjuncts1) (Disjunction defaults2 disjuncts2) =
    disjuncts1 == disjuncts2 && defaults1 == defaults2
  (==) (Bottom _) (Bottom _) = True
  (==) Top Top = True
  (==) Null Null = True
  (==) _ _ = False

buildCUEStr :: Value -> Builder
buildCUEStr = buildCUEStr' 0

buildCUEStr' :: Int -> Value -> Builder
buildCUEStr' _ (String s) = char7 '"' <> string7 s <> char7 '"'
buildCUEStr' _ (Int i) = integerDec i
buildCUEStr' _ (Bool b) = if b then string7 "true" else string7 "false"
buildCUEStr' _ Top = string7 "_"
buildCUEStr' _ Null = string7 "null"
buildCUEStr' ident (Struct ols fds _ _) =
  buildStructStr ident (map (\label -> (label, fds Map.! label)) ols)
buildCUEStr' ident (Disjunction dfs djs) =
  if null dfs
    then buildList djs
    else buildList dfs
  where
    buildList xs = foldl1 (\x y -> x <> string7 " | " <> y) (map (\d -> buildCUEStr' ident d) xs)
buildCUEStr' _ (Bottom _) = string7 "_|_"

buildStructStr :: Int -> [(String, Value)] -> Builder
buildStructStr ident xs =
  if null xs
    then string7 "{}"
    else
      char7 '{'
        <> char7 '\n'
        <> buildFieldsStr ident xs
        <> string7 (replicate (ident * 2) ' ')
        <> char7 '}'

buildFieldsStr :: Int -> [(String, Value)] -> Builder
buildFieldsStr _ [] = string7 ""
buildFieldsStr ident (x : xs) =
  f x <> buildFieldsStr ident xs
  where
    f (label, val) =
      string7 (replicate ((ident + 1) * 2) ' ')
        <> string7 label
        <> string7 ": "
        <> buildCUEStr' (ident + 1) val
        <> char7 '\n'

-- TODO: IntSelector
data Selector = StringSelector String

type Path = [Selector]

-- the first argument is the pending value.
-- the second argument is a list of paths to the unresolved references.
-- the third argument is a function that takes a list of values and returns a value.
data PendingUpdater = PendingUpdater Zipper [Path] ([Value] -> Value)

-- | Crumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type Crumb = (Selector, Value)

type Zipper = (Value, [Crumb])

goUp :: Zipper -> Maybe Zipper
goUp (_, []) = Nothing
goUp (_, (_, v') : vs) = Just (v', vs)

goTo :: Selector -> Zipper -> Maybe Zipper
goTo n@(StringSelector name) (val@(Struct _ edges _ _), vs) = do
  val' <- Map.lookup name edges
  return (val', (n, val) : vs)
goTo _ (_, _) = Nothing

-- modify :: (Value -> Value) -> ValueZipper -> Maybe ValueZipper
-- modify f (v, vs) = Just (f v, vs)

searchUp :: String -> Zipper -> Maybe Value
searchUp name (Struct _ edges _ _, []) = Map.lookup name edges
searchUp _ (_, []) = Nothing
searchUp name z = do
  z' <- goUp z
  searchUp name z'
