module Value where

import Data.ByteString.Builder (Builder, char7, integerDec, string7)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)

data Value
  = String String
  | Int Integer
  | Bool Bool
  | Struct
      { getOrderedLabels :: [String],
        getEdges :: Map.Map String Value
      }
  | Disjunction
      { getDefault :: Maybe Value,
        getDisjuncts :: [Value]
      }
  | Bottom String

instance Show Value where
  show (String s) = s
  show (Int i) = show i
  show (Bool b) = show b
  show (Struct orderedLabels edges) = "{ labels:" ++ show orderedLabels ++ ", edges: " ++ show edges ++ "}"
  show (Disjunction d disjuncts) = "Disjunction: " ++ show d ++ " " ++ show disjuncts
  show (Bottom msg) = "_|_: " ++ msg

instance Eq Value where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) (Struct orderedLabels1 edges1) (Struct orderedLabels2 edges2) =
    orderedLabels1 == orderedLabels2 && edges1 == edges2
  (==) (Disjunction d1 disjuncts1) (Disjunction d2 disjuncts2) =
    d1 == d2 && disjuncts1 == disjuncts2
  (==) (Bottom _) (Bottom _) = True
  (==) _ _ = False

buildCUEStr :: Value -> Builder
buildCUEStr = buildCUEStr' 0

buildCUEStr' :: Int -> Value -> Builder
buildCUEStr' _ (String s) = char7 '"' <> string7 s <> char7 '"'
buildCUEStr' _ (Int i) = integerDec i
buildCUEStr' _ (Bool b) = if b then string7 "true" else string7 "false"
buildCUEStr' ident (Struct orderedLabels edges) =
  buildStructStr ident (map (\label -> (label, edges Map.! label)) orderedLabels)
buildCUEStr' _ (Disjunction d disjuncts)
  | isJust d = buildCUEStr (fromJust d)
  -- disjuncts must have at least two elements
  | otherwise = foldl1 (\x y -> x <> string7 " | " <> y) (map buildCUEStr disjuncts)
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
