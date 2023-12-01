module Value where

import Data.ByteString.Builder (Builder, char7, integerDec, string7)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)

data Value
  = String String
  | Int Integer
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
  show = show . buildValueStr

buildValueStr :: Value -> Builder
buildValueStr = buildValueStr' 0

buildValueStr' :: Int -> Value -> Builder
buildValueStr' _ (String s) = char7 '"' <> string7 s <> char7 '"'
buildValueStr' _ (Int i) = integerDec i
buildValueStr' ident (Struct orderedLabels edges) =
  buildStructStr ident (map (\label -> (label, edges Map.! label)) orderedLabels)
buildValueStr' _ (Disjunction d disjuncts)
  | isJust d = buildValueStr (fromJust d)
  -- disjuncts must have at least two elements
  | otherwise = foldl1 (\x y -> x <> string7 " | " <> y) (map buildValueStr disjuncts)
buildValueStr' _ (Bottom _) = string7 "_|_"

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
        <> buildValueStr' (ident + 1) val
        <> char7 '\n'
