module Value where

import Data.ByteString.Builder (Builder, char7, integerDec, string7)

data Value
  = String String
  | Int Integer
  | Struct [(String, Value)]
  deriving (Eq)

buildValueStr :: Value -> Builder
buildValueStr = buildValueStr' 0

buildValueStr' :: Int -> Value -> Builder
buildValueStr' _ (String s) = string7 s
buildValueStr' _ (Int i) = integerDec i
buildValueStr' ident (Struct xs) = buildStructStr ident xs

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
