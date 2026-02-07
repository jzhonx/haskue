{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Syntax.Token where

import Control.DeepSeq (NFData)
import qualified Data.ByteString.Char8 as BC
import Data.Maybe (fromJust, isNothing)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import GHC.Generics (Generic)
import Text.Printf (printf)

data Token = Token
  { tkType :: TokenType
  , tkLoc :: Location
  , tkLiteral :: BC.ByteString
  }
  deriving (Eq, Generic, NFData)

instance Show Token where
  show (Token t loc lit) = printf "Token(%s, %s, \"%s\")" (show t) (show loc) (BC.unpack lit)

emptyToken :: Token
emptyToken = Token Illegal emptyLoc ""

mkTypeToken :: TokenType -> Token
mkTypeToken tt = Token tt emptyLoc (toByteString tt)

mkToken :: TokenType -> BC.ByteString -> Token
mkToken tt = Token tt emptyLoc

textIdentToken :: T.Text -> Token
textIdentToken t = Token Identifier emptyLoc (TE.encodeUtf8 t)

tkLiteralToText :: Token -> T.Text
tkLiteralToText = TE.decodeUtf8 . tkLiteral

prettyPrintTokens :: [Token] -> String
prettyPrintTokens tokens = unlines $ map show tokens

data TokenType
  = -- Single-character tokens
    LParen -- (
  | RParen -- )
  | LBrace -- {
  | RBrace -- }
  | LSquare -- [
  | RSquare -- ]
  | Dot -- .
  | Colon -- :
  | Comma -- ,
  | QuestionMark -- ?
  | Exclamation -- !
  | -- Operators
    Plus -- +
  | Minus -- -
  | Multiply
  | Divide -- /
  | Unify -- &
  | Disjoin
  | Equal -- ==
  | NotEqual -- !=
  | Less -- <
  | LessEqual -- <=
  | Greater -- >
  | GreaterEqual -- >=
  | Match -- =~
  | NotMatch -- !~
  | Assign -- =
  | Ellipsis -- ...
  | -- Literals
    String -- "hello"
  | MultiLineString -- """hello\nworld"""
  | Int -- 42
  | Float -- 3.14
  | Bool -- true or false
  | Null -- null
  | Bottom -- _|_
  | Interpolation -- \(...). Interpolation will only be produced by individual string literal scanner.
  | -- Keywords
    Package -- package
  | Import -- import
  | For -- for
  | In -- in
  | If -- if
  | Let -- let
  | -- Identifiers and other
    Identifier -- variable names, field names
  | EOF -- end of file
  | Illegal -- illegal token
  deriving (Show, Eq, Enum, Bounded, Generic, NFData)

toByteString :: TokenType -> BC.ByteString
toByteString tt = case tt of
  LParen -> "("
  RParen -> ")"
  LBrace -> "{"
  RBrace -> "}"
  LSquare -> "["
  RSquare -> "]"
  Dot -> "."
  Colon -> ":"
  Comma -> ","
  QuestionMark -> "?"
  Exclamation -> "!"
  Plus -> "+"
  Minus -> "-"
  Multiply -> "*"
  Divide -> "/"
  Unify -> "&"
  Disjoin -> "|"
  Equal -> "=="
  NotEqual -> "!="
  Less -> "<"
  LessEqual -> "<="
  Greater -> ">"
  GreaterEqual -> ">="
  Match -> "=~"
  NotMatch -> "!~"
  Assign -> "="
  Ellipsis -> "..."
  Null -> "null"
  Bottom -> "_|_"
  Package -> "package"
  Import -> "import"
  For -> "for"
  In -> "in"
  If -> "if"
  Let -> "let"
  _ -> ""

isTokenKeyword :: TokenType -> Bool
isTokenKeyword Package = True
isTokenKeyword Import = True
isTokenKeyword For = True
isTokenKeyword In = True
isTokenKeyword If = True
isTokenKeyword Let = True
isTokenKeyword _ = False

-- | Location in source code with line and column numbers
data Location = Location
  { line :: !Int
  , column :: !Int
  , filePath :: Maybe FilePath
  }
  deriving (Eq, Generic, NFData)

instance Show Location where
  -- If the file path is not available, just show -:line:column. "-" indicates standard input.
  show (Location l c fp) =
    let fpStr =
          if isNothing fp || null (fromJust fp) then "-" else show (fromJust fp)
     in printf "%s:%d:%d" fpStr l c

emptyLoc :: Location
emptyLoc = Location 0 0 Nothing