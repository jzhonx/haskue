module Parser where

import AST
  ( BinaryOp (..),
    Expression (..),
    Literal (..),
    StringLit,
  )
import Data.Maybe (fromJust)
import Text.ParserCombinators.Parsec
  ( Parser,
    char,
    choice,
    digit,
    many,
    many1,
    noneOf,
    optionMaybe,
    parse,
    spaces,
    string,
    (<|>),
  )

parseCUE :: String -> Expression
parseCUE s =
  case parse parseExpr "" s of
    Left err -> error $ show err
    Right val -> val

operator :: Parser String
operator =
  choice
    [ string "&",
      string "+",
      string "-",
      string "*",
      string "/"
    ]

operatorsTable :: [(String, BinaryOp)]
operatorsTable =
  [ ("&", Unify),
    ("+", Add),
    ("-", Sub),
    ("*", Mul),
    ("/", Div)
  ]

parseExpr :: Parser Expression
parseExpr = do
  spaces
  e1 <- parseUnary
  spaces
  op' <- optionMaybe operator
  spaces
  case op' of
    Nothing -> return e1
    Just op -> do
      e2 <- parseExpr
      spaces
      return $ BinaryOp (fromJust $ lookup op operatorsTable) e1 e2

parseUnary :: Parser Expression
parseUnary = fmap UnaryExpr parseLiteral

parseLiteral :: Parser Literal
parseLiteral = do
  spaces
  lit <- parseInt <|> parseStruct <|> parseString
  spaces
  return lit

parseStruct :: Parser Literal
parseStruct = do
  spaces
  _ <- char '{'
  fields <- many parseField
  _ <- char '}'
  spaces
  return $ StructLit fields

parseField :: Parser (StringLit, Expression)
parseField = do
  spaces
  key <- parseString
  spaces
  _ <- char ':'
  spaces
  e <- parseExpr
  spaces
  let x = case key of
        StringLit s -> s
        _ -> error "parseField: key is not a string"
  return (x, e)

parseString :: Parser Literal
parseString = do
  _ <- char '"'
  s <- many (noneOf "\"")
  _ <- char '"'
  return $ StringLit s

parseInt :: Parser Literal
parseInt = do
  s <- many1 digit
  return $ IntLit (read s :: Integer)
