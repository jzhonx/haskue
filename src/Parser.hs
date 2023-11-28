module Parser where

import AST
  ( BinaryOp (..),
    Expression (..),
    Literal (..),
    StringLit,
  )
import Text.ParserCombinators.Parsec
  ( Parser,
    char,
    digit,
    many,
    many1,
    noneOf,
    optionMaybe,
    parse,
    spaces,
    try,
    (<|>),
  )

parseCUE :: String -> Expression
parseCUE s =
  case parse parseExpr "" s of
    Left err -> error $ show err
    Right val -> val

parseExpr :: Parser Expression
parseExpr = do
  spaces
  e1 <- parseUnary
  spaces
  op' <- optionMaybe (char '&')
  case op' of
    Nothing -> return e1
    Just _ -> do
      spaces
      e2 <- parseExpr
      spaces
      return (BinaryOp Unify e1 e2)

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

parseField :: Parser (StringLit, Literal)
parseField = do
  spaces
  key <- parseString
  spaces
  _ <- char ':'
  spaces
  val <- parseLiteral
  spaces
  let x = case key of
        StringLit s -> s
        _ -> error "parseField: key is not a string"
  return (x, val)

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
