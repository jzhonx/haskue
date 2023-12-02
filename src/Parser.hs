module Parser where

import AST
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
    try,
    (<|>),
  )

parseCUE :: String -> Expression
parseCUE s =
  case parse parseExpr "" s of
    Left err -> error $ show err
    Right val -> val

binOp :: Parser String
binOp =
  choice
    [ string "&",
      string "|",
      string "+",
      string "-",
      string "*",
      string "/"
    ]

binopTable :: [(String, BinaryOp)]
binopTable =
  [ ("&", Unify),
    ("|", Disjunction),
    ("+", Add),
    ("-", Sub),
    ("*", Mul),
    ("/", Div)
  ]

unaryOp :: Parser String
unaryOp =
  choice
    [ string "+",
      string "-",
      string "!",
      string "*"
    ]

unaryOpTable :: [(String, UnaryOp)]
unaryOpTable =
  [ ("+", Plus),
    ("-", Minus),
    ("!", Not),
    ("*", Star)
  ]

parseComment :: Parser ()
parseComment = do
  spaces
  _ <- string "//"
  _ <- many (noneOf "\n")
  _ <- char '\n'
  return ()

skipElements :: Parser ()
skipElements = try (parseComment >> spaces) <|> spaces

parseExpr :: Parser Expression
parseExpr = do
  skipElements
  e1 <- parseUnary
  skipElements
  op' <- optionMaybe binOp
  skipElements
  case op' of
    Nothing -> return $ UnaryExprCons e1
    Just op -> do
      e2 <- parseExpr
      skipElements
      return $ BinaryOpCons (fromJust $ lookup op binopTable) (UnaryExprCons e1) e2

parseUnary :: Parser UnaryExpr
parseUnary = do
  skipElements
  op' <- optionMaybe unaryOp
  skipElements
  case op' of
    Nothing -> fmap PrimaryExprCons parsePrimary
    Just op -> do
      e <- parseUnary
      skipElements
      return $ UnaryOpCons (fromJust $ lookup op unaryOpTable) e

parsePrimary :: Parser PrimaryExpr
parsePrimary = do
  skipElements
  op <- parseOperand
  skipElements
  return $ Operand op

parseOperand :: Parser Operand
parseOperand = do
  skipElements
  op <-
    fmap Literal parseLiteral
      <|> ( do
              _ <- char '('
              expr <- parseExpr
              _ <- char ')'
              return $ OpExpression expr
          )
  skipElements
  return op

parseLiteral :: Parser Literal
parseLiteral = do
  skipElements
  lit <-
    parseInt
      <|> parseStruct
      <|> parseBool
      <|> parseString
      <|> try parseBottom
      <|> parseTop
      <|> parseNull
  skipElements
  return lit

parseStruct :: Parser Literal
parseStruct = do
  skipElements
  _ <- char '{'
  fields <- many parseField
  _ <- char '}'
  skipElements
  return $ StructLit fields

parseField :: Parser (StringLit, Expression)
parseField = do
  skipElements
  key <- parseString
  skipElements
  _ <- char ':'
  skipElements
  e <- parseExpr
  skipElements
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

parseBool :: Parser Literal
parseBool = do
  b <- string "true" <|> string "false"
  return $ BoolLit (b == "true")

parseTop :: Parser Literal
parseTop = do
  _ <- string "_"
  return TopLit

parseBottom :: Parser Literal
parseBottom = do
  _ <- string "_|_"
  return BottomLit

parseNull :: Parser Literal
parseNull = do
  _ <- string "null"
  return NullLit
