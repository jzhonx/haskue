module Parser where

import AST
import Data.Maybe (fromJust)
import Text.ParserCombinators.Parsec
  ( Parser,
    chainr1,
    char,
    digit,
    many,
    many1,
    noneOf,
    oneOf,
    optionMaybe,
    parse,
    spaces,
    string,
    try,
    (<|>),
  )

parseCUE :: String -> Expression
parseCUE s =
  case parse expr "" s of
    Left err -> error $ show err
    Right val -> val

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
unaryOp = fmap (: []) (oneOf "+-!*")

unaryOpTable :: [(String, UnaryOp)]
unaryOpTable =
  [ ("+", Plus),
    ("-", Minus),
    ("!", Not),
    ("*", Star)
  ]

comment :: Parser ()
comment = do
  spaces
  _ <- string "//"
  _ <- many (noneOf "\n")
  _ <- char '\n'
  return ()

skipElements :: Parser ()
skipElements = try (comment >> spaces) <|> spaces

expr :: Parser Expression
expr = do
  skipElements
  e <- chainr1 unaryExpr' binOp'
  skipElements
  return e
  where
    binOp' = do
      skipElements
      -- the following order is the operator precedence order.
      op <-
        char '*'
          <|> char '/'
          <|> char '+'
          <|> char '-'
          <|> char '&'
          <|> char '|'
      skipElements
      return $ BinaryOpCons (fromJust $ lookup [op] binopTable)
    unaryExpr' = do
      e <- unaryExpr
      return $ UnaryExprCons e

unaryExpr :: Parser UnaryExpr
unaryExpr = do
  skipElements
  op' <- optionMaybe unaryOp
  skipElements
  case op' of
    Nothing -> fmap PrimaryExprCons primaryExpr
    Just op -> do
      e <- unaryExpr
      skipElements
      return $ UnaryOpCons (fromJust $ lookup op unaryOpTable) e

primaryExpr :: Parser PrimaryExpr
primaryExpr = do
  skipElements
  op <- operand
  skipElements
  return $ Operand op

operand :: Parser Operand
operand = do
  skipElements
  op <-
    fmap Literal literal
      <|> (OperandName . Identifier <$> identifier)
      <|> ( do
              _ <- char '('
              e <- expr
              _ <- char ')'
              return $ OpExpression e
          )
  skipElements
  return op

literal :: Parser Literal
literal = do
  skipElements
  lit <-
    parseInt
      <|> struct
      <|> bool
      <|> (StringLit . SimpleStringLit <$> stringLit)
      <|> try bottom
      <|> top
      <|> null'
  skipElements
  return lit

struct :: Parser Literal
struct = do
  skipElements
  _ <- char '{'
  fields <- many field
  _ <- char '}'
  skipElements
  return $ StructLit fields

labelName :: Parser String
labelName = undefined

letter :: Parser Char
letter = oneOf ['a' .. 'z'] <|> oneOf ['A' .. 'Z'] <|> char '_' <|> char '$'

identifier :: Parser String
identifier = do
  firstChar <- letter
  rest <- many (letter <|> digit)
  return $ firstChar : rest

field :: Parser (Label, Expression)
field = do
  skipElements
  ln <- (LabelID <$> identifier) <|> (LabelString <$> stringLit)
  skipElements
  _ <- char ':'
  skipElements
  e <- expr
  skipElements
  return ((Label . LabelName) ln, e)

stringLit :: Parser SimpleStringLit
stringLit = do
  _ <- char '"'
  s <- many (noneOf "\"")
  _ <- char '"'
  return s

parseInt :: Parser Literal
parseInt = do
  s <- many1 digit
  return $ IntLit (read s :: Integer)

bool :: Parser Literal
bool = do
  b <- string "true" <|> string "false"
  return $ BoolLit (b == "true")

top :: Parser Literal
top = do
  _ <- string "_"
  return TopLit

bottom :: Parser Literal
bottom = do
  _ <- string "_|_"
  return BottomLit

null' :: Parser Literal
null' = do
  _ <- string "null"
  return NullLit
