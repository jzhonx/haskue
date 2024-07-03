{-# LANGUAGE FlexibleContexts #-}

module Parser where

import AST
import Control.Monad.Except (MonadError, throwError)
import Data.Maybe (fromJust)
import Text.ParserCombinators.Parsec (
  Parser,
  chainl1,
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
  (<?>),
  (<|>),
 )
import Prelude hiding (GT, LT, null)

parseCUE :: (MonadError String m) => String -> m Expression
parseCUE s = case parse expr "" s of
  Left err -> throwError $ show err
  Right val -> return val

binopTable :: [(String, BinaryOp)]
binopTable =
  [ ("&", Unify)
  , ("|", Disjunction)
  , ("+", Add)
  , ("-", Sub)
  , ("*", Mul)
  , ("/", Div)
  , ("==", Equ)
  , ("!=", BinRelOp NE)
  ]

unaryOp :: Parser String
unaryOp =
  try (string "!=")
    <|> try (string "!~")
    <|> string "!"
    <|> try (string "<=")
    <|> string "<"
    <|> try (string ">=")
    <|> string ">"
    <|> string "=~"
    <|> string "+"
    <|> string "-"
    <|> string "*"

unaryOpTable :: [(String, UnaryOp)]
unaryOpTable =
  [ ("+", Plus)
  , ("-", Minus)
  , ("!", Not)
  , ("*", Star)
  , ("!=", UnaRelOp NE)
  , ("<", UnaRelOp AST.LT)
  , ("<=", UnaRelOp LE)
  , (">", UnaRelOp AST.GT)
  , (">=", UnaRelOp GE)
  , ("=~", UnaRelOp ReMatch)
  , ("!~", UnaRelOp ReNotMatch)
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
  e <- prec1
  skipElements
  return e
 where
  binOp :: Parser Expression -> Parser (Expression -> Expression -> Expression) -> Parser Expression
  binOp higher sep = do
    skipElements
    e <- chainl1 higher sep
    skipElements
    return e

  precedence :: Parser String -> Parser (Expression -> Expression -> Expression)
  precedence op = do
    skipElements
    s <- op
    skipElements
    return $ ExprBinaryOp (fromJust $ lookup s binopTable)

  prec7 :: Parser Expression
  prec7 = binOp (ExprUnaryExpr <$> unaryExpr) (precedence (string "*" <|> string "/"))

  prec6 :: Parser Expression
  prec6 = binOp prec7 (precedence (string "+" <|> string "-"))

  prec5 :: Parser Expression
  prec5 = binOp prec6 (precedence (string "==" <|> string "!="))

  prec2 :: Parser Expression
  prec2 = binOp prec5 (precedence (string "&"))

  prec1 :: Parser Expression
  prec1 = binOp prec2 (precedence (string "|"))

unaryExpr :: Parser UnaryExpr
unaryExpr = do
  skipElements
  opM <- optionMaybe unaryOp
  skipElements
  case opM of
    Nothing -> UnaryExprPrimaryExpr <$> primaryExpr
    Just op -> do
      e <- unaryExpr
      skipElements
      return $ UnaryExprUnaryOp (fromJust $ lookup op unaryOpTable) e

primaryExpr :: Parser PrimaryExpr
primaryExpr = do
  skipElements
  e <- chainPrimExpr primOperand selector
  skipElements
  return e
 where
  primOperand = PrimExprOperand <$> operand

  selector :: Parser (PrimaryExpr -> PrimaryExpr)
  selector = do
    _ <- char '.'
    sel <- (IDSelector <$> identifier) <|> (StringSelector <$> simpleStringLit)
    return $ \pe -> PrimExprSelector pe sel

chainPrimExpr :: Parser PrimaryExpr -> Parser (PrimaryExpr -> PrimaryExpr) -> Parser PrimaryExpr
chainPrimExpr p op = do
  x <- p
  rest x
 where
  rest x =
    ( do
        g <- op
        rest (g x)
    )
      <|> return x
      <?> "failed to parse chainPrimExpr"

operand :: Parser Operand
operand = do
  skipElements
  opd <-
    OpLiteral
      <$> literal
        <|> (OperandName . Identifier <$> identifier)
        <|> ( do
                _ <- char '('
                e <- expr
                _ <- char ')'
                return $ OpExpression e
            )
        <?> "failed to parse operand"
  skipElements
  return opd

literal :: Parser Literal
literal = do
  skipElements
  lit <-
    parseInt
      <|> struct
      <|> try bool
      <|> try (StringLit . SimpleStringLit <$> simpleStringLit)
      <|> try bottom
      <|> try top
      <|> try null
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
  ln <- (LabelID <$> identifier) <|> (LabelString <$> simpleStringLit)
  skipElements
  _ <- char ':'
  skipElements
  e <- expr
  skipElements
  return ((Label . LabelName) ln, e)

simpleStringLit :: Parser SimpleStringLit
simpleStringLit = do
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

null :: Parser Literal
null = do
  _ <- string "null"
  return NullLit
