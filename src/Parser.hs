{-# LANGUAGE FlexibleContexts #-}

module Parser where

import           AST
import           Control.Monad.Except          (MonadError, throwError)
import           Data.Maybe                    (fromJust)
import           Text.Parsec                   (parserTrace, parserTraced)
import           Text.ParserCombinators.Parsec (Parser, chainl1, chainr1, char,
                                                digit, many, many1, noneOf,
                                                oneOf, optionMaybe, parse,
                                                spaces, string, try, (<?>),
                                                (<|>))

parseCUE :: (MonadError String m) => String -> m Expression
parseCUE s = case parse expr "" s of
  Left err  -> throwError $ show err
  Right val -> return val

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
  e <- chainr1 (ExprUnaryExpr <$> unaryExpr) binOpF
  skipElements
  return e
  where
    binOpF = do
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
      return $ ExprBinaryOp (fromJust $ lookup [op] binopTable)

unaryExpr :: Parser UnaryExpr
unaryExpr = do
  skipElements
  op' <- optionMaybe unaryOp
  skipElements
  case op' of
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
    OpLiteral <$> literal
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
      <|> bool
      <|> (StringLit . SimpleStringLit <$> simpleStringLit)
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

null' :: Parser Literal
null' = do
  _ <- string "null"
  return NullLit
