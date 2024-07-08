{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Parser where

import AST
import Control.Monad.Except (MonadError, throwError)
import Data.Maybe (fromJust)
import Text.Parsec (
  Parsec,
  chainl1,
  char,
  digit,
  eof,
  getState,
  many,
  many1,
  newline,
  noneOf,
  oneOf,
  optionMaybe,
  parse,
  runParser,
  satisfy,
  setState,
  skipMany,
  skipMany1,
  string,
  try,
  (<?>),
  (<|>),
 )
import Prelude hiding (GT, LT, null)

data ParseState = ParseState
  {
  }

type Parser a = Parsec String () a

data TokenType
  = TokenUnaryOp
  | TokenBinOp
  | TokenString
  | TokenInt
  | TokenBool
  | TokenFloat
  | TokenNull
  | TokenTop
  | TokenBottom
  | TokenIdentifier
  | TokenLParen
  | TokenRParen
  | TokenLBrace
  | TokenRBrace
  | TokenDot
  | TokenColon
  deriving (Show, Eq, Enum)

type TokAttr a = (a, TokenType)
type LexemeRes a = (a, TokenType, Bool)

getLexeme :: LexemeRes a -> a
getLexeme (a, _, _) = a

modLexemeRes :: (a -> b) -> LexemeRes a -> LexemeRes b
modLexemeRes f (a, b, c) = (f a, b, c)

parseCUE :: (MonadError String m) => String -> m Expression
parseCUE s = case runParser expr () "" s of
  Left err -> throwError $ show err
  Right res -> return $ getLexeme res

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

unaryOp :: Parser (LexemeRes String)
unaryOp =
  lexeme $
    (,TokenUnaryOp)
      <$> ( try (string "!=")
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
          )

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

skipElements :: Parser ()
skipElements = undefined

expr :: Parser (LexemeRes Expression)
expr = prec1
 where
  binOp ::
    Parser (LexemeRes Expression) ->
    Parser ((LexemeRes Expression) -> (LexemeRes Expression) -> (LexemeRes Expression)) ->
    Parser (LexemeRes Expression)
  binOp higher sep = chainl1 higher sep

  precedence :: Parser String -> Parser ((LexemeRes Expression) -> (LexemeRes Expression) -> (LexemeRes Expression))
  precedence op = do
    (s, _, _) <- lexeme (binOpAdapt op)
    let _op = fromJust $ lookup s binopTable
    -- return the rightmost token type and newline status.
    return $ \(l, _, _) (r, rtok, nl) -> (ExprBinaryOp _op l r, rtok, nl)

  binOpAdapt :: Parser String -> Parser (TokAttr String)
  binOpAdapt op = (,TokenBinOp) <$> op

  prec7 :: Parser (LexemeRes Expression)
  prec7 = binOp (modLexemeRes ExprUnaryExpr <$> unaryExpr) (precedence (string "*" <|> string "/"))

  prec6 :: Parser (LexemeRes Expression)
  prec6 = binOp prec7 (precedence (string "+" <|> string "-"))

  prec5 :: Parser (LexemeRes Expression)
  prec5 = binOp prec6 (precedence (string "==" <|> string "!="))

  prec2 :: Parser (LexemeRes Expression)
  prec2 = binOp prec5 (precedence (string "&"))

  prec1 :: Parser (LexemeRes Expression)
  prec1 = binOp prec2 (precedence (string "|"))

unaryExpr :: Parser (LexemeRes UnaryExpr)
unaryExpr = do
  opM <- optionMaybe unaryOp
  case opM of
    Nothing -> modLexemeRes UnaryExprPrimaryExpr <$> primaryExpr
    Just (op, _, _) -> do
      (e, tok, nl) <- unaryExpr
      let ue = UnaryExprUnaryOp (fromJust $ lookup op unaryOpTable) e
      return (ue, tok, nl)

primaryExpr :: Parser (LexemeRes PrimaryExpr)
primaryExpr = chainPrimExpr primOperand selector
 where
  primOperand :: Parser (LexemeRes PrimaryExpr)
  primOperand = modLexemeRes PrimExprOperand <$> operand

  selector :: Parser ((LexemeRes PrimaryExpr) -> (LexemeRes PrimaryExpr))
  selector = do
    _ <- lexeme $ (,TokenDot) <$> char '.'
    (sel, tok, nl) <-
      (modLexemeRes IDSelector <$> identifier)
        <|> (modLexemeRes StringSelector <$> (litLexeme TokenString simpleStringLit))
    return $ \(pe, _, _) -> (PrimExprSelector pe sel, tok, nl)

chainPrimExpr ::
  Parser (LexemeRes PrimaryExpr) ->
  Parser ((LexemeRes PrimaryExpr) -> (LexemeRes PrimaryExpr)) ->
  Parser (LexemeRes PrimaryExpr)
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

operand :: Parser (LexemeRes Operand)
operand = do
  opd <-
    (modLexemeRes OpLiteral <$> literal)
      <|> (modLexemeRes (OperandName . Identifier) <$> identifier)
      <|> lexeme
        ( do
            _ <- lexeme $ (,TokenLParen) <$> char '('
            (e, _, _) <- expr
            _ <- lexeme $ (,TokenRParen) <$> char ')'
            return $ (OpExpression e, TokenRParen)
        )
      <?> "failed to parse operand"
  return opd

literal :: Parser (LexemeRes Literal)
literal =
  try (litLexeme TokenFloat floatLit)
    <|> (litLexeme TokenInt intLit)
    <|> try (litLexeme TokenBool bool)
    <|> try (modLexemeRes (StringLit . SimpleStringLit) <$> (litLexeme TokenString simpleStringLit))
    <|> try (litLexeme TokenBottom bottom)
    <|> try (litLexeme TokenTop top)
    <|> try (litLexeme TokenNull null)
    <|> struct

identifier :: Parser (LexemeRes String)
identifier = lexeme $ do
  firstChar <- letter
  rest <- many (letter <|> digit)
  return (firstChar : rest, TokenIdentifier)

letter :: Parser Char
letter = oneOf ['a' .. 'z'] <|> oneOf ['A' .. 'Z'] <|> char '_' <|> char '$'

struct :: Parser (LexemeRes Literal)
struct = do
  _ <- lexeme $ (,TokenLBrace) <$> char '{'
  decls <- many decl
  (_, _, nl) <- lexeme $ (,TokenRBrace) <$> char '}'
  let
    ds :: [Declaration]
    ds = map (\x -> getLexeme x) decls
  return (StructLit ds, TokenRBrace, nl)

decl :: Parser (LexemeRes Declaration)
decl = do
  (d, tok, nl) <- field
  return (FieldDecl d, tok, nl)

labelName :: Parser String
labelName = undefined

field :: Parser (LexemeRes FieldDecl)
field = do
  (ln, _, _) <-
    (modLexemeRes LabelID <$> identifier) <|> (modLexemeRes LabelString <$> (litLexeme TokenString simpleStringLit))
  _ <- lexeme $ (,TokenColon) <$> char ':'
  (e, tok, nl) <- expr
  return (Field ((Label . LabelName) ln) e, tok, nl)

litLexeme :: TokenType -> Parser a -> Parser (LexemeRes a)
litLexeme t p = lexeme $ do
  lit <- p
  return (lit, t)

simpleStringLit :: Parser SimpleStringLit
simpleStringLit = do
  _ <- char '"'
  s <- many (noneOf "\"")
  _ <- char '"'
  return s

intLit :: Parser Literal
intLit = do
  s <- many1 digit
  return $ IntLit (read s :: Integer)

floatLit :: Parser Literal
floatLit = do
  i <- many1 digit
  _ <- char '.'
  f <- many1 digit
  return $ FloatLit (read (i ++ "." ++ f) :: Double)

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

spaces :: Parser Bool
spaces = do
  isnl <-
    many1
      ( (char ' ' >> return False)
          <|> (char '\t' >> return False)
          <|> (char '\n' >> return True)
      )
  return $ any (== True) isnl

lineComment :: Parser ()
lineComment = do
  _ <- try $ string "//"
  skipMany (satisfy (/= '\n'))

skippable :: Parser Bool
skippable = do
  hasnls <- many (spaces <|> (lineComment >> return False))
  return $ any (== True) hasnls

lexeme :: Parser (TokAttr a) -> Parser (LexemeRes a)
lexeme p = do
  (x, ltok) <- p
  hasnl <- skippable
  return (x, ltok, hasnl)
