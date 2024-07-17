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
  lookAhead,
  many,
  many1,
  noneOf,
  oneOf,
  optionMaybe,
  runParser,
  satisfy,
  skipMany,
  string,
  try,
  unexpected,
  (<?>),
  (<|>),
 )
import Prelude hiding (GT, LT, null)

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
  | TokenLSquare
  | TokenRSquare
  | TokenDot
  | TokenColon
  | TokenComma
  deriving (Show, Eq, Enum)

type TokAttr a = (a, TokenType)
type Lexeme a = (a, TokenType, Bool)

getLexeme :: Lexeme a -> a
getLexeme (a, _, _) = a

modLexemeRes :: (a -> b) -> Lexeme a -> Lexeme b
modLexemeRes f (a, b, c) = (f a, b, c)

parseCUE :: (MonadError String m) => String -> m Expression
parseCUE s = case runParser entry () "" s of
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

unaryOp :: Parser (Lexeme String)
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

entry :: Parser (Lexeme Expression)
entry = do
  _ <- skippable
  expr

expr :: Parser (Lexeme Expression)
expr = prec1
 where
  binOp ::
    Parser (Lexeme Expression) ->
    Parser ((Lexeme Expression) -> (Lexeme Expression) -> (Lexeme Expression)) ->
    Parser (Lexeme Expression)
  binOp higher sep = chainl1 higher sep

  precedence :: Parser String -> Parser ((Lexeme Expression) -> (Lexeme Expression) -> (Lexeme Expression))
  precedence op = do
    (s, _, _) <- lexeme (binOpAdapt op)
    let _op = fromJust $ lookup s binopTable
    -- return the rightmost token type and newline status.
    return $ \(l, _, _) (r, rtok, nl) -> (ExprBinaryOp _op l r, rtok, nl)

  binOpAdapt :: Parser String -> Parser (TokAttr String)
  binOpAdapt op = (,TokenBinOp) <$> op

  prec7 :: Parser (Lexeme Expression)
  prec7 = binOp (modLexemeRes ExprUnaryExpr <$> unaryExpr) (precedence (string "*" <|> string "/"))

  prec6 :: Parser (Lexeme Expression)
  prec6 = binOp prec7 (precedence (string "+" <|> string "-"))

  prec5 :: Parser (Lexeme Expression)
  prec5 = binOp prec6 (precedence (string "==" <|> string "!="))

  prec2 :: Parser (Lexeme Expression)
  prec2 = binOp prec5 (precedence (string "&"))

  prec1 :: Parser (Lexeme Expression)
  prec1 = binOp prec2 (precedence (string "|"))

unaryExpr :: Parser (Lexeme UnaryExpr)
unaryExpr = do
  opM <- optionMaybe unaryOp
  case opM of
    Nothing -> modLexemeRes UnaryExprPrimaryExpr <$> primaryExpr
    Just (op, _, _) -> do
      (e, tok, nl) <- unaryExpr
      let ue = UnaryExprUnaryOp (fromJust $ lookup op unaryOpTable) e
      return (ue, tok, nl)

primaryExpr :: Parser (Lexeme PrimaryExpr)
primaryExpr = chainPrimExpr primOperand (selector <|> index)
 where
  primOperand :: Parser (Lexeme PrimaryExpr)
  primOperand = modLexemeRes PrimExprOperand <$> operand

  selector :: Parser ((Lexeme PrimaryExpr) -> (Lexeme PrimaryExpr))
  selector = do
    _ <- lexeme $ (,TokenDot) <$> char '.'
    (sel, tok, nl) <-
      (modLexemeRes IDSelector <$> identifier)
        <|> (modLexemeRes StringSelector <$> (litLexeme TokenString simpleStringLit))
    return $ \(pe, _, _) -> (PrimExprSelector pe sel, tok, nl)

  index :: Parser ((Lexeme PrimaryExpr) -> (Lexeme PrimaryExpr))
  index = do
    _ <- lexeme $ (,TokenLSquare) <$> char '['
    (e, _, _) <- expr
    (_, tok, nl) <- lexeme $ (,TokenRSquare) <$> char ']'
    return $ \(pe, _, _) -> (PrimExprIndex pe (Index e), tok, nl)

chainPrimExpr ::
  Parser (Lexeme PrimaryExpr) ->
  Parser ((Lexeme PrimaryExpr) -> (Lexeme PrimaryExpr)) ->
  Parser (Lexeme PrimaryExpr)
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

operand :: Parser (Lexeme Operand)
operand = do
  opd <-
    (modLexemeRes OpLiteral <$> literal)
      <|> (modLexemeRes (OperandName . Identifier) <$> identifier)
      <|> ( do
              _ <- lexeme $ (,TokenLParen) <$> char '('
              (e, _, _) <- expr
              (_, _, nl) <- lexeme $ (,TokenRParen) <$> char ')'
              return $ (OpExpression e, TokenRParen, nl)
          )
      <?> "failed to parse operand"
  return opd

literal :: Parser (Lexeme Literal)
literal =
  try (litLexeme TokenFloat floatLit)
    <|> (litLexeme TokenInt intLit)
    <|> try (litLexeme TokenBool bool)
    <|> try (modLexemeRes (StringLit . SimpleStringLit) <$> (litLexeme TokenString simpleStringLit))
    <|> try (litLexeme TokenBottom bottom)
    <|> try (litLexeme TokenTop top)
    <|> try (litLexeme TokenNull null)
    <|> struct
    <|> list

identifier :: Parser (Lexeme String)
identifier = lexeme $ do
  firstChar <- letter
  rest <- many (letter <|> digit)
  return (firstChar : rest, TokenIdentifier)

letter :: Parser Char
letter = oneOf ['a' .. 'z'] <|> oneOf ['A' .. 'Z'] <|> char '_' <|> char '$'

struct :: Parser (Lexeme Literal)
struct = do
  _ <- lexeme $ (,TokenLBrace) <$> char '{'
  decls <- many $ do
    (r, tok, nl) <- decl
    rbraceMaybe <- lookAhead $ optionMaybe rbrace
    case rbraceMaybe of
      Just _ -> return (r, tok, nl)
      Nothing -> do
        _ <- comma tok nl
        return (r, tok, nl)
  (_, _, nl) <- rbrace
  let
    ds :: [Declaration]
    ds = map (\x -> getLexeme x) decls
  return (StructLit ds, TokenRBrace, nl)

rbrace :: Parser (Lexeme Char)
rbrace = lexeme $ (,TokenRBrace) <$> (char '}' <?> "failed to parse right brace")

list :: Parser (Lexeme Literal)
list = do
  _ <- lexeme $ (,TokenLSquare) <$> char '['
  elements <- many $ do
    (r, tok, nl) <- expr
    rsquareMaybe <- lookAhead $ optionMaybe rsquare
    case rsquareMaybe of
      Just _ -> return (r, tok, nl)
      Nothing -> do
        _ <- comma tok nl
        return (r, tok, nl)
  (_, _, nl) <- rsquare
  let es :: [Embedding]
      es = map (\x -> getLexeme x) elements
  return (ListLit (EmbeddingList es), TokenRSquare, nl)

rsquare :: Parser (Lexeme Char)
rsquare = lexeme $ (,TokenRSquare) <$> (char ']' <?> "failed to parse right square")

comma :: TokenType -> Bool -> Parser (Lexeme ())
comma tok nl = do
  commaMaybe <- optionMaybe $ lexeme $ (,TokenComma) <$> (char ',' <?> "failed to parse comma")
  case commaMaybe of
    Just _ -> return ((), tok, nl)
    -- According to the cuelang spec, a comma is added to the last token of a line if the token is
    -- - an identifier, keyword, or bottom
    -- - a number or string literal, including an interpolation
    -- - one of the characters ), ], }, or ?
    -- - an ellipsis ...
    Nothing ->
      if nl
        && tok
          `elem` [ TokenIdentifier
                 , TokenTop -- Top is indentifier
                 , TokenNull -- Null is indentifier
                 , TokenBottom
                 , TokenInt
                 , TokenFloat
                 , TokenBool
                 , TokenString
                 , TokenRBrace
                 , TokenRParen
                 , TokenRSquare
                 ]
        then return ((), tok, nl)
        else unexpected "failed to parse comma"

decl :: Parser (Lexeme Declaration)
decl =
  (modLexemeRes FieldDecl <$> field) <|> (modLexemeRes Embedding <$> expr)

labelName :: Parser String
labelName = undefined

field :: Parser (Lexeme FieldDecl)
field = do
  lnx <- label
  otherxs <- many (try label)
  (e, tok, nl) <- expr
  let
    ln = getLexeme lnx
    otherLns = map (\x -> getLexeme x) otherxs
  return (Field (ln : otherLns) e, tok, nl)
 where
  label :: Parser (Lexeme Label)
  label = do
    (ln, _, _) <-
      (modLexemeRes LabelID <$> identifier)
        <|> (modLexemeRes LabelString <$> (litLexeme TokenString simpleStringLit))
    (_, tok, nl) <- lexeme $ (,TokenColon) <$> char ':'
    return ((Label . LabelName) ln, tok, nl)

litLexeme :: TokenType -> Parser a -> Parser (Lexeme a)
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
  nls <-
    many1
      ( (char ' ' >> return False)
          <|> (char '\t' >> return False)
          <|> (char '\n' >> return True)
      )
  return $ any (== True) nls

lineComment :: Parser ()
lineComment = do
  _ <- try $ string "//"
  skipMany (satisfy (/= '\n'))

skippable :: Parser Bool
skippable = do
  hasnls <- many (spaces <|> (lineComment >> return False))
  return $ any (== True) hasnls

lexeme :: Parser (TokAttr a) -> Parser (Lexeme a)
lexeme p = do
  (x, ltok) <- p
  hasnl <- skippable <?> "failed to parse white spaces and comments"
  return (x, ltok, hasnl)
