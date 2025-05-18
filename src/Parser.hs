{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Parser where

import AST
import Control.Monad (void, when)
import Control.Monad.Except (MonadError, throwError)
import Data.Maybe (fromJust, isJust, isNothing)
import Text.Parsec (
  Parsec,
  chainl1,
  char,
  digit,
  getInput,
  lookAhead,
  many,
  many1,
  noneOf,
  oneOf,
  option,
  optionMaybe,
  optional,
  -- parserTrace,
  runParser,
  satisfy,
  setInput,
  skipMany,
  string,
  try,
  (<?>),
  (<|>),
 )
import Prelude hiding (GT, LT, lex, null)

type Parser a = Parsec String () a

data TokenType
  = TokenNone
  | TokenUnaryOp
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
  | TokenExclamation
  | TokenQuestionMark
  | TokenEllipsis
  deriving (Show, Eq, Enum)

type TokAttr a = (a, TokenType)

-- | Lexeme is a sequence of tokens ending with a sequence of whitespace.
data Lexeme a = Lexeme
  { lex :: a
  , lexType :: TokenType
  , lexNewLine :: Bool
  }
  deriving (Show)

instance Functor Lexeme where
  fmap f (Lexeme a t nl) = Lexeme (f a) t nl

emptyLexeme :: Lexeme ()
emptyLexeme = Lexeme () TokenNone False

parseExpr :: (MonadError String m) => String -> m Expression
parseExpr s = case runParser (entry expr) () "" s of
  Left err -> throwError $ show err
  Right res -> return $ lex res

parseSourceFile :: (MonadError String m) => String -> m SourceFile
parseSourceFile s = case runParser (entry sourceFile) () "" s of
  Left err -> throwError $ show err
  Right res -> return $ lex res

binopTable :: [(String, BinaryOp)]
binopTable =
  [ ("&", Unify)
  , ("|", Disjoin)
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

sourceFile :: Parser (Lexeme SourceFile)
sourceFile = do
  declLexes <- manyEndByComma decl Nothing
  -- null was hidden, so use the dumb way to check if the declLexes is empty.
  if length declLexes == 0
    then return $ SourceFile [] <$ emptyLexeme
    else return $ SourceFile (map lex declLexes) <$ last declLexes

entry :: Parser (Lexeme a) -> Parser (Lexeme a)
entry p = do
  _ <- skippable
  p

expr :: Parser (Lexeme Expression)
expr = do
  r <- prec1
  return r
 where
  binOp ::
    Parser (Lexeme Expression) ->
    Parser (Lexeme Expression -> Lexeme Expression -> Lexeme Expression) ->
    Parser (Lexeme Expression)
  binOp = chainl1

  precedence :: Parser String -> Parser (Lexeme Expression -> Lexeme Expression -> Lexeme Expression)
  precedence op = do
    opLex <- lexeme (binOpAdapt op)
    let _op = fromJust $ lookup (lex opLex) binopTable
    -- return the rightmost token type and newline status.
    return $ \l r -> r{lex = ExprBinaryOp _op (lex l) (lex r)}

  binOpAdapt :: Parser String -> Parser (TokAttr String)
  binOpAdapt op = (,TokenBinOp) <$> op

  prec7 :: Parser (Lexeme Expression)
  prec7 = binOp (fmap ExprUnaryExpr <$> unaryExpr) (precedence (string "*" <|> string "/"))

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
    Nothing -> fmap UnaryExprPrimaryExpr <$> primaryExpr
    Just Lexeme{lex = op} -> do
      ul <- unaryExpr
      let ue = UnaryExprUnaryOp (fromJust $ lookup op unaryOpTable) (lex ul)
      return $ ue <$ ul

primaryExpr :: Parser (Lexeme PrimaryExpr)
primaryExpr = chainPrimExpr primOperand (segment <|> index <|> arguments)
 where
  primOperand :: Parser (Lexeme PrimaryExpr)
  primOperand = fmap PrimExprOperand <$> operand

  segment :: Parser (Lexeme PrimaryExpr -> Lexeme PrimaryExpr)
  segment = do
    _ <- lexeme $ (,TokenDot) <$> char '.'
    selLex <-
      (fmap IDSelector <$> identifier)
        <|> (fmap StringSelector <$> litLexeme TokenString simpleStringLit)
    return $ \pLex -> PrimExprSelector (lex pLex) (lex selLex) <$ selLex

  index :: Parser (Lexeme PrimaryExpr -> Lexeme PrimaryExpr)
  index = do
    _ <- lexeme $ (,TokenLSquare) <$> char '['
    selLex <- expr
    rLex <- lexeme $ (,TokenRSquare) <$> char ']'
    return $ \pLex -> PrimExprIndex (lex pLex) (Index (lex selLex)) <$ rLex

  arguments :: Parser (Lexeme PrimaryExpr -> Lexeme PrimaryExpr)
  arguments = do
    _ <- lexeme $ (,TokenLParen) <$> char '('
    args <- many $ do
      eLex <- expr
      rparenMaybe <- lookAhead $ optionMaybe rparen
      case rparenMaybe of
        Just _ -> return eLex
        Nothing -> do
          _ <- comma
          return eLex
    rLex <- rparen
    let es :: [Expression]
        es = map lex args
    return $ \pLex -> PrimExprArguments (lex pLex) es <$ rLex

chainPrimExpr ::
  Parser (Lexeme PrimaryExpr) ->
  Parser (Lexeme PrimaryExpr -> Lexeme PrimaryExpr) ->
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
operand =
  (fmap OpLiteral <$> literal)
    <|> (fmap (OperandName . Identifier) <$> identifier)
    <|> ( do
            _ <- lparen
            eLex <- expr
            rLex <- rparen
            return $ OpExpression (lex eLex) <$ rLex
        )
    <?> "failed to parse operand"

lparen :: Parser (Lexeme Char)
lparen = lexeme $ (,TokenLParen) <$> (char '(' <?> "failed to parse left parenthesis")

rparen :: Parser (Lexeme Char)
rparen = lexeme $ (,TokenRParen) <$> (char ')' <?> "failed to parse right parenthesis")

literal :: Parser (Lexeme Literal)
literal = do
  try (litLexeme TokenFloat floatLit)
    <|> litLexeme TokenInt intLit
    <|> try (litLexeme TokenBool bool)
    <|> try (fmap (StringLit . SimpleStringLit) <$> litLexeme TokenString simpleStringLit)
    <|> try (litLexeme TokenBottom bottom)
    <|> try (litLexeme TokenTop top)
    <|> try (litLexeme TokenNull null)
    <|> (fmap LitStructLit <$> structLit)
    <|> list

identifier :: Parser (Lexeme String)
identifier =
  lexeme $
    ( do
        prefix <- string "#"
        part <- identPart
        return (prefix ++ fst part, TokenIdentifier)
    )
      <|> try
        ( do
            -- "_" is a valid identPart letter as well, so we use try to first match the identifier with a prefix.
            prefix <- string "_#"
            part <- identPart
            return (prefix ++ fst part, TokenIdentifier)
        )
      <|> identPart
 where
  identPart = do
    firstChar <- letter
    rest <- many (letter <|> digit)
    return (firstChar : rest, TokenIdentifier)

letter :: Parser Char
letter = oneOf ['a' .. 'z'] <|> oneOf ['A' .. 'Z'] <|> char '_' <|> char '$'

structLit :: Parser (Lexeme StructLit)
structLit = do
  _ <- lbrace
  decls <- manyEndByComma decl (Just rbrace)
  rLex <- rbrace
  let
    ds :: [Declaration]
    ds = map lex decls
  return $ StructLit ds <$ rLex

lbrace :: Parser (Lexeme Char)
lbrace = lexeme $ (,TokenLBrace) <$> (char '{' <?> "failed to parse left brace")

rbrace :: Parser (Lexeme Char)
rbrace = lexeme $ (,TokenRBrace) <$> (char '}' <?> "failed to parse right brace")

list :: Parser (Lexeme Literal)
list = do
  _ <- lsquare
  elements <- many $ do
    eLex <- embedding
    rsquareMaybe <- lookAhead $ optionMaybe rsquare
    case rsquareMaybe of
      Just _ -> return eLex
      Nothing -> do
        _ <- comma
        return eLex
  rLex <- rsquare
  let es :: [Embedding]
      es = map lex elements
  return $ ListLit (EmbeddingList es) <$ rLex

lsquare :: Parser (Lexeme Char)
lsquare = lexeme $ (,TokenLSquare) <$> (char '[' <?> "failed to parse left square")

rsquare :: Parser (Lexeme Char)
rsquare = lexeme $ (,TokenRSquare) <$> (char ']' <?> "failed to parse right square")

comma :: Parser (Lexeme Char)
comma = lexeme $ (,TokenComma) <$> (char ',' <?> "failed to parse comma")

decl :: Parser (Lexeme Declaration)
decl =
  try (fmap FieldDecl <$> field)
    -- let would not consume EllipsisDecl. But it could consume Embedding. So it needs "try".
    <|> try (fmap DeclLet <$> letClause)
    <|> (fmap EllipsisDecl <$> ellipsisDecl)
    <|> (fmap Embedding <$> embedding)

field :: Parser (Lexeme FieldDecl)
field = do
  lnx <- label
  -- labels might be in the form of "a: b: c: val". We need to try to match the b and c.
  otherxs <- many (try label)
  eLex <- expr
  let
    ln = lex lnx
    otherLns = map lex otherxs
  return $ Field (ln : otherLns) (lex eLex) <$ eLex
 where
  label :: Parser (Lexeme Label)
  label = do
    lLex <- labelExpr
    rLex <- lexeme $ (,TokenColon) <$> char ':'
    return $ Label (lex lLex) <$ rLex

labelExpr :: Parser (Lexeme LabelExpr)
labelExpr = labelPattern <|> labelNameConstraint

labelNameConstraint :: Parser (Lexeme LabelExpr)
labelNameConstraint = do
  lnlem <- labelName
  optionMaybe (questionMark <|> exclamation) >>= \case
    Just x ->
      if lexType x == TokenQuestionMark
        then return $ LabelName (lex lnlem) OptionalLabel <$ x
        else return $ LabelName (lex lnlem) RequiredLabel <$ x
    Nothing -> return $ fmap (`LabelName` RegularLabel) lnlem

labelPattern :: Parser (Lexeme LabelExpr)
labelPattern = do
  _ <- lsquare
  e <- expr
  r <- rsquare
  return $ LabelPattern (lex e) <$ r

questionMark :: Parser (Lexeme Char)
questionMark = lexeme $ (,TokenQuestionMark) <$> (char '?' <?> "failed to parse ?")

exclamation :: Parser (Lexeme Char)
exclamation = lexeme $ (,TokenExclamation) <$> (char '!' <?> "failed to parse !")

ellipsis :: Parser (Lexeme String)
ellipsis = lexeme $ (,TokenEllipsis) <$> (string "..." <?> "failed to parse ...")

ellipsisDecl :: Parser (Lexeme EllipsisDecl)
ellipsisDecl = do
  lLex <- ellipsis
  eLexM <- optionMaybe expr
  maybe
    (return $ Ellipsis Nothing <$ lLex)
    (\eLex -> return $ Ellipsis (Just $ lex eLex) <$ eLex)
    eLexM

embedding :: Parser (Lexeme Embedding)
embedding = try (fmap EmbedComprehension <$> comprehension) <|> aliasExpr
 where
  aliasExpr = do
    eLex <- expr
    return $ AliasExpr (lex eLex) <$ eLex

comprehension :: Parser (Lexeme Comprehension)
comprehension = do
  stLex <- startClause
  -- If start clause may have newline, or a real comma followed
  _ <- optional comma
  restClauses <- many $ do
    r <- clause
    _ <- optional comma
    return r

  structLex <- structLit
  let
    cls = Clauses (lex stLex) (map lex restClauses)
    c = Comprehension cls (lex structLex)
  return $ c <$ structLex

clause :: Parser (Lexeme Clause)
clause =
  try (fmap ClauseStartClause <$> startClause)
    <|> (fmap ClauseLetClause <$> letClause)
    <?> "failed to parse clause"

startClause :: Parser (Lexeme StartClause)
startClause = try guardClause <|> forClause <?> "failed to parse start clause"

guardClause :: Parser (Lexeme StartClause)
guardClause = do
  _ <- lexeme $ (,TokenString) <$> (string "if" <?> "failed to parse keyword if")
  eLex <- expr
  return $ GuardClause (lex eLex) <$ eLex

forClause :: Parser (Lexeme StartClause)
forClause = do
  _ <- lexeme $ (,TokenString) <$> (string "for" <?> "failed to parse keyword for")
  identLex <- identifier
  secIdentLexM <- optionMaybe $ do
    _ <- comma
    identifier
  _ <- lexeme $ (,TokenString) <$> (string "in" <?> "failed to parse keyword in")
  eLex <- expr
  return $ ForClause (lex identLex) (lex <$> secIdentLexM) (lex eLex) <$ eLex

letClause :: Parser (Lexeme LetClause)
letClause = do
  _ <- lexeme $ (,TokenString) <$> (string "let" <?> "failed to parse keyword let")
  identLex <- identifier
  _ <- lexeme $ (,TokenBinOp) <$> (char '=' <?> "failed to parse =")
  eLex <- expr
  return $ LetClause (lex identLex) (lex eLex) <$ eLex

labelName :: Parser (Lexeme LabelName)
labelName =
  (fmap LabelID <$> identifier)
    <|> (fmap LabelString <$> litLexeme TokenString simpleStringLit)
    <|> labelNameExpr

labelNameExpr :: Parser (Lexeme LabelName)
labelNameExpr = do
  _ <- lparen
  e <- expr
  r <- rparen
  return $ LabelNameExpr (lex e) <$ r

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

-- Predeclared identifiers

bool :: Parser Literal
bool = do
  b <- string "true" <|> string "false"
  return $ BoolLit (b == "true")

top :: Parser Literal
top = string "_" >> return TopLit

bottom :: Parser Literal
bottom = string "_|_" >> return BottomLit

null :: Parser Literal
null = string "null" >> return NullLit

-- Match white spaces. Return True if a newline is matched.
spaces :: Parser Bool
spaces = do
  nls <-
    many1
      ( (char ' ' >> return False)
          <|> (char '\t' >> return False)
          <|> (char '\n' >> return True)
      )
  return $ or nls

lineComment :: Parser ()
lineComment = do
  _ <- try $ string "//"
  skipMany (satisfy (/= '\n'))

skippable :: Parser Bool
skippable = do
  hasnls <- many (spaces <|> (lineComment >> return False))
  return $ or hasnls

lexeme :: Parser (TokAttr a) -> Parser (Lexeme a)
lexeme p = do
  (x, ltok) <- p
  hasnl <- skippable <?> "failed to parse white spaces and comments"
  -- According to the cuelang spec, a comma is added to the last token of a line if the token is
  -- - an identifier, keyword, or bottom
  -- - a number or string literal, including an interpolation
  -- - one of the characters ), ], }, or ?
  -- - an ellipsis ...
  let commaFound =
        hasnl
          && ltok
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
                   , TokenQuestionMark
                   , TokenEllipsis
                   ]
  when commaFound $ do
    s <- getInput
    setInput $ "," ++ s
  return $ Lexeme x ltok hasnl

-- | Match the grammar {p ","} but loose restriction on the last comma if the enclosing element is matched.
manyEndByComma :: Parser (Lexeme a) -> Maybe (Parser (Lexeme b)) -> Parser [Lexeme a]
manyEndByComma p enclosingM = do
  many $ do
    x <- p

    rM <- maybe (return Nothing) (lookAhead . optionMaybe) enclosingM
    -- If the enclosing element is not found, we need to consume the comma.
    when (isNothing rM) $ void comma
    return x