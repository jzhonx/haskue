{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Parser where

import AST
import Control.Monad (void, when)
import Control.Monad.Except (MonadError, throwError)
import Data.Maybe (fromJust, isNothing)
import qualified Data.Text as T
import Exception (throwErrSt)
import Text.Parsec (
  Parsec,
  chainl1,
  char,
  digit,
  eof,
  getInput,
  getPosition,
  getState,
  lookAhead,
  many,
  many1,
  noneOf,
  oneOf,
  optionMaybe,
  optional,
  parserTrace,
  parserTraced,
  runParser,
  satisfy,
  setInput,
  skipMany,
  sourceColumn,
  sourceLine,
  sourceName,
  string,
  try,
  (<?>),
  (<|>),
 )
import Text.Printf (printf)
import Prelude hiding (GT, LT, null)

type Parser a = Parsec String Int a

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
  | TokenBackslash
  deriving (Show, Eq, Enum)

type TokAttr a = (a, TokenType)

data WithTokenInfo a = WithTokenInfo
  { wtVal :: a
  , wtLastToken :: TokenType
  , wtNewLine :: Bool
  }
  deriving (Show, Functor)

type WithTokenPos a = WithTokenInfo (ASTN a)

emptyLexeme :: WithTokenInfo ()
emptyLexeme = WithTokenInfo () TokenNone False

parseExpr :: (MonadError String m) => String -> m Expression
parseExpr s = case runParser (entry expr) 0 "" s of
  Left err -> throwErrSt $ show err
  Right res -> return $ wtVal res

parseSourceFile :: (MonadError String m) => String -> String -> m SourceFile
parseSourceFile filename s = case runParser (entry sourceFile) 0 filename s of
  Left err -> throwErrSt $ show err
  Right res -> return $ wtVal res

binopTable :: [(String, BinaryOpNode)]
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

unaryOp :: Parser (WithTokenPos String)
unaryOp =
  lexeme "unaryOp" $
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

unaryOpTable :: [(String, UnaryOpNode)]
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

sourceFile :: Parser (WithTokenInfo SourceFile)
sourceFile = do
  declLexes <- manyEndByComma decl Nothing
  -- null was hidden, so use the dumb way to check if the declLexes is empty.
  if length declLexes == 0
    then return $ SourceFile [] <$ emptyLexeme
    else return $ SourceFile (map wtVal declLexes) <$ last declLexes

entry :: Parser (WithTokenInfo a) -> Parser (WithTokenInfo a)
entry p = do
  _ <- skippable
  p

expr :: Parser (WithTokenInfo Expression)
expr = do
  r <- prec1
  return r
 where
  binOp ::
    Parser (WithTokenInfo Expression) ->
    Parser (WithTokenInfo Expression -> WithTokenInfo Expression -> WithTokenInfo Expression) ->
    Parser (WithTokenInfo Expression)
  binOp = chainl1

  precedence ::
    Parser String ->
    Parser (WithTokenInfo Expression -> WithTokenInfo Expression -> WithTokenInfo Expression)
  precedence op = do
    opTp@WithTokenInfo{wtVal = opWp} <- lexeme "binOp" (binOpAdapt op)
    let _op = fmap (fromJust (lookup (anVal opWp) binopTable) <$) opTp
    -- return the rightmost token type and newline status.
    return $ \l r -> betweenTokenInfos l (ExprBinaryOp (wtVal _op) (wtVal l) (wtVal r)) r

  binOpAdapt :: Parser String -> Parser (TokAttr String)
  binOpAdapt op = (,TokenBinOp) <$> op

  prec7 :: Parser (WithTokenInfo Expression)
  prec7 = binOp (fmapSingleNode ExprUnaryExpr <$> unaryExpr) (precedence (string "*" <|> string "/"))

  prec6 :: Parser (WithTokenInfo Expression)
  prec6 = binOp prec7 (precedence (string "+" <|> string "-"))

  prec5 :: Parser (WithTokenInfo Expression)
  prec5 = binOp prec6 (precedence (string "==" <|> string "!="))

  prec2 :: Parser (WithTokenInfo Expression)
  prec2 = binOp prec5 (precedence (string "&"))

  prec1 :: Parser (WithTokenInfo Expression)
  prec1 = binOp prec2 (precedence (string "|"))

unaryExpr :: Parser (WithTokenInfo UnaryExpr)
unaryExpr = do
  opStrM <- optionMaybe unaryOp
  case opStrM of
    Nothing -> fmapSingleNode UnaryExprPrimaryExpr <$> primaryExpr
    Just opStrTp@WithTokenInfo{wtVal = op} -> do
      ul <- unaryExpr
      let
        opTp = fmap (fromJust (lookup (anVal op) unaryOpTable) <$) opStrTp
        ue = UnaryExprUnaryOp (wtVal opTp) (wtVal ul)
      return $ betweenTokenInfos opTp ue ul

primaryExpr :: Parser (WithTokenInfo PrimaryExpr)
primaryExpr = chainPrimExpr primOperand (segment <|> index <|> arguments)
 where
  primOperand :: Parser (WithTokenInfo PrimaryExpr)
  primOperand = fmapSingleNode PrimExprOperand <$> operand

  segment :: Parser (WithTokenInfo PrimaryExpr -> WithTokenInfo PrimaryExpr)
  segment = do
    l <- lexeme "." $ (,TokenDot) <$> char '.'
    sel <-
      (fmapSingleNode IDSelector <$> identifier)
        <|> ( do
                x <- simpleStringLit
                return $ fmapSingleNode StringSelector x
            )
    return $ \p -> betweenTokenInfos l (PrimExprSelector (wtVal p) (wtVal sel)) sel

  index :: Parser (WithTokenInfo PrimaryExpr -> WithTokenInfo PrimaryExpr)
  index = do
    l <- lexeme "[" $ (,TokenLSquare) <$> char '['
    sel <- expr
    r <- lexeme "]" $ (,TokenRSquare) <$> char ']'
    return $ \p ->
      betweenTokenInfos
        l
        (PrimExprIndex (wtVal p) (wtVal $ fmapSingleNode Index sel))
        r

  arguments :: Parser (WithTokenInfo PrimaryExpr -> WithTokenInfo PrimaryExpr)
  arguments = do
    l <- lexeme "(" $ (,TokenLParen) <$> char '('
    args <- many $ do
      eLex <- expr
      rparenMaybe <- lookAhead $ optionMaybe rparen
      case rparenMaybe of
        Just _ -> return eLex
        Nothing -> do
          _ <- comma
          return eLex
    r <- rparen
    let es :: [Expression]
        es = map wtVal args
    return $ \p -> betweenTokenInfos l (PrimExprArguments (wtVal p) es) r

chainPrimExpr ::
  Parser (WithTokenInfo PrimaryExpr) ->
  Parser (WithTokenInfo PrimaryExpr -> WithTokenInfo PrimaryExpr) ->
  Parser (WithTokenInfo PrimaryExpr)
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

operand :: Parser (WithTokenInfo Operand)
operand =
  (fmapSingleNode OpLiteral <$> literal)
    <|> ( do
            x <- identifier
            return $ fmapSingleNode OperandName (fmapSingleNode Identifier x)
        )
    -- <|> (fmapSingleNode OperandName <$> (composeNoPos Identifier <$> identifier))
    <|> ( do
            l <- lparen
            e <- expr
            r <- rparen
            return $ betweenTokenInfos l (OpExpression (wtVal e)) r
        )
    <?> "failed to parse operand"

lparen :: Parser (WithTokenPos Char)
lparen = lexeme "(" $ (,TokenLParen) <$> (char '(' <?> "failed to parse left parenthesis")

rparen :: Parser (WithTokenPos Char)
rparen = lexeme ")" $ (,TokenRParen) <$> (char ')' <?> "failed to parse right parenthesis")

literal :: Parser (WithTokenInfo Literal)
literal = do
  try (litLexeme TokenFloat floatLit)
    <|> litLexeme TokenInt intLit
    <|> try (litLexeme TokenBool bool)
    <|> try
      ( do
          x <- simpleStringLit
          let v = fmapSingleNode SimpleStringL x
          return $ fmapSingleNode StringLit v
      )
    <|> try (litLexeme TokenBottom bottom)
    <|> try (litLexeme TokenTop top)
    <|> try (litLexeme TokenNull null)
    <|> (fmapSingleNode LitStructLit <$> structLit)
    <|> (fmapSingleNode ListLit <$> list)

identifier :: Parser (WithTokenInfo Identifier)
identifier =
  lexeme "ident" $
    ( do
        prefix <- string "#"
        part <- identPart
        return (T.pack $ prefix ++ fst part, TokenIdentifier)
    )
      <|> try
        ( do
            -- "_" is a valid identPart letter as well, so we use try to first match the identifier with a prefix.
            prefix <- string "_#"
            part <- identPart
            return (T.pack $ prefix ++ fst part, TokenIdentifier)
        )
      <|> ( do
              (x, y) <- identPart
              return (T.pack x, y)
          )
 where
  identPart = do
    firstChar <- letter
    rest <- many (letter <|> digit)
    return (firstChar : rest, TokenIdentifier)

letter :: Parser Char
letter = oneOf ['a' .. 'z'] <|> oneOf ['A' .. 'Z'] <|> char '_' <|> char '$'

structLit :: Parser (WithTokenInfo StructLit)
structLit = do
  st <- lbrace
  decls <-
    manyEndByComma
      decl
      (Just rbrace)
  r <- rbrace
  let
    ds :: [Declaration]
    ds = map wtVal decls
  return $ betweenTokenInfos st (StructLit ds) r

lbrace :: Parser (WithTokenPos Char)
lbrace = lexeme "{" $ (,TokenLBrace) <$> (char '{' <?> "failed to parse left brace")

rbrace :: Parser (WithTokenPos Char)
rbrace = lexeme "}" $ do
  c <- char '}' <?> "failed to parse right brace"
  return (c, TokenRBrace)

list :: Parser (WithTokenInfo ElementList)
list = do
  st <- lsquare
  elements <- many $ do
    eLex <- embedding
    rsquareMaybe <- lookAhead $ optionMaybe rsquare
    case rsquareMaybe of
      Just _ -> return eLex
      Nothing -> do
        _ <- comma
        return eLex
  r <- rsquare
  let es :: [Embedding]
      es = map wtVal elements

  return $ betweenTokenInfos st (EmbeddingList es) r

lsquare :: Parser (WithTokenPos Char)
lsquare = lexeme "[" $ (,TokenLSquare) <$> (char '[' <?> "failed to parse left square")

rsquare :: Parser (WithTokenPos Char)
rsquare = lexeme "]" $ (,TokenRSquare) <$> (char ']' <?> "failed to parse right square")

comma :: Parser (WithTokenPos Char)
comma = lexeme "," $ (,TokenComma) <$> (char ',' <?> "failed to parse comma")

decl :: Parser (WithTokenInfo Declaration)
decl =
  try (fmapSingleNode FieldDecl <$> field)
    -- let would not consume EllipsisDecl. But it could consume Embedding. So it needs "try".
    <|> try (fmapSingleNode DeclLet <$> letClause)
    <|> (fmapSingleNode EllipsisDecl <$> ellipsisDecl)
    <|> (fmapSingleNode Embedding <$> embedding)
    <?> "failed to parse declaration"

field :: Parser (WithTokenInfo FieldDecl)
field = do
  lnx <- label
  -- labels might be in the form of "a: b: c: val". We need to try to match the b and c.
  otherxs <- many (try label)
  e <- expr
  let
    ln = wtVal lnx
    otherLns = map wtVal otherxs
  return $ fmap (Field (ln : otherLns) (wtVal e) <$) e
 where
  label :: Parser (WithTokenInfo Label)
  label = do
    lb <- labelExpr
    r <- lexeme ":" $ (,TokenColon) <$> char ':'
    return $ fmap (Label (wtVal lb) <$) r

labelExpr :: Parser (WithTokenInfo LabelExpr)
labelExpr = labelPattern <|> labelNameConstraint

labelNameConstraint :: Parser (WithTokenInfo LabelExpr)
labelNameConstraint = do
  lnlem <- labelName
  optionMaybe (questionMark <|> exclamation) >>= \case
    Just x ->
      if wtLastToken x == TokenQuestionMark
        then return $ fmapSingleNode (const $ LabelName (wtVal lnlem) OptionalLabel) x
        else return $ fmapSingleNode (const $ LabelName (wtVal lnlem) RequiredLabel) x
    Nothing -> return $ fmapSingleNode (const $ LabelName (wtVal lnlem) RegularLabel) lnlem

labelPattern :: Parser (WithTokenInfo LabelExpr)
labelPattern = do
  l <- lsquare
  e <- expr
  r <- rsquare
  return $ betweenTokenInfos l (LabelPattern (wtVal e)) r

questionMark :: Parser (WithTokenPos Char)
questionMark = lexeme "?" $ (,TokenQuestionMark) <$> (char '?' <?> "failed to parse ?")

exclamation :: Parser (WithTokenPos Char)
exclamation = lexeme "!" $ (,TokenExclamation) <$> (char '!' <?> "failed to parse !")

ellipsis :: Parser (WithTokenPos String)
ellipsis = lexeme "..." $ (,TokenEllipsis) <$> (string "..." <?> "failed to parse ...")

ellipsisDecl :: Parser (WithTokenInfo EllipsisDecl)
ellipsisDecl = do
  el <- ellipsis
  eNodeM <- optionMaybe expr
  maybe
    (return $ fmap (fmap (const $ Ellipsis Nothing)) el)
    (\eNode -> return $ fmapSingleNode (const $ Ellipsis (Just $ wtVal eNode)) eNode)
    eNodeM

embedding :: Parser (WithTokenInfo Embedding)
embedding =
  (fmapSingleNode EmbedComprehension <$> comprehension)
    <|> (fmapSingleNode AliasExpr <$> expr)

comprehension :: Parser (WithTokenInfo Comprehension)
comprehension = do
  stNode <- startClause
  -- If start clause may have newline, or a real comma followed
  _ <- optional comma
  restClauses <- many $ do
    r <- clause
    _ <- optional comma
    return r

  structNode <- structLit
  let
    cls =
      if length restClauses == 0
        then
          ASTN
            { anVal = Clauses (wtVal stNode) []
            , anPos = anPos $ wtVal stNode
            , anComments = []
            }
        else
          ASTN
            { anVal = Clauses (wtVal stNode) (map wtVal restClauses)
            , anPos =
                Just
                  ( Position
                      (posStart $ fromJust $ anPos $ wtVal stNode)
                      (posEnd $ fromJust $ anPos $ wtVal (last restClauses))
                      (posFile $ fromJust $ anPos $ wtVal stNode)
                  )
            , anComments = []
            }
    c = Comprehension cls (wtVal structNode)

  return $ betweenTokenInfos stNode c structNode

clause :: Parser (WithTokenInfo Clause)
clause =
  (fmapSingleNode ClauseStartClause <$> startClause)
    <|> (fmapSingleNode ClauseLetClause <$> letClause)
    <?> "failed to parse clause"

startClause :: Parser (WithTokenInfo StartClause)
startClause = guardClause <|> forClause <?> "failed to parse start clause"

guardClause :: Parser (WithTokenInfo StartClause)
guardClause = do
  st <- lexeme "if" $ (,TokenString) <$> (string "if" <?> "failed to parse keyword if")
  end <- expr
  return $ betweenTokenInfos st (GuardClause (wtVal end)) end

-- return $ GuardClause (wtVal eLex) <$ eLex

forClause :: Parser (WithTokenInfo StartClause)
forClause = do
  st <- lexeme "for" $ (,TokenString) <$> (string "for" <?> "failed to parse keyword for")
  ident <- identifier
  secIdentM <- optionMaybe $ do
    _ <- comma
    identifier
  _ <- lexeme "in" $ (,TokenString) <$> (string "in" <?> "failed to parse keyword in")
  end <- expr
  return $ betweenTokenInfos st (ForClause (wtVal ident) (wtVal <$> secIdentM) (wtVal end)) end

letClause :: Parser (WithTokenInfo LetClause)
letClause = do
  st <- lexeme "let" $ (,TokenString) <$> (string "let" <?> "failed to parse keyword let")
  identNode <- identifier
  _ <- lexeme "=" $ (,TokenBinOp) <$> (char '=' <?> "failed to parse =")
  end <- expr
  return $ betweenTokenInfos st (LetClause (wtVal identNode) (wtVal end)) end

labelName :: Parser (WithTokenInfo LabelName)
labelName =
  (fmapSingleNode LabelID <$> identifier)
    <|> ( do
            s <- simpleStringLit
            return $ fmapSingleNode LabelString s
        )
    <|> labelNameExpr

labelNameExpr :: Parser (WithTokenInfo LabelName)
labelNameExpr = do
  st <- lparen
  e <- expr
  r <- rparen
  return $ betweenTokenInfos st (LabelNameExpr (wtVal e)) r

litLexeme :: TokenType -> Parser a -> Parser (WithTokenPos a)
litLexeme t p = lexeme "literal" $ do
  lit <- p
  return (lit, t)

-- | Match a double quote without using the lexeme combinator.
doublequote :: Parser (WithTokenPos Char)
doublequote = do
  x <- wrapPos (char '"')
  return $ WithTokenInfo x TokenString False

simpleStringLit :: Parser (WithTokenInfo SimpleStringLit)
simpleStringLit = do
  -- Any spaces after the opening doublequote should not be ignored so we do not use lexeme here.
  st <- doublequote
  xs <-
    many
      ( ( interpolation <|> do
            x <- UnicodeVal <$> noneOf "\""
            return $ WithTokenInfo x TokenString False
        )
      )
  end <- lexeme "\"" $ (,TokenString) <$> (char '"' <?> "failed to parse doublequote character")

  return $ betweenTokenInfos st (SimpleStringLit (map wtVal xs)) end

backslash :: Parser (WithTokenPos Char)
backslash = lexeme "\\" $ (,TokenBackslash) <$> (char '\\' <?> "failed to parse backslash character")

interpolation :: Parser (WithTokenInfo SimpleStringLitSeg)
interpolation = do
  st <- backslash
  _ <- lparen
  e <- expr
  r <- rparen
  let v = betweenTokenInfos st (Interpolation (wtVal e)) r
  return $ fmap InterpolationStr v

intLit :: Parser LiteralNode
intLit = do
  s <- many1 digit
  return $ IntLit (read s :: Integer)

floatLit :: Parser LiteralNode
floatLit = do
  i <- many1 digit
  _ <- char '.'
  f <- many1 digit
  return $ FloatLit (read (i ++ "." ++ f) :: Double)

-- Predeclared identifiers

bool :: Parser LiteralNode
bool = do
  b <- string "true" <|> string "false"
  return $ BoolLit (b == "true")

top :: Parser LiteralNode
top = string "_" >> return TopLit

bottom :: Parser LiteralNode
bottom = string "_|_" >> return BottomLit

null :: Parser LiteralNode
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

-- | lineComment matches a line comment starting with "//" until the newline character.
lineComment :: Parser Bool
lineComment = do
  _ <- try $ string "//"
  skipMany (satisfy (/= '\n'))
  void (char '\n') <|> eof <?> "failed to parse line comment's newline or eof"
  return True

skippable :: Parser Bool
skippable = do
  -- line skippable is of the form, "{space}[//comment<end>]"
  -- first try the composite parser, then try each part separately.
  let lineSkippable = try (spaces >> lineComment) <|> lineComment <|> spaces
  hasnls <- many lineSkippable
  return $ or hasnls

-- | Parse a text that starts with a lexeme and ends with skippable.
lexeme :: String -> Parser (TokAttr a) -> Parser (WithTokenPos a)
lexeme name p = do
  wp <- wrapPos p
  skip name wp

skip :: String -> ASTN (TokAttr a) -> Parser (WithTokenPos a)
skip _ (ASTN{anVal = (x, ltok), anPos = posM}) = do
  hasnl <- (eof >> return True) <|> skippable <?> "failed to parse skippable"
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
  return $ annotatePos (fromJust posM) (WithTokenInfo x ltok hasnl)

-- | Match the grammar {p ","} but loose restriction on the last comma if the enclosing element is matched.
manyEndByComma :: Parser (WithTokenInfo a) -> Maybe (Parser (WithTokenInfo b)) -> Parser [WithTokenInfo a]
manyEndByComma p enclosingM = do
  many $ do
    x <- p

    rM <- maybe (return Nothing) (lookAhead . optionMaybe) enclosingM
    -- If the enclosing element is not found, we need to consume the comma.
    when (isNothing rM) $ do
      void comma
    return x

ptrace :: String -> Parser ()
ptrace s = do
  i <- getState
  parserTrace $ printf "id=%s, %s" (show i) s
  return ()

ptraced :: String -> Parser a -> Parser a
ptraced s p = do
  i <- getState
  parserTraced (printf "id=%s, %s" (show i) s) p

wrapPos :: Parser a -> Parser (ASTN a)
wrapPos p = do
  startPos <- getPosition
  x <- p
  endPos <- getPosition
  return $
    ASTN
      { anPos =
          Just
            ( Position
                ( SourcePos
                    (sourceLine startPos)
                    (sourceColumn startPos)
                )
                ( SourcePos
                    (sourceLine endPos)
                    (sourceColumn endPos)
                )
                (let n = sourceName startPos in if length n == 0 then Nothing else Just n)
            )
      , anComments = []
      , anVal = x
      }

-- | Attach a position to WithTokenInfo.
annotatePos :: Position -> WithTokenInfo a -> WithTokenInfo (ASTN a)
annotatePos pos = fmap (withPos pos)

-- | fmap a function over a node that only has one sub-node and turns it into a ASTN node of new type.
fmapSingleNode :: (ASTN a -> b) -> WithTokenInfo (ASTN a) -> WithTokenInfo (ASTN b)
fmapSingleNode f = fmap (\x -> withPos (fromJust $ anPos x) (f x))

betweenTokenInfos ::
  WithTokenInfo (ASTN a) -> b -> WithTokenInfo (ASTN c) -> WithTokenInfo (ASTN b)
betweenTokenInfos startTokInfo v endTokInfo =
  fmap
    ( const $
        withPos
          ( Position
              (posStart $ getPos startTokInfo)
              (posEnd $ getPos endTokInfo)
              (posFile $ getPos startTokInfo)
          )
          v
    )
    endTokInfo

getPos :: WithTokenInfo (ASTN a) -> Position
getPos WithTokenInfo{wtVal = ASTN{anPos = pos}} = fromJust pos