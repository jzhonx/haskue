{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Syntax.Parser where

import Control.Monad (void)
import qualified Data.ByteString.Char8 as BC
import qualified Data.Text as T
import Syntax.AST
import qualified Syntax.AST as AST
import Syntax.Scanner (partitionUnquotedStr, scanTokens)
import Syntax.Token
import qualified Syntax.Token as Token
import Text.Parsec (
  Parsec,
  chainl1,
  getState,
  lookAhead,
  many,
  optionMaybe,
  optional,
  parserTrace,
  parserTraced,
  runParser,
  try,
  unexpected,
  (<?>),
  (<|>),
 )
import Text.Parsec.Pos (newPos)
import Text.Parsec.Prim (token)
import Text.Printf (printf)
import Prelude hiding (GT, LT, null)

type Parser a = Parsec [Token] Int a

accept :: TokenType -> Parser Token
accept t = token show testPos testVal
 where
  testVal tok =
    if tkType tok == t
      then Just tok
      else Nothing
  testPos (Token{tkLoc = tkLoc}) = newPos (maybe "" id (filePath tkLoc)) (line tkLoc) (column tkLoc)

parseExpr :: [Token] -> Either String Expression
parseExpr tks = case runParser expr 0 "" tks of
  Left err -> Left $ show err
  Right res -> return res

parseSourceFile :: [Token] -> Either String SourceFile
parseSourceFile tks = case runParser sourceFile 0 "" tks of
  Left err -> Left $ show err
  Right res -> return res

sourceFile :: Parser SourceFile
sourceFile = SourceFile <$> decls

expr :: Parser Expression
expr = prec1
 where
  binOp ::
    Parser Expression ->
    Parser (Expression -> Expression -> Expression) ->
    Parser Expression
  binOp = chainl1

  precedence :: Parser Token -> Parser (Expression -> Expression -> Expression)
  precedence op = Binary <$> op

  prec7 :: Parser Expression
  prec7 = binOp (Unary <$> unaryExpr) (precedence (accept Multiply <|> accept Divide))

  prec6 :: Parser Expression
  prec6 = binOp prec7 (precedence (accept Plus <|> accept Minus))

  prec5 :: Parser Expression
  prec5 = binOp prec6 (precedence (accept Equal <|> accept NotEqual))

  prec2 :: Parser Expression
  prec2 = binOp prec5 (precedence (accept Unify))

  prec1 :: Parser Expression
  prec1 = binOp prec2 (precedence (accept Disjoin))

unaryExpr :: Parser UnaryExpr
unaryExpr = do
  opTokenM <- optionMaybe unaryOp
  case opTokenM of
    Nothing -> Primary <$> primaryExpr
    Just op -> UnaryOp op <$> unaryExpr

unaryOp :: Parser Token
unaryOp =
  accept NotEqual
    <|> accept NotMatch
    <|> accept Exclamation
    <|> accept LessEqual
    <|> accept Less
    <|> accept GreaterEqual
    <|> accept Greater
    <|> accept Match
    <|> accept Plus
    <|> accept Minus
    <|> accept Multiply

primaryExpr :: Parser PrimaryExpr
primaryExpr = chainPrimExpr primOperand (selector <|> index <|> arguments)
 where
  primOperand :: Parser PrimaryExpr
  primOperand = PrimExprOperand <$> operand

  selector :: Parser (PrimaryExpr -> PrimaryExpr)
  selector = do
    l <- dot
    sel <-
      (IDSelector <$> identifier)
        <|> (StringSelector <$> simpleStringLit)
    return $ \p -> PrimExprSelector p l.tkLoc sel

  index :: Parser (PrimaryExpr -> PrimaryExpr)
  index = do
    l <- lsquare
    sel <- expr
    r <- rsquare
    return $ \p -> PrimExprIndex p l.tkLoc sel r.tkLoc

  arguments :: Parser (PrimaryExpr -> PrimaryExpr)
  arguments = do
    l <- lparen
    args <- manyEndByComma expr rparen ")"
    r <- rparen
    return $ \p -> PrimExprArguments p l.tkLoc args r.tkLoc

identifier :: Parser Token
identifier = accept Token.Identifier <?> "failed to parse identifier"

chainPrimExpr ::
  Parser PrimaryExpr ->
  Parser (PrimaryExpr -> PrimaryExpr) ->
  Parser PrimaryExpr
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
operand =
  (OpLiteral <$> literal)
    <|> (OpName . OperandName <$> identifier)
    <|> ( do
            l <- lparen
            e <- expr
            r <- rparen
            return $ OpExpression l.tkLoc e r.tkLoc
        )
    <?> "failed to parse operand"

literal :: Parser Literal
literal =
  (LitBasic <$> basicLit)
    <|> (LitStruct <$> structLit)
    <|> (LitList <$> list)

basicLit :: Parser BasicLit
basicLit =
  (AST.IntLit <$> accept Token.Int)
    <|> (AST.FloatLit <$> accept Token.Float)
    <|> (AST.BoolLit <$> accept Token.Bool)
    <|> (AST.NullLit <$> accept Token.Null)
    <|> (AST.BottomLit <$> accept Token.Bottom)
    <|> (AST.StringLit <$> stringLit)

stringLit :: Parser StringLit
stringLit =
  (SimpleStringL <$> simpleStringLit)
    <|> (MultiLineStringL <$> multiLineStringLit)

structLit :: Parser StructLit
structLit = do
  l <- lbrace
  dcls <- decls
  r <- rbrace
  return $ StructLit l.tkLoc dcls r.tkLoc

decls :: Parser [Declaration]
decls = manyEndByComma decl rbrace "}"

list :: Parser ListLit
list = do
  l <- lsquare
  el <-
    ( do
        e <- ellipsisExpr
        _ <- optional comma
        return $ EllipsisList e
      )
      <|> ( do
              fstEmb <- embedding
              revL <- manyCommaElem []
              let xs = reverse revL
                  embeds = [e | ListCommaEmbedding e <- xs]
                  ellM = case [e | ListCommaEllipsis e <- xs] of
                    [] -> Nothing
                    [e] -> Just e
                    _ -> error "multiple ellipsis in list literal should have been rejected by parser"

              return $ EmbeddingList (fstEmb : embeds) ellM
          )
  r <- rsquare
  return $ ListLit l.tkLoc el r.tkLoc
 where
  -- manyCommaElem is used to parse the ",<elem>" structure.
  -- Given
  -- ListLit       = "[" [ ElementList [ "," ] ] "]" .
  -- ElementList   = Ellipsis | Embedding { "," Embedding } [ "," Ellipsis ] .
  -- When we are at ",", we don't know if it's followed by an Embedding or an Ellipsis, or it's the end of the list,
  -- which is indicated by "]". So we need to try all three possibilities.
  manyCommaElem revAcc =
    do
      m <- optionMaybe comma
      case m of
        Nothing -> do
          return revAcc
        Just _ ->
          ( do
              e <- embedding
              manyCommaElem (ListCommaEmbedding e : revAcc)
          )
            <|> ( do
                    e <- ellipsisExpr
                    manyCommaElem (ListCommaEllipsis e : revAcc)
                )
            <|> ( do
                    -- If it's not followed by an embedding or an ellipsis, it must be followed by a "]". We use
                    -- lookAhead to check if the next token is "]" without consuming it.
                    _ <- lookAhead rsquare <?> "expected embedding, ellipsis or ] after comma in list literal"
                    return revAcc
                )

data ListCommaElem
  = ListCommaEmbedding Embedding
  | ListCommaEllipsis EllipsisExpr

decl :: Parser Declaration
decl =
  try (FieldDecl <$> field)
    -- let would not consume EllipsisExpr. But it could consume Embedding. So it needs "try".
    <|> try (DeclLet <$> letClause)
    <|> (EllipsisExpr <$> ellipsisExpr)
    <|> (Embedding <$> embedding)
    <?> "failed to parse declaration"

field :: Parser FieldDecl
field = do
  l <- label
  -- labels might be in the form of "a: b: c: val". We need to try to match the b and c.
  others <- many (try label)
  Field (l : others) <$> aliasExpr
 where
  label :: Parser Label
  label = do
    lb <- labelExpr
    _ <- colon
    return $ Label lb

labelExpr :: Parser LabelExpr
labelExpr =
  ( do
      l <- lsquare
      e <- aliasExpr
      r <- rsquare
      return $ LabelExpr l.tkLoc e r.tkLoc
  )
    <|> labelNameConstraint

labelNameConstraint :: Parser LabelExpr
labelNameConstraint = do
  lnlem <- labelName
  optionMaybe (questionMark <|> exclamation) >>= \case
    Just x -> case x.tkType of
      QuestionMark -> return $ LabelName lnlem (Just QuestionMark)
      Exclamation -> return $ LabelName lnlem (Just Exclamation)
      _ -> unexpected $ printf "unexpected %s after label name" (show x.tkLiteral)
    Nothing -> return $ LabelName lnlem Nothing

ellipsisExpr :: Parser EllipsisExpr
ellipsisExpr = do
  el <- ellipsis
  eNodeM <- optionMaybe expr
  return $ AST.Ellipsis el.tkLoc eNodeM

embedding :: Parser Embedding
embedding = do
  -- Use try to avoid consuming expr when comprehension is not matched. For example, an identifier "fo".
  try (EmbedComprehension <$> comprehension)
    <|> (EmbeddingAlias <$> aliasExpr)
    <?> "failed to parse embedding"

aliasExpr :: Parser AliasExpr
aliasExpr =
  try
    ( do
        idM <- optionMaybe $ do
          idTk <- identifier
          _ <- accept Assign
          return idTk
        AliasExpr idM <$> expr
    )
    <|> (AliasExpr Nothing <$> expr)

comprehension :: Parser Comprehension
comprehension = do
  stNode <- startClause
  -- If start clause may have newline, or a real comma followed
  _ <- optional comma
  restClauses <- many $ do
    r <- clause
    _ <- optional comma
    return r

  Comprehension (Clauses stNode restClauses) <$> structLit

clause :: Parser Clause
clause =
  (ClauseStart <$> startClause)
    <|> (ClauseLet <$> letClause)
    <?> "failed to parse clause"

startClause :: Parser StartClause
startClause = guardClause <|> forClause <?> "failed to parse start clause"

guardClause :: Parser StartClause
guardClause = do
  st <- accept If <?> "failed to parse keyword if"
  GuardClause st.tkLoc <$> expr

forClause :: Parser StartClause
forClause = do
  st <- accept For <?> "failed to parse keyword for"
  ident <- identifier
  secIdentM <- optionMaybe $ do
    _ <- comma
    identifier
  _ <- accept In <?> "failed to parse keyword in"
  ForClause st.tkLoc ident secIdentM <$> expr

letClause :: Parser LetClause
letClause = do
  st <- accept Let <?> "failed to parse keyword let"
  ident <- identifier
  _ <- accept Assign <?> "failed to parse = in let clause"
  LetClause st.tkLoc ident <$> expr

labelName :: Parser LabelName
labelName =
  (LabelID <$> identifier)
    <|> (LabelString <$> simpleStringLit)
    <|> labelNameExpr

labelNameExpr :: Parser LabelName
labelNameExpr = do
  st <- lparen
  e <- aliasExpr
  r <- rparen
  return $ LabelNameExpr st.tkLoc e r.tkLoc

simpleStringLit :: Parser SimpleStringLit
simpleStringLit = do
  st <- accept Token.String <?> "failed to parse string literal"
  segs <- stringSegments st
  return $ SimpleStringLit st.tkLoc segs

multiLineStringLit :: Parser MultiLineStringLit
multiLineStringLit = do
  st <- accept Token.MultiLineString <?> "failed to parse multi-line string literal"
  segs <- stringSegments st
  return $ MultiLineStringLit st.tkLoc segs

stringSegments :: Token -> Parser [StringLitSeg]
stringSegments tk = case partitionUnquotedStr tk of
  Left err -> fail (BC.unpack $ tkLiteral err)
  Right partitions -> do
    mapM
      ( \x -> case x.tkType of
          Token.String -> return $ AST.UnicodeChars (T.pack $ BC.unpack $ tkLiteral x)
          Token.Interpolation -> do
            e <- case scanTokens (tkLiteral x) of
              Left err -> fail (BC.unpack $ tkLiteral err)
              Right tks -> case parseExpr tks of
                Left err -> fail err
                Right e -> return e
            return $ AST.Interpolation x.tkLoc e
          _ -> error (printf "unexpected token type in string literal: %s" (show x.tkType))
      )
      partitions

{- | Match the grammar p ","

Simialr to Go, To allow complex statements to occupy a single line, a semicolon may be omitted before a closing "}" or
")".
-}
manyEndByComma :: Parser a -> Parser b -> String -> Parser [a]
manyEndByComma p delimiter delimiterName =
  many $ do
    x <- p

    hasComma <- optionMaybe comma
    case hasComma of
      Just _ -> return ()
      Nothing -> void (lookAhead delimiter) <?> "expected comma or " ++ delimiterName

    return x

lparen :: Parser Token
lparen = accept LParen <?> "failed to parse left parenthesis"

rparen :: Parser Token
rparen = accept RParen <?> "failed to parse right parenthesis"

lsquare :: Parser Token
lsquare = accept LSquare <?> "failed to parse left square"

rsquare :: Parser Token
rsquare = accept RSquare <?> "failed to parse right square"

lbrace :: Parser Token
lbrace = accept LBrace <?> "failed to parse left brace"

rbrace :: Parser Token
rbrace = accept RBrace <?> "failed to parse right brace"

comma :: Parser Token
comma = accept Comma <?> "failed to parse comma"

questionMark :: Parser Token
questionMark = accept QuestionMark <?> "failed to parse ?"

exclamation :: Parser Token
exclamation = accept Exclamation <?> "failed to parse !"

ellipsis :: Parser Token
ellipsis = accept Token.Ellipsis <?> "failed to parse ..."

dot :: Parser Token
dot = accept Dot <?> "failed to parse ."

colon :: Parser Token
colon = accept Colon <?> "failed to parse :"

ptrace :: String -> Parser ()
ptrace s = do
  i <- getState
  parserTrace $ printf "id=%s, %s" (show i) s
  return ()

ptraced :: String -> Parser a -> Parser a
ptraced s p = do
  i <- getState
  parserTraced (printf "id=%s, %s" (show i) s) p
