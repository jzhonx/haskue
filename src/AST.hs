{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module AST where

import Control.DeepSeq (NFData (..))
import Control.Monad (foldM)
import Control.Monad.State (MonadState, evalState, gets, modify')
import Data.ByteString.Builder (
  Builder,
  byteString,
  char7,
  charUtf8,
  integerDec,
  string7,
  toLazyByteString,
 )
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import GHC.Generics (Generic)
import Prelude hiding (GT, LT)

-- | Source position with line and column information
data SourcePos = SourcePos
  { posLine :: Int
  , posColumn :: Int
  }
  deriving (Eq, Show, Generic, NFData)

-- | Position range with start and end positions, and optional file path
data Position = Position
  { posStart :: SourcePos
  , posEnd :: SourcePos
  , posFile :: Maybe FilePath
  }
  deriving (Eq, Show, Generic, NFData)

-- | Create a default position with no information
noPosition :: Position
noPosition = Position (SourcePos 0 0) (SourcePos 0 0) Nothing

-- | Annotate an AST node with position information
data ASTN a = ASTN
  { anPos :: Maybe Position
  , anComments :: [T.Text]
  -- ^ Comments associated with the AST node
  , anVal :: a
  }
  deriving (Eq, Functor, Generic, NFData)

instance (Show a) => Show (ASTN a) where
  show (ASTN _ _ val) = show val

instance (Ord a) => Ord (ASTN a) where
  ASTN _ _ v1 `compare` ASTN _ _ v2 = v1 `compare` v2

instance Applicative ASTN where
  pure = ASTN Nothing []
  ASTN _ _ f <*> ASTN pos c x = ASTN pos c (f x)

withPos :: Position -> a -> ASTN a
withPos pos = ASTN (Just pos) []

(<^>) :: (ASTN a -> b) -> ASTN a -> ASTN b
(<^>) f a@(ASTN pos c _) = ASTN pos c (f a)

(<<^>>) :: (ASTN b -> c) -> (ASTN a -> b) -> ASTN a -> c
(<<^>>) f g a = anVal $ f <^> (g <^> a)

newtype SourceFile = SourceFile
  { sfDecls :: [Declaration]
  }
  deriving (Eq, Show)

type Expression = ASTN ExprNode

data ExprNode
  = ExprUnaryExpr UnaryExpr
  | ExprBinaryOp BinaryOp Expression Expression
  deriving (Eq, Show, Generic, NFData)

type UnaryExpr = ASTN UnaryExprNode

data UnaryExprNode
  = UnaryExprPrimaryExpr PrimaryExpr
  | UnaryExprUnaryOp UnaryOp UnaryExpr
  deriving (Eq, Show, Generic, NFData)

type PrimaryExpr = ASTN PrimaryExprNode

data PrimaryExprNode
  = PrimExprOperand Operand
  | PrimExprSelector PrimaryExpr Selector
  | PrimExprIndex PrimaryExpr Index
  | PrimExprArguments PrimaryExpr [Expression]
  deriving (Eq, Show, Generic, NFData)

type Selector = ASTN SelectorNode

data SelectorNode
  = IDSelector Identifier
  | StringSelector SimpleStringLit
  deriving (Eq, Show, Generic, NFData)

type Index = ASTN IndexNode

newtype IndexNode = Index Expression deriving (Eq, Show, Generic, NFData)

type Operand = ASTN OperandNode

data OperandNode
  = OpLiteral Literal
  | OpExpression Expression
  | OperandName OperandName
  deriving (Eq, Show, Generic, NFData)

type Literal = ASTN LiteralNode

data LiteralNode
  = StringLit StringLit
  | IntLit Integer
  | FloatLit Double
  | BoolLit Bool
  | TopLit
  | BottomLit
  | NullLit
  | LitStructLit StructLit
  | ListLit ElementList
  deriving (Eq, Show, Generic, NFData)

type StructLit = ASTN StructLitNode

newtype StructLitNode = StructLit [Declaration] deriving (Eq, Show, Generic, NFData)

type Declaration = ASTN DeclarationNode

data DeclarationNode
  = FieldDecl FieldDecl
  | EllipsisDecl EllipsisDecl
  | Embedding Embedding
  | DeclLet LetClause
  deriving (Eq, Show, Generic, NFData)

type FieldDecl = ASTN FieldDeclNode

data FieldDeclNode
  = Field [Label] Expression
  deriving (Eq, Show, Generic, NFData)

type EllipsisDecl = ASTN EllipsisDeclNode

newtype EllipsisDeclNode = Ellipsis (Maybe Expression) deriving (Eq, Show, Generic, NFData)

type ElementList = ASTN ElementListNode

newtype ElementListNode = EmbeddingList [Embedding] deriving (Eq, Show, Generic, NFData)

type OperandName = ASTN OperandNameNode

newtype OperandNameNode = Identifier Identifier deriving (Eq, Show, Generic, NFData)

type StringLit = ASTN StringLitNode

newtype StringLitNode = SimpleStringL SimpleStringLit deriving (Eq, Show, Generic, NFData)

type SimpleStringLit = ASTN SimpleStringLitNode

newtype SimpleStringLitNode = SimpleStringLit [SimpleStringLitSeg]
  deriving (Eq, Show, Generic, NFData)

data SimpleStringLitSeg
  = UnicodeVal Char
  | InterpolationStr Interpolation
  deriving (Eq, Show, Generic, NFData)

newtype InterpolationNode = Interpolation Expression deriving (Eq, Show, Generic, NFData)

type Interpolation = ASTN InterpolationNode

newtype LabelNode = Label LabelExpr deriving (Eq, Show, Generic, NFData)

type Label = ASTN LabelNode

data LabelExprNode
  = LabelName LabelName LabelConstraint
  | LabelPattern Expression
  deriving (Eq, Show, Generic, NFData)

type LabelExpr = ASTN LabelExprNode

data LabelConstraint
  = RegularLabel
  | OptionalLabel
  | RequiredLabel
  deriving (Eq, Show, Generic, NFData)

data LabelNameNode
  = LabelID Identifier
  | LabelString SimpleStringLit
  | LabelNameExpr Expression
  deriving (Eq, Show, Generic, NFData)

type LabelName = ASTN LabelNameNode

type IdentifierNode = T.Text

type Identifier = ASTN IdentifierNode

data EmbeddingNode = EmbedComprehension Comprehension | AliasExpr Expression
  deriving (Eq, Show, Generic, NFData)

type Embedding = ASTN EmbeddingNode

data ComprehensionNode = Comprehension Clauses StructLit
  deriving (Eq, Show, Generic, NFData)

type Comprehension = ASTN ComprehensionNode

data ClausesNode = Clauses StartClause [Clause] deriving (Eq, Show, Generic, NFData)

type Clauses = ASTN ClausesNode

data StartClauseNode
  = -- | GuardClause is an "if" expression
    GuardClause Expression
  | -- | ForClause is a "for" expression
    ForClause Identifier (Maybe Identifier) Expression
  deriving (Eq, Show, Generic, NFData)

type StartClause = ASTN StartClauseNode

data ClauseNode
  = ClauseStartClause StartClause
  | ClauseLetClause LetClause
  deriving (Eq, Show, Generic, NFData)

type Clause = ASTN ClauseNode

data LetClauseNode = LetClause Identifier Expression
  deriving (Eq, Show, Generic, NFData)

type LetClause = ASTN LetClauseNode

type BinaryOp = ASTN BinaryOpNode

data BinaryOpNode
  = Unify
  | Disjoin
  | Add
  | Sub
  | Mul
  | Div
  | Equ
  | BinRelOp RelOpNode
  | -- | Disjunction operation is used in debugging and should not appear in the final AST.
    DisjoinDebugOp
  deriving (Eq, Ord, Generic, NFData)

instance Show BinaryOpNode where
  show Unify = "&"
  show Disjoin = "|"
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  show Equ = "=="
  show (BinRelOp op) = show op
  show DisjoinDebugOp = "|_o"

getBinaryOpNodePrec :: BinaryOpNode -> Int
getBinaryOpNodePrec Unify = 2
getBinaryOpNodePrec Disjoin = 1
getBinaryOpNodePrec Add = 6
getBinaryOpNodePrec Sub = 6
getBinaryOpNodePrec Mul = 7
getBinaryOpNodePrec Div = 7
getBinaryOpNodePrec Equ = 4
getBinaryOpNodePrec (BinRelOp _) = 4
getBinaryOpNodePrec DisjoinDebugOp = 1

type UnaryOp = ASTN UnaryOpNode

data UnaryOpNode
  = Plus
  | Minus
  | Not
  | Star
  | UnaRelOp RelOpNode
  deriving (Eq, Ord, Generic, NFData)

instance Show UnaryOpNode where
  show Plus = "+"
  show Minus = "-"
  show Not = "!"
  show Star = "*"
  show (UnaRelOp op) = show op

data RelOpNode
  = NE
  | LT
  | LE
  | GT
  | GE
  | ReMatch
  | ReNotMatch
  deriving (Eq, Ord, Generic, NFData)

instance Show RelOpNode where
  show NE = "!="
  show LT = "<"
  show LE = "<="
  show GT = ">"
  show GE = ">="
  show ReMatch = "=~"
  show ReNotMatch = "!~"

data Operator = OpBinary BinaryOpNode | OpUnary UnaryOpNode

data Quote = SingleQuote | DoubleQuote deriving (Eq)

instance Show Quote where
  show SingleQuote = "'"
  show DoubleQuote = "\""

strToLit :: T.Text -> Literal
strToLit s = StringLit <<^>> SimpleStringL <^> strToSimpleStrLit s

strToSimpleStrLit :: T.Text -> SimpleStringLit
strToSimpleStrLit s = pure (SimpleStringLit (map UnicodeVal (T.unpack s)))

litCons :: Literal -> Expression
litCons x =
  ExprUnaryExpr
    <<^>> UnaryExprPrimaryExpr
    <<^>> PrimExprOperand
    <<^>> OpLiteral
    <^> x

idCons :: Identifier -> Expression
idCons x = ExprUnaryExpr <<^>> UnaryExprPrimaryExpr <^> idToPrimExpr x

idToPrimExpr :: Identifier -> PrimaryExpr
idToPrimExpr x = PrimExprOperand <<^>> OperandName <<^>> Identifier <^> x

unaryOpCons :: UnaryOp -> Expression -> Maybe Expression
unaryOpCons op (ASTN{anVal = ExprUnaryExpr e}) =
  Just $ pure . ExprUnaryExpr . pure $ UnaryExprUnaryOp op e
unaryOpCons _ _ = Nothing

binaryOpCons :: BinaryOp -> Expression -> Expression -> Expression
binaryOpCons op e1 e2 = pure $ ExprBinaryOp op e1 e2

-- == Below are functions for pretty printing the AST ==

exprToStr :: Expression -> String
exprToStr e = show $ toLazyByteString $ exprToBuilder False e

exprToOneLinerStr :: Expression -> String
exprToOneLinerStr e = show $ toLazyByteString $ exprToBuilder True e

exprToBuilder :: Bool -> Expression -> Builder
exprToBuilder oneLiner e = evalState (exprBld e) (ASTBuilderState 0 oneLiner)

exprToOneLinerBuilder :: Expression -> Builder
exprToOneLinerBuilder = exprToBuilder True

declsToBuilder :: [Declaration] -> Builder
declsToBuilder decls = evalState (declsBld decls) (ASTBuilderState 0 False)

data ASTBuilderState = ASTBuilderState
  { absIndent :: Int
  , absOneLiner :: Bool
  }
  deriving (Eq, Show)

type M = MonadState ASTBuilderState

getIndent :: (M m) => m Int
getIndent = gets absIndent

getOneLiner :: (M m) => m Bool
getOneLiner = gets absOneLiner

withIncIndent :: (M m) => m a -> m a
withIncIndent action = do
  indent <- getIndent
  modify' (\s -> s{absIndent = indent + 1})
  r <- action
  modify' (\s -> s{absIndent = indent})
  return r

exprBld :: (M m) => Expression -> m Builder
exprBld e@ASTN{anComments = cmts} = do
  cmt <- commentsBld True cmts
  b <- buildForE
  return $ b <> cmt
 where
  buildForE = case anVal e of
    ExprUnaryExpr ue -> unaryBld ue
    ExprBinaryOp op e1 e2 -> do
      b1 <- wrapParensIfNeeded e1 op
      b2 <- wrapParensIfNeeded e2 op
      return $
        b1 <> char7 ' ' <> binopBld op <> char7 ' ' <> b2

  wrapParensIfNeeded operand@(anVal -> (ExprBinaryOp op1 _ _)) op = do
    operandB <- exprBld operand
    return $
      if getBinaryOpNodePrec (anVal op1) < getBinaryOpNodePrec (anVal op)
        then char7 '(' <> operandB <> char7 ')'
        else operandB
  wrapParensIfNeeded operand _ = exprBld operand

binopBld :: BinaryOp -> Builder
binopBld op = string7 (show (anVal op :: BinaryOpNode))

unaryBld :: (M m) => UnaryExpr -> m Builder
unaryBld e = case anVal e of
  UnaryExprPrimaryExpr pe -> primBld pe
  UnaryExprUnaryOp op ue -> do
    b <- unaryBld ue
    return $ unaryOpBld op <> b

unaryOpBld :: UnaryOp -> Builder
unaryOpBld op = string7 (show (anVal op :: UnaryOpNode))

primBld :: (M m) => PrimaryExpr -> m Builder
primBld e = case anVal e of
  PrimExprOperand op -> opndBld op
  PrimExprSelector pe sel -> do
    b <- primBld pe
    b2 <- selBld sel
    return $ b <> string7 "." <> b2
  PrimExprIndex pe (ASTN{anVal = Index ie}) -> do
    b1 <- primBld pe
    b2 <- exprBld ie
    return $ b1 <> string7 "[" <> b2 <> string7 "]"
  PrimExprArguments pe es -> do
    b <- primBld pe
    (argsB, _) <-
      foldM
        ( \(acc, started) x -> do
            xb <- exprBld x
            return (if not started then xb else acc <> string7 ", " <> xb, True)
        )
        (mempty, False)
        es
    return $ b <> string7 "(" <> argsB <> string7 ")"

selBld :: (M m) => Selector -> m Builder
selBld e = case anVal e of
  IDSelector is -> return $ byteString $ TE.encodeUtf8 (anVal is)
  StringSelector s -> simpleStrLitBld s

opndBld :: (M m) => Operand -> m Builder
opndBld op = case anVal op of
  OpLiteral lit -> litBld lit
  OperandName on -> return $ opNameBld on
  OpExpression e -> exprBld e

opNameBld :: OperandName -> Builder
opNameBld e = case anVal e of
  Identifier i -> byteString $ TE.encodeUtf8 (anVal i)

litBld :: (M m) => Literal -> m Builder
litBld e = case anVal e of
  StringLit s -> strLitBld s
  IntLit i -> return $ integerDec i
  FloatLit f -> return $ string7 (show f)
  BoolLit b -> return $ if b then string7 "true" else string7 "false"
  TopLit -> return $ string7 "_"
  BottomLit -> return $ string7 "_|_"
  NullLit -> return $ string7 "null"
  LitStructLit l -> structLitBld l
  ListLit l -> listBld l

strLitBld :: (M m) => StringLit -> m Builder
strLitBld (anVal -> SimpleStringL s) = do
  b <- simpleStrLitBld s
  return $ char7 '"' <> b <> char7 '"'

-- | TODO: efficiency
simpleStrLitBld :: (M m) => SimpleStringLit -> m Builder
simpleStrLitBld (ASTN{anVal = SimpleStringLit segs}) =
  foldM
    ( \acc seg -> do
        b <- simpleStrLitSegBld seg
        return $ acc <> b
    )
    mempty
    segs

simpleStrLitSegBld :: (M m) => SimpleStringLitSeg -> m Builder
simpleStrLitSegBld (UnicodeVal s) = return $ charUtf8 s
simpleStrLitSegBld (InterpolationStr (anVal -> Interpolation e)) = do
  b <- exprBld e
  return $ string7 "\\(" <> b <> char7 ')'

structLitBld :: (M m) => StructLit -> m Builder
structLitBld (ASTN{anVal = StructLit decls})
  | null decls = return $ string7 "{}"
  | otherwise = do
      indent <- getIndent
      oneLiner <- getOneLiner
      if oneLiner
        then do
          -- When one-liner is set, we do not add new lines or indentation.
          declsB <- declsBld decls
          return $ string7 "{" <> declsB <> string7 "}"
        else do
          declsB <- withIncIndent $ declsBld decls
          return $ string7 "{\n" <> declsB <> indentBld indent <> char7 '}'

declsBld :: (M m) => [Declaration] -> m Builder
declsBld [] = return $ string7 ""
declsBld (x : xs) = do
  b <- declBld x
  rest <- declsBld xs
  oneLiner <- getOneLiner
  if oneLiner
    then
      -- When one-liner is set, we do not add new lines or indentation.
      return $ b <> (if null xs then mempty else string7 ",") <> rest
    else do
      cmt <- commentsBld True (anComments x)
      indent <- getIndent
      return $
        cmt <> indentBld indent <> b <> char7 '\n' <> rest

declBld :: (M m) => Declaration -> m Builder
declBld e = case anVal e of
  FieldDecl f -> fieldDeclBld f
  EllipsisDecl (ASTN{anVal = Ellipsis _}) -> return $ string7 "..."
  Embedding eb -> embeddingBld eb
  DeclLet (ASTN{anVal = LetClause ident binde}) -> do
    b <- exprBld binde
    return $ string7 "let " <> byteString (TE.encodeUtf8 $ anVal ident) <> string7 " = " <> b

fieldDeclBld :: (M m) => FieldDecl -> m Builder
fieldDeclBld e = case anVal e of
  Field ls fe -> do
    declB <- exprBld fe
    labels <-
      foldM
        ( \acc l -> do
            lb <- labelBld l
            return $ acc <> lb <> string7 ": "
        )
        mempty
        ls
    return $ labels <> declB

embeddingBld :: (M m) => Embedding -> m Builder
embeddingBld e = case anVal e of
  EmbedComprehension _ -> return $ string7 "<undefined>"
  AliasExpr ex -> exprBld ex

listBld :: (M m) => ElementList -> m Builder
listBld (ASTN{anVal = EmbeddingList l}) = do
  b <- goList l
  return $ string7 "[" <> b
 where
  goList [] = return $ string7 "]"
  goList [x] = do
    b <- embeddingBld x
    return $ b <> string7 "]"
  goList (x : xs) = do
    b <- embeddingBld x
    rest <- goList xs
    return $ b <> string7 ", " <> rest

labelBld :: (M m) => Label -> m Builder
labelBld (ASTN{anVal = Label e}) = labelExprBld e

labelExprBld :: (M m) => LabelExpr -> m Builder
labelExprBld e = case anVal e of
  LabelName ln cnstr -> case cnstr of
    RegularLabel -> labelNameBld ln
    OptionalLabel -> do
      b <- labelNameBld ln
      return $ b <> string7 "?"
    RequiredLabel -> do
      b <- labelNameBld ln
      return $ b <> string7 "!"
  -- The LabelPattern should not be exported.
  LabelPattern le -> do
    b <- exprBld le
    return $ string7 "[" <> b <> string7 "]"

labelNameBld :: (M m) => LabelName -> m Builder
labelNameBld e = case anVal e of
  LabelID i -> return $ byteString $ TE.encodeUtf8 (anVal i)
  LabelString s -> simpleStrLitBld s
  LabelNameExpr ex -> do
    b <- exprBld ex
    return $ char7 '(' <> b <> char7 ')'

indentBld :: Int -> Builder
indentBld indent = string7 (replicate (indent * tabSize) ' ')

tabSize :: Int
tabSize = 4

commentBld :: T.Text -> Builder
commentBld c = string7 "// " <> string7 (T.unpack c)

{- | Build comments for an AST node.

If `forceNLBefore` is `True`, it will always make comments start on a new line before the node.
-}
commentsBld :: (M m) => Bool -> [T.Text] -> m Builder
commentsBld _ [] = return mempty
commentsBld forceNLBefore cs
  | not forceNLBefore && length cs < 2 = return $ char7 ' ' <> commentBld (head cs)
  | otherwise = do
      indent <- getIndent
      return $ mconcat (map (\c -> indentBld indent <> commentBld c <> char7 '\n') cs)
