{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}

module AST where

import Control.DeepSeq (NFData (..))
import Data.ByteString.Builder (
  Builder,
  byteString,
  char7,
  charUtf8,
  integerDec,
  string7,
  toLazyByteString,
 )
import Data.List (intersperse)
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
  deriving (Eq, Show, Functor, Generic, NFData)

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

data ExprNode
  = ExprUnaryExpr UnaryExpr
  | ExprBinaryOp BinaryOp Expression Expression
  deriving (Eq, Show, Generic, NFData)

type Expression = ASTN ExprNode

data UnaryExprNode
  = UnaryExprPrimaryExpr PrimaryExpr
  | UnaryExprUnaryOp UnaryOp UnaryExpr
  deriving (Eq, Show, Generic, NFData)

type UnaryExpr = ASTN UnaryExprNode

data PrimaryExprNode
  = PrimExprOperand Operand
  | PrimExprSelector PrimaryExpr Selector
  | PrimExprIndex PrimaryExpr Index
  | PrimExprArguments PrimaryExpr [Expression]
  deriving (Eq, Show, Generic, NFData)

type PrimaryExpr = ASTN PrimaryExprNode

data SelectorNode
  = IDSelector Identifier
  | StringSelector SimpleStringLit
  deriving (Eq, Show, Generic, NFData)

type Selector = ASTN SelectorNode

newtype IndexNode = Index Expression deriving (Eq, Show, Generic, NFData)

type Index = ASTN IndexNode

data OperandNode
  = OpLiteral Literal
  | OpExpression Expression
  | OperandName OperandName
  deriving (Eq, Show, Generic, NFData)

type Operand = ASTN OperandNode

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

type Literal = ASTN LiteralNode

newtype StructLitNode = StructLit [Declaration] deriving (Eq, Show, Generic, NFData)

type StructLit = ASTN StructLitNode

data DeclarationNode
  = FieldDecl FieldDecl
  | EllipsisDecl EllipsisDecl
  | Embedding Embedding
  | DeclLet LetClause
  deriving (Eq, Show, Generic, NFData)

type Declaration = ASTN DeclarationNode

data FieldDeclNode
  = Field [Label] Expression
  deriving (Eq, Show, Generic, NFData)

type FieldDecl = ASTN FieldDeclNode

newtype EllipsisDeclNode = Ellipsis (Maybe Expression) deriving (Eq, Show, Generic, NFData)

type EllipsisDecl = ASTN EllipsisDeclNode

newtype ElementListNode = EmbeddingList [Embedding] deriving (Eq, Show, Generic, NFData)

type ElementList = ASTN ElementListNode

newtype OperandNameNode = Identifier Identifier deriving (Eq, Show, Generic, NFData)

type OperandName = ASTN OperandNameNode

newtype StringLitNode = SimpleStringL SimpleStringLit deriving (Eq, Show, Generic, NFData)

type StringLit = ASTN StringLitNode

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

type RelOp = ASTN RelOpNode

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

data BinaryOpNode
  = Unify
  | Disjoin
  | Add
  | Sub
  | Mul
  | Div
  | Equ
  | BinRelOp RelOpNode
  deriving (Eq, Ord, Generic, NFData)

type BinaryOp = ASTN BinaryOpNode

instance Show BinaryOpNode where
  show Unify = "&"
  show Disjoin = "|"
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  show Equ = "=="
  show (BinRelOp op) = show op

data UnaryOpNode
  = Plus
  | Minus
  | Not
  | Star
  | UnaRelOp RelOpNode
  deriving (Eq, Ord, Generic, NFData)

type UnaryOp = ASTN UnaryOpNode

instance Show UnaryOpNode where
  show Plus = "+"
  show Minus = "-"
  show Not = "!"
  show Star = "*"
  show (UnaRelOp op) = show op

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
idCons x = ExprUnaryExpr <<^>> UnaryExprPrimaryExpr <<^>> PrimExprOperand <<^>> OperandName <<^>> Identifier <^> x

unaryOpCons :: UnaryOp -> Expression -> Maybe Expression
unaryOpCons op (ASTN{anVal = ExprUnaryExpr e}) =
  Just $ pure . ExprUnaryExpr . pure $ UnaryExprUnaryOp op e
unaryOpCons _ _ = Nothing

binaryOpCons :: BinaryOp -> Expression -> Expression -> Expression
binaryOpCons op e1 e2 = pure $ ExprBinaryOp op e1 e2

-- == Below are functions for pretty printing the AST ==

exprStr :: Expression -> String
exprStr e = show $ toLazyByteString $ exprBldIdent 0 e

exprBld :: Expression -> Builder
exprBld = exprBldIdent 0

exprBldIdent :: Int -> Expression -> Builder
exprBldIdent indent e@ASTN{anComments = cmts} = b <> commentsBld indent True cmts
 where
  b = case anVal e of
    ExprUnaryExpr ue -> unaryBld indent ue
    ExprBinaryOp op e1 e2 ->
      exprBldIdent indent e1
        <> char7 ' '
        <> binopBld op
        <> char7 ' '
        <> exprBldIdent indent e2

binopBld :: BinaryOp -> Builder
binopBld op = string7 (show (anVal op :: BinaryOpNode))

unaryBld :: Int -> UnaryExpr -> Builder
unaryBld indent e = case anVal e of
  UnaryExprPrimaryExpr pe -> primBld indent pe
  UnaryExprUnaryOp op ue -> unaryOpBld op <> unaryBld indent ue

unaryOpBld :: UnaryOp -> Builder
unaryOpBld op = string7 (show (anVal op :: UnaryOpNode))

primBld :: Int -> PrimaryExpr -> Builder
primBld indent e = case anVal e of
  PrimExprOperand op -> opndBld indent op
  PrimExprSelector pe sel -> primBld indent pe <> string7 "." <> selBld sel
  PrimExprIndex pe (ASTN{anVal = Index ie}) -> primBld indent pe <> string7 "[" <> exprBldIdent indent ie <> string7 "]"
  PrimExprArguments pe es ->
    primBld indent pe
      <> string7 "("
      <> foldr (\x acc -> exprBld x <> string7 ", " <> acc) mempty es
      <> string7 ")"

selBld :: Selector -> Builder
selBld e = case anVal e of
  IDSelector is -> byteString $ TE.encodeUtf8 (anVal is)
  StringSelector s -> simpleStrLitBld s

opndBld :: Int -> Operand -> Builder
opndBld indent op = case anVal op of
  OpLiteral lit -> litBld indent lit
  OperandName on -> opNameBld indent on
  OpExpression e -> exprBldIdent indent e

opNameBld :: Int -> OperandName -> Builder
opNameBld _ e = case anVal e of
  Identifier i -> byteString $ TE.encodeUtf8 (anVal i)

litBld :: Int -> Literal -> Builder
litBld indent e = case anVal e of
  StringLit s -> strLitBld s
  IntLit i -> integerDec i
  FloatLit f -> string7 (show f)
  BoolLit b -> if b then string7 "true" else string7 "false"
  TopLit -> string7 "_"
  BottomLit -> string7 "_|_"
  NullLit -> string7 "null"
  LitStructLit l -> structLitBld indent l
  ListLit l -> listBld l

strLitBld :: StringLit -> Builder
strLitBld (anVal -> SimpleStringL s) = char7 '"' <> simpleStrLitBld s <> char7 '"'

simpleStrLitBld :: SimpleStringLit -> Builder
simpleStrLitBld (ASTN{anVal = SimpleStringLit segs}) =
  foldr (\seg acc -> simpleStrLitSegBld seg <> acc) mempty segs

simpleStrLitSegBld :: SimpleStringLitSeg -> Builder
simpleStrLitSegBld (UnicodeVal s) = charUtf8 s
simpleStrLitSegBld (InterpolationStr (anVal -> Interpolation e)) =
  string7 "\\(" <> exprBldIdent 0 e <> char7 ')'

structLitBld :: Int -> StructLit -> Builder
structLitBld indent (ASTN{anVal = StructLit decls}) =
  if null decls
    then string7 "{}"
    else
      string7 "{\n"
        <> declsBld (indent + 1) decls
        <> indentBld indent
        <> char7 '}'

declsBld :: Int -> [Declaration] -> Builder
declsBld _ [] = string7 ""
declsBld indent (x : xs) =
  commentsBld indent True (anComments x)
    <> indentBld indent
    <> declBld indent x
    <> char7 '\n'
    <> declsBld indent xs

declBld :: Int -> Declaration -> Builder
declBld i e = case anVal e of
  FieldDecl f -> fieldDeclBld i f
  EllipsisDecl (ASTN{anVal = Ellipsis _}) -> string7 "..."
  Embedding eb -> embeddingBld i eb
  DeclLet (ASTN{anVal = LetClause ident binde}) ->
    string7 "let" <> byteString (TE.encodeUtf8 $ anVal ident) <> string7 " = " <> exprBldIdent 0 binde

fieldDeclBld :: Int -> FieldDecl -> Builder
fieldDeclBld indent e = case anVal e of
  Field ls fe ->
    foldr (\l acc -> labelBld l <> string7 ": " <> acc) mempty ls
      <> exprBldIdent indent fe

embeddingBld :: Int -> Embedding -> Builder
embeddingBld indent e = case anVal e of
  EmbedComprehension _ -> string7 "<undefined>"
  AliasExpr ex -> exprBldIdent indent ex

listBld :: ElementList -> Builder
listBld (ASTN{anVal = EmbeddingList l}) = string7 "[" <> goList l
 where
  goList :: [Embedding] -> Builder
  goList [] = string7 "]"
  goList [x] = embeddingBld 0 x <> string7 "]"
  goList (x : xs) = embeddingBld 0 x <> string7 ", " <> goList xs

labelBld :: Label -> Builder
labelBld (ASTN{anVal = Label e}) = labelExprBld e

labelExprBld :: LabelExpr -> Builder
labelExprBld e = case anVal e of
  LabelName ln cnstr -> case cnstr of
    RegularLabel -> labelNameBld ln
    OptionalLabel -> labelNameBld ln <> string7 "?"
    RequiredLabel -> labelNameBld ln <> string7 "!"
  -- The LabelPattern should not be exported.
  LabelPattern le -> string7 "[" <> exprBldIdent 0 le <> string7 "]"

labelNameBld :: LabelName -> Builder
labelNameBld e = case anVal e of
  LabelID i -> byteString $ TE.encodeUtf8 (anVal i)
  LabelString s -> simpleStrLitBld s
  LabelNameExpr ex -> char7 '(' <> exprBldIdent 0 ex <> char7 ')'

indentBld :: Int -> Builder
indentBld indent = string7 (replicate (indent * tabSize) ' ')

tabSize :: Int
tabSize = 4

commentBld :: T.Text -> Builder
commentBld c = string7 "// " <> string7 (T.unpack c)

{- | Build comments for an AST node.

If `forceNLBefore` is `True`, it will always make comments start on a new line before the node.
-}
commentsBld :: Int -> Bool -> [T.Text] -> Builder
commentsBld _ _ [] = mempty
commentsBld indent forceNLBefore cs
  | not forceNLBefore && length cs < 2 = char7 ' ' <> commentBld (head cs)
  | otherwise = mconcat (map (\c -> indentBld indent <> commentBld c <> char7 '\n') cs)
