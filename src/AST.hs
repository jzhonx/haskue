{-# LANGUAGE DeriveFunctor #-}

module AST where

import Data.ByteString.Builder (
  Builder,
  char7,
  integerDec,
  string7,
  toLazyByteString,
 )
import Prelude hiding (GT, LT)

-- | Source position with line and column information
data SourcePos = SourcePos
  { posLine :: Int
  , posColumn :: Int
  }
  deriving (Eq, Show)

-- | Position range with start and end positions, and optional file path
data Position = Position
  { posStart :: SourcePos
  , posEnd :: SourcePos
  , posFile :: Maybe FilePath
  }
  deriving (Eq, Show)

-- | Create a default position with no information
noPosition :: Position
noPosition = Position (SourcePos 0 0) (SourcePos 0 0) Nothing

-- | Annotate an AST node with position information
data WithPos a = WithPos
  { wpPos :: Maybe Position
  , wpVal :: a
  }
  deriving (Eq, Show, Functor)

instance (Ord a) => Ord (WithPos a) where
  WithPos _ v1 `compare` WithPos _ v2 = v1 `compare` v2

instance Applicative WithPos where
  pure = WithPos Nothing
  WithPos _ f <*> WithPos pos x = WithPos pos (f x)

withPos :: Position -> a -> WithPos a
withPos pos = WithPos (Just pos)

(<^>) :: (WithPos a -> b) -> WithPos a -> WithPos b
(<^>) f a@(WithPos pos _) = WithPos pos (f a)

(<<^>>) :: (WithPos b -> c) -> (WithPos a -> b) -> WithPos a -> c
(<<^>>) f g a = wpVal $ f <^> (g <^> a)

newtype SourceFile = SourceFile
  { sfDecls :: [Declaration]
  }
  deriving (Eq, Show)

data ExprNode
  = ExprUnaryExpr UnaryExpr
  | ExprBinaryOp BinaryOp Expression Expression
  deriving (Eq, Show)

type Expression = WithPos ExprNode

data UnaryExprNode
  = UnaryExprPrimaryExpr PrimaryExpr
  | UnaryExprUnaryOp UnaryOp UnaryExpr
  deriving (Eq, Show)

type UnaryExpr = WithPos UnaryExprNode

data PrimaryExprNode
  = PrimExprOperand Operand
  | PrimExprSelector PrimaryExpr Selector
  | PrimExprIndex PrimaryExpr Index
  | PrimExprArguments PrimaryExpr [Expression]
  deriving (Eq, Show)

type PrimaryExpr = WithPos PrimaryExprNode

data SelectorNode
  = IDSelector Identifier
  | StringSelector SimpleStringLit
  deriving (Eq, Show)

type Selector = WithPos SelectorNode

newtype IndexNode = Index Expression deriving (Eq, Show)

type Index = WithPos IndexNode

data OperandNode
  = OpLiteral Literal
  | OpExpression Expression
  | OperandName OperandName
  deriving (Eq, Show)

type Operand = WithPos OperandNode

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
  deriving (Eq, Show)

type Literal = WithPos LiteralNode

newtype StructLitNode = StructLit [Declaration] deriving (Eq, Show)

type StructLit = WithPos StructLitNode

data DeclarationNode
  = FieldDecl FieldDecl
  | EllipsisDecl EllipsisDecl
  | Embedding Embedding
  | DeclLet LetClause
  deriving (Eq, Show)

type Declaration = WithPos DeclarationNode

data FieldDeclNode
  = Field [Label] Expression
  deriving (Eq, Show)

type FieldDecl = WithPos FieldDeclNode

newtype EllipsisDeclNode = Ellipsis (Maybe Expression) deriving (Eq, Show)

type EllipsisDecl = WithPos EllipsisDeclNode

newtype ElementListNode = EmbeddingList [Embedding] deriving (Eq, Show)

type ElementList = WithPos ElementListNode

newtype OperandNameNode = Identifier Identifier deriving (Eq, Show)

type OperandName = WithPos OperandNameNode

newtype StringLit = SimpleStringLit SimpleStringLit deriving (Eq, Show)

type SimpleStringLit = String

newtype LabelNode = Label LabelExpr deriving (Eq, Show)

type Label = WithPos LabelNode

data LabelExprNode
  = LabelName LabelName LabelConstraint
  | LabelPattern Expression
  deriving (Eq, Show)

type LabelExpr = WithPos LabelExprNode

data LabelConstraint
  = RegularLabel
  | OptionalLabel
  | RequiredLabel
  deriving (Eq, Show)

data LabelNameNode
  = LabelID Identifier
  | LabelString String
  | LabelNameExpr Expression
  deriving (Eq, Show)

type LabelName = WithPos LabelNameNode

type IdentifierNode = String

type Identifier = WithPos IdentifierNode

data RelOpNode
  = NE
  | LT
  | LE
  | GT
  | GE
  | ReMatch
  | ReNotMatch
  deriving (Eq, Ord)

instance Show RelOpNode where
  show NE = "!="
  show LT = "<"
  show LE = "<="
  show GT = ">"
  show GE = ">="
  show ReMatch = "=~"
  show ReNotMatch = "!~"

type RelOp = WithPos RelOpNode

data EmbeddingNode = EmbedComprehension Comprehension | AliasExpr Expression
  deriving (Eq, Show)

type Embedding = WithPos EmbeddingNode

data ComprehensionNode = Comprehension Clauses StructLit
  deriving (Eq, Show)

type Comprehension = WithPos ComprehensionNode

data ClausesNode = Clauses StartClause [Clause] deriving (Eq, Show)

type Clauses = WithPos ClausesNode

data StartClauseNode
  = -- | GuardClause is an "if" expression
    GuardClause Expression
  | -- | ForClause is a "for" expression
    ForClause Identifier (Maybe Identifier) Expression
  deriving (Eq, Show)

type StartClause = WithPos StartClauseNode

data ClauseNode
  = ClauseStartClause StartClause
  | ClauseLetClause LetClause
  deriving (Eq, Show)

type Clause = WithPos ClauseNode

data LetClauseNode = LetClause Identifier Expression
  deriving (Eq, Show)

type LetClause = WithPos LetClauseNode

data BinaryOpNode
  = Unify
  | Disjoin
  | Add
  | Sub
  | Mul
  | Div
  | Equ
  | BinRelOp RelOpNode
  deriving (Eq, Ord)

type BinaryOp = WithPos BinaryOpNode

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
  deriving (Eq, Ord)

type UnaryOp = WithPos UnaryOpNode

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
unaryOpCons op (WithPos{wpVal = ExprUnaryExpr e}) =
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
exprBldIdent ident e =
  case wpVal e of
    ExprUnaryExpr ue -> unaryBld ident ue
    ExprBinaryOp op e1 e2 ->
      exprBldIdent ident e1
        <> char7 ' '
        <> binopBld op
        <> char7 ' '
        <> exprBldIdent ident e2

binopBld :: BinaryOp -> Builder
binopBld op = string7 (show (wpVal op :: BinaryOpNode))

unaryBld :: Int -> UnaryExpr -> Builder
unaryBld ident e = case wpVal e of
  UnaryExprPrimaryExpr pe -> primBld ident pe
  UnaryExprUnaryOp op ue -> unaryOpBld op <> unaryBld ident ue

unaryOpBld :: UnaryOp -> Builder
unaryOpBld op = string7 (show (wpVal op :: UnaryOpNode))

primBld :: Int -> PrimaryExpr -> Builder
primBld ident e = case wpVal e of
  PrimExprOperand op -> opndBld ident op
  PrimExprSelector pe sel -> primBld ident pe <> string7 "." <> selBld sel
  PrimExprIndex pe (WithPos{wpVal = Index ie}) -> primBld ident pe <> string7 "[" <> exprBldIdent ident ie <> string7 "]"
  PrimExprArguments pe es ->
    primBld ident pe
      <> string7 "("
      <> foldr (\x acc -> exprBld x <> string7 ", " <> acc) mempty es
      <> string7 ")"

selBld :: Selector -> Builder
selBld e = case wpVal e of
  IDSelector is -> string7 (wpVal is)
  StringSelector s -> string7 s

opndBld :: Int -> Operand -> Builder
opndBld ident op = case wpVal op of
  OpLiteral lit -> litBld ident lit
  OperandName on -> opNameBld ident on
  OpExpression e -> exprBldIdent ident e

opNameBld :: Int -> OperandName -> Builder
opNameBld _ e = case wpVal e of
  Identifier i -> string7 (wpVal i)

litBld :: Int -> Literal -> Builder
litBld ident e = case wpVal e of
  StringLit s -> strLitBld s
  IntLit i -> integerDec i
  FloatLit f -> string7 (show f)
  BoolLit b -> if b then string7 "true" else string7 "false"
  TopLit -> string7 "_"
  BottomLit -> string7 "_|_"
  NullLit -> string7 "null"
  LitStructLit l -> structLitBld ident l
  ListLit l -> listBld l

strLitBld :: StringLit -> Builder
strLitBld (SimpleStringLit s) = char7 '"' <> string7 s <> char7 '"'

structLitBld :: Int -> StructLit -> Builder
structLitBld ident (WithPos{wpVal = StructLit decls}) =
  if null decls
    then string7 "{}"
    else
      string7 "{\n"
        <> declsBld (ident + 1) decls
        <> string7 (replicate (ident * tabSize) ' ')
        <> char7 '}'

tabSize :: Int
tabSize = 4

declsBld :: Int -> [Declaration] -> Builder
declsBld _ [] = string7 ""
declsBld ident (x : xs) =
  string7 (replicate (ident * tabSize) ' ')
    <> declBld ident x
    <> char7 '\n'
    <> declsBld ident xs

declBld :: Int -> Declaration -> Builder
declBld i e = case wpVal e of
  FieldDecl f -> fieldDeclBld i f
  EllipsisDecl (WithPos{wpVal = Ellipsis _}) -> string7 "..."
  Embedding eb -> embeddingBld i eb
  DeclLet (WithPos{wpVal = LetClause ident binde}) ->
    string7 "let" <> string7 (wpVal ident) <> string7 " = " <> exprBldIdent 0 binde

fieldDeclBld :: Int -> FieldDecl -> Builder
fieldDeclBld ident e = case wpVal e of
  Field ls fe ->
    foldr (\l acc -> labelBld l <> string7 ": " <> acc) mempty ls
      <> exprBldIdent ident fe

embeddingBld :: Int -> Embedding -> Builder
embeddingBld ident e = case wpVal e of
  EmbedComprehension _ -> string7 "<undefined>"
  AliasExpr ex -> exprBldIdent ident ex

listBld :: ElementList -> Builder
listBld (WithPos{wpVal = EmbeddingList l}) = string7 "[" <> goList l
 where
  goList :: [Embedding] -> Builder
  goList [] = string7 "]"
  goList [x] = embeddingBld 0 x <> string7 "]"
  goList (x : xs) = embeddingBld 0 x <> string7 ", " <> goList xs

labelBld :: Label -> Builder
labelBld (WithPos{wpVal = Label e}) = labelExprBld e

labelExprBld :: LabelExpr -> Builder
labelExprBld e = case wpVal e of
  LabelName ln cnstr -> case cnstr of
    RegularLabel -> labelNameBld ln
    OptionalLabel -> labelNameBld ln <> string7 "?"
    RequiredLabel -> labelNameBld ln <> string7 "!"
  -- The LabelPattern should not be exported.
  LabelPattern le -> string7 "[" <> exprBldIdent 0 le <> string7 "]"

labelNameBld :: LabelName -> Builder
labelNameBld e = case wpVal e of
  LabelID i -> string7 (wpVal i)
  LabelString s -> string7 s
  LabelNameExpr ex -> char7 '(' <> exprBldIdent 0 ex <> char7 ')'
