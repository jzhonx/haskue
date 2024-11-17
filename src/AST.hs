module AST (
  BinaryOp (..),
  Declaration (..),
  ElementList (..),
  EllipsisDecl (..),
  Embedding,
  Expression (..),
  FieldDecl (..),
  Identifer,
  Index (..),
  Label (..),
  LabelConstraint (..),
  LabelExpr (..),
  LabelName (..),
  Literal (..),
  Operand (..),
  OperandName (..),
  PrimaryExpr (..),
  Quote (..),
  RelOp (..),
  Selector (..),
  SimpleStringLit,
  SourceFile (..),
  StringLit (..),
  UnaryExpr (..),
  UnaryOp (..),
  binaryOpCons,
  exprBld,
  exprBldIdent,
  exprStr,
  idCons,
  litCons,
  unaryOpCons,
  declsBld,
)
where

import Data.ByteString.Builder (
  Builder,
  char7,
  integerDec,
  string7,
  toLazyByteString,
 )
import Prelude hiding (GT, LT)

newtype SourceFile = SourceFile
  { sfDecls :: [Declaration]
  }
  deriving (Eq, Show)

data Expression
  = ExprUnaryExpr UnaryExpr
  | ExprBinaryOp BinaryOp Expression Expression
  deriving (Eq, Show)

data UnaryExpr
  = UnaryExprPrimaryExpr PrimaryExpr
  | UnaryExprUnaryOp UnaryOp UnaryExpr
  deriving (Eq, Show)

data PrimaryExpr
  = PrimExprOperand Operand
  | PrimExprSelector PrimaryExpr Selector
  | PrimExprIndex PrimaryExpr Index
  | PrimExprArguments PrimaryExpr [Expression]
  deriving (Eq, Show)

data Selector
  = IDSelector Identifer
  | StringSelector SimpleStringLit
  deriving (Eq, Show)

newtype Index = Index Expression deriving (Eq, Show)

data Operand
  = OpLiteral Literal
  | OpExpression Expression
  | OperandName OperandName
  deriving (Eq, Show)

data Literal
  = StringLit StringLit
  | IntLit Integer
  | FloatLit Double
  | BoolLit Bool
  | TopLit
  | BottomLit
  | NullLit
  | StructLit [Declaration]
  | ListLit ElementList
  deriving (Eq, Show)

type Embedding = Expression

data Declaration
  = FieldDecl FieldDecl
  | EllipsisDecl EllipsisDecl
  | Embedding Embedding
  deriving (Eq, Show)

data FieldDecl
  = Field [Label] Expression
  deriving (Eq, Show)

newtype EllipsisDecl = Ellipsis (Maybe Expression) deriving (Eq, Show)

newtype ElementList = EmbeddingList [Embedding] deriving (Eq, Show)

newtype OperandName = Identifier Identifer deriving (Eq, Show)

newtype StringLit = SimpleStringLit SimpleStringLit deriving (Eq, Show)

type SimpleStringLit = String

newtype Label = Label LabelExpr deriving (Eq, Show)

data LabelExpr
  = LabelName LabelName LabelConstraint
  | LabelPattern Expression
  deriving (Eq, Show)

data LabelConstraint
  = RegularLabel
  | OptionalLabel
  | RequiredLabel
  deriving (Eq, Show)

data LabelName
  = LabelID Identifer
  | LabelString String
  | LabelNameExpr Expression
  deriving (Eq, Show)

type Identifer = String

data RelOp
  = NE
  | LT
  | LE
  | GT
  | GE
  | ReMatch
  | ReNotMatch
  deriving (Eq, Ord)

instance Show RelOp where
  show NE = "!="
  show LT = "<"
  show LE = "<="
  show GT = ">"
  show GE = ">="
  show ReMatch = "=~"
  show ReNotMatch = "!~"

data BinaryOp
  = Unify
  | Disjunction
  | Add
  | Sub
  | Mul
  | Div
  | Equ
  | BinRelOp RelOp
  deriving (Eq, Ord)

instance Show BinaryOp where
  show Unify = "&"
  show Disjunction = "|"
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  show Equ = "=="
  show (BinRelOp op) = show op

data UnaryOp
  = Plus
  | Minus
  | Not
  | Star
  | UnaRelOp RelOp
  deriving (Eq, Ord)

instance Show UnaryOp where
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
litCons = ExprUnaryExpr . UnaryExprPrimaryExpr . PrimExprOperand . OpLiteral

idCons :: Identifer -> Expression
idCons = ExprUnaryExpr . UnaryExprPrimaryExpr . PrimExprOperand . OperandName . Identifier

unaryOpCons :: UnaryOp -> Expression -> Maybe Expression
unaryOpCons op (ExprUnaryExpr e) = Just $ ExprUnaryExpr $ UnaryExprUnaryOp op e
unaryOpCons _ _ = Nothing

binaryOpCons :: BinaryOp -> Expression -> Expression -> Expression
binaryOpCons = ExprBinaryOp

-- Below are functions for pretty printing the AST.

exprStr :: Expression -> String
exprStr e = show $ toLazyByteString $ exprBldIdent 0 e

exprBld :: Expression -> Builder
exprBld = exprBldIdent 0

exprBldIdent :: Int -> Expression -> Builder
exprBldIdent ident e =
  case e of
    ExprUnaryExpr ue -> unaryBld ident ue
    ExprBinaryOp op e1 e2 ->
      exprBldIdent ident e1
        <> char7 ' '
        <> string7 (show op)
        <> char7 ' '
        <> exprBldIdent ident e2

unaryBld :: Int -> UnaryExpr -> Builder
unaryBld ident e = case e of
  UnaryExprPrimaryExpr pe -> primBld ident pe
  UnaryExprUnaryOp op ue -> string7 (show op) <> unaryBld ident ue

primBld :: Int -> PrimaryExpr -> Builder
primBld ident e = case e of
  PrimExprOperand op -> opBld ident op
  PrimExprSelector pe sel -> primBld ident pe <> string7 "." <> selBld sel
  PrimExprIndex pe (Index ie) -> primBld ident pe <> string7 "[" <> exprBldIdent ident ie <> string7 "]"
  PrimExprArguments pe es ->
    primBld ident pe
      <> string7 "("
      <> foldr (\x acc -> exprBld x <> string7 ", " <> acc) mempty es
      <> string7 ")"

selBld :: Selector -> Builder
selBld e = case e of
  IDSelector is -> string7 is
  StringSelector s -> string7 s

opBld :: Int -> Operand -> Builder
opBld ident op = case op of
  OpLiteral lit -> litBld ident lit
  OpExpression e -> exprBldIdent ident e
  OperandName on -> opNameBld ident on

opNameBld :: Int -> OperandName -> Builder
opNameBld _ e = case e of
  Identifier i -> string7 i

litBld :: Int -> Literal -> Builder
litBld ident e = case e of
  StringLit s -> strLitBld s
  IntLit i -> integerDec i
  FloatLit f -> string7 (show f)
  BoolLit b -> if b then string7 "true" else string7 "false"
  TopLit -> string7 "_"
  BottomLit -> string7 "_|_"
  NullLit -> string7 "null"
  StructLit l -> structBld ident l
  ListLit l -> listBld l

strLitBld :: StringLit -> Builder
strLitBld (SimpleStringLit s) = string7 s

structBld :: Int -> [Declaration] -> Builder
structBld ident lit =
  if null lit
    then string7 "{}"
    else
      string7 "{\n"
        <> declsBld (ident + 1) lit
        <> string7 (replicate (ident * 2) ' ')
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
declBld i e = case e of
  FieldDecl f -> fieldDeclBld i f
  EllipsisDecl (Ellipsis _) -> string7 "..."
  Embedding eb -> exprBldIdent i eb

fieldDeclBld :: Int -> FieldDecl -> Builder
fieldDeclBld ident e = case e of
  Field ls fe ->
    foldr (\l acc -> labelBld l <> string7 ": " <> acc) mempty ls
      <> exprBldIdent ident fe

listBld :: ElementList -> Builder
listBld (EmbeddingList l) = string7 "[" <> goList l
 where
  goList :: [Embedding] -> Builder
  goList [] = string7 "]"
  goList [x] = exprBldIdent 0 x <> string7 "]"
  goList (x : xs) = exprBldIdent 0 x <> string7 ", " <> goList xs

labelBld :: Label -> Builder
labelBld (Label e) = labelExprBld e

labelExprBld :: LabelExpr -> Builder
labelExprBld e = case e of
  LabelName ln cnstr -> case cnstr of
    RegularLabel -> labelNameBld ln
    OptionalLabel -> labelNameBld ln <> string7 "?"
    RequiredLabel -> labelNameBld ln <> string7 "!"
  -- The LabelPattern should not be exported.
  LabelPattern le -> string7 "[" <> exprBldIdent 0 le <> string7 "]"

labelNameBld :: LabelName -> Builder
labelNameBld e = case e of
  LabelID i -> string7 i
  LabelString s -> string7 s
  LabelNameExpr ex -> char7 '(' <> exprBldIdent 0 ex <> char7 ')'
