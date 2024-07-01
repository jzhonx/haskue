module AST (
  Expression (..),
  UnaryExpr (..),
  PrimaryExpr (..),
  Selector (..),
  Operand (..),
  Literal (..),
  OperandName (..),
  StringLit (..),
  SimpleStringLit,
  Label (..),
  LabelExpr (..),
  LabelName (..),
  Identifer,
  BinaryOp (..),
  UnaryOp (..),
  RelOp (..),
  litCons,
  idCons,
  unaryOpCons,
  binaryOpCons,
  exprStr,
  exprBld,
  exprBldIdent,
  Quote (..),
)
where

import Data.ByteString.Builder (
  Builder,
  char7,
  integerDec,
  string7,
  toLazyByteString,
 )

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
  deriving (Eq, Show)

data Selector
  = IDSelector Identifer
  | StringSelector SimpleStringLit
  deriving (Eq, Show)

data Operand
  = OpLiteral Literal
  | OpExpression Expression
  | OperandName OperandName
  deriving (Eq, Show)

data Literal
  = StringLit StringLit
  | IntLit Integer
  | BoolLit Bool
  | TopLit
  | BottomLit
  | NullLit
  | StructLit [(Label, Expression)]
  deriving (Eq, Show)

newtype OperandName = Identifier Identifer deriving (Eq, Show)

newtype StringLit = SimpleStringLit SimpleStringLit deriving (Eq, Show)

type SimpleStringLit = String

newtype Label = Label LabelExpr deriving (Eq, Ord, Show)

newtype LabelExpr = LabelName LabelName deriving (Eq, Ord, Show)

data LabelName
  = LabelID Identifer
  | LabelString String
  deriving (Eq, Ord, Show)

type Identifer = String

data RelOp
  = NE
  deriving (Eq)

instance Show RelOp where
  show NE = "!="

data BinaryOp
  = Unify
  | Disjunction
  | Add
  | Sub
  | Mul
  | Div
  | Equ
  | BinRelOp RelOp
  deriving (Eq)

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
  deriving (Eq)

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
exprBldIdent ident e = case e of
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
  BoolLit b -> if b then string7 "true" else string7 "false"
  TopLit -> string7 "_"
  BottomLit -> string7 "_|_"
  NullLit -> string7 "null"
  StructLit l -> structBld ident l

strLitBld :: StringLit -> Builder
strLitBld (SimpleStringLit s) = string7 s

structBld :: Int -> [(Label, Expression)] -> Builder
structBld ident lit =
  if null lit
    then string7 "{}"
    else
      string7 "{\n"
        <> goFields lit
        <> string7 (replicate (ident * 2) ' ')
        <> char7 '}'
 where
  fieldBld (label, val) =
    string7 (replicate ((ident + 1) * 2) ' ')
      <> labelBld label
      <> string7 ": "
      <> exprBldIdent (ident + 1) val
      <> char7 '\n'
  goFields :: [(Label, Expression)] -> Builder
  goFields [] = string7 ""
  goFields (x : xs) =
    fieldBld x <> goFields xs

labelBld :: Label -> Builder
labelBld (Label e) = labelExprBld e

labelExprBld :: LabelExpr -> Builder
labelExprBld (LabelName e) = labelNameBld e

labelNameBld :: LabelName -> Builder
labelNameBld e = case e of
  LabelID i -> string7 i
  LabelString s -> string7 s
