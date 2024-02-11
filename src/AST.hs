module AST
  ( Expression (..),
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
    litCons,
    exprStr,
    exprBld,
  )
where

import Data.ByteString.Builder
  ( Builder,
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

data BinaryOp
  = Unify
  | Disjunction
  | Add
  | Sub
  | Mul
  | Div
  deriving (Eq)

instance Show BinaryOp where
  show Unify = "&"
  show Disjunction = "|"
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"

data UnaryOp
  = Plus
  | Minus
  | Not
  | Star
  deriving (Eq)

instance Show UnaryOp where
  show Plus = "+"
  show Minus = "-"
  show Not = "!"
  show Star = "*"

litCons :: Literal -> Expression
litCons = ExprUnaryExpr . UnaryExprPrimaryExpr . PrimExprOperand . OpLiteral

exprStr :: Expression -> String
exprStr e = show $ toLazyByteString $ exprBld 0 e

exprBld :: Int -> Expression -> Builder
exprBld ident e = case e of
  ExprUnaryExpr ue -> unaryBld ident ue
  ExprBinaryOp op e1 e2 ->
    exprBld ident e1
      <> char7 ' '
      <> string7 (show op)
      <> char7 ' '
      <> exprBld ident e2

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
  OpExpression e -> exprBld ident e
  OperandName on -> opNameBld ident on

opNameBld :: Int -> OperandName -> Builder
opNameBld _ e = case e of
  Identifier i -> string7 i

litBld :: Int -> Literal -> Builder
litBld ident e = case e of
  StringLit s -> strLitBld s
  IntLit i -> integerDec i
  BoolLit b -> string7 (show b)
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
        <> exprBld (ident + 1) val
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
