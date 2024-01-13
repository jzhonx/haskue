module AST where

data Expression
  = ExprUnaryExpr UnaryExpr
  | ExprBinaryOp BinaryOp Expression Expression
  deriving (Show)

data UnaryExpr
  = UnaryExprPrimaryExpr PrimaryExpr
  | UnaryExprUnaryOp UnaryOp UnaryExpr
  deriving (Show)

data PrimaryExpr
  = PrimExprOperand Operand
  | PrimExprSelector PrimaryExpr Selector
  deriving (Show)

newtype Selector = IDSelector Identifer deriving (Show)

data Operand
  = OpLiteral Literal
  | OpExpression Expression
  | OperandName OperandName
  deriving (Show)

data Literal
  = StringLit StringLit
  | IntLit Integer
  | BoolLit Bool
  | TopLit
  | BottomLit
  | NullLit
  | StructLit [(Label, Expression)]
  deriving (Show)

data OperandName = Identifier Identifer deriving (Show)

data StringLit = SimpleStringLit SimpleStringLit deriving (Show)

type SimpleStringLit = String

data Label = Label LabelExpr deriving (Show)

data LabelExpr = LabelName LabelName deriving (Show)

data LabelName = LabelID Identifer | LabelString String deriving (Show)

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
  show Unify       = "&"
  show Disjunction = "|"
  show Add         = "+"
  show Sub         = "-"
  show Mul         = "*"
  show Div         = "/"

data UnaryOp
  = Plus
  | Minus
  | Not
  | Star

instance Show UnaryOp where
  show Plus  = "+"
  show Minus = "-"
  show Not   = "!"
  show Star  = "*"
