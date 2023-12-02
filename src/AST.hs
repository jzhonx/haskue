module AST where

data Expression
  = UnaryExprCons UnaryExpr
  | BinaryOpCons BinaryOp Expression Expression
  deriving (Show)

data UnaryExpr
  = PrimaryExprCons PrimaryExpr
  | UnaryOpCons UnaryOp UnaryExpr
  deriving (Show)

data PrimaryExpr
  = Operand Operand
  deriving (Show)

data Operand
  = Literal Literal
  | OpExpression Expression
  deriving (Show)

data Literal
  = StringLit StringLit
  | IntLit Integer
  | BoolLit Bool
  | TopLit
  | BottomLit
  | NullLit
  | StructLit [(StringLit, Expression)]
  deriving (Show)

type StringLit = String

data BinaryOp
  = Unify
  | Disjunction
  | Add
  | Sub
  | Mul
  | Div

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

instance Show UnaryOp where
  show Plus = "+"
  show Minus = "-"
  show Not = "!"
  show Star = "*"
