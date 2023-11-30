module AST where

data Expression
  = UnaryExpr UnaryExpr
  | BinaryOp BinaryOp Expression Expression
  deriving (Show)

data UnaryExpr
  = PrimaryExpr PrimaryExpr
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
