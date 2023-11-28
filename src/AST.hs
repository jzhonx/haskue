module AST where

data Expression
  = UnaryExpr Literal
  | BinaryOp BinaryOp Expression Expression
  deriving (Show)

data Literal
  = StringLit StringLit
  | IntLit Integer
  | StructLit [(StringLit, Expression)]
  deriving (Show)

type StringLit = String

data BinaryOp
  = Unify
  | Add
  | Sub
  | Mul
  | Div

instance Show BinaryOp where
  show Unify = "&"
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
