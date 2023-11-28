module AST where

data Expression
  = UnaryExpr Literal
  | BinaryOp BinaryOp Expression Expression
  deriving (Show)

data Literal
  = StringLit StringLit
  | IntLit Integer
  | StructLit [(StringLit, Literal)]
  deriving (Eq, Show)

type StringLit = String

data BinaryOp = Unify

instance Show BinaryOp where
  show Unify = "&"
