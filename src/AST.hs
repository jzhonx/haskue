module AST where

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

data OperandName = Identifier Identifer deriving (Eq, Show)

data StringLit = SimpleStringLit SimpleStringLit deriving (Eq, Show)

type SimpleStringLit = String

data Label = Label LabelExpr deriving (Eq, Ord, Show)

data LabelExpr = LabelName LabelName deriving (Eq, Ord, Show)

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
  deriving (Eq)

instance Show UnaryOp where
  show Plus  = "+"
  show Minus = "-"
  show Not   = "!"
  show Star  = "*"

litCons :: Literal -> Expression
litCons = ExprUnaryExpr . UnaryExprPrimaryExpr . PrimExprOperand . OpLiteral
