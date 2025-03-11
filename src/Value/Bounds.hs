module Value.Bounds where

import qualified AST
import Class (BuildASTExpr (..), TreeRepBuilder (..))
import Value.Atom (Atom, aToLiteral)

newtype Bounds = Bounds {bdsList :: [Bound]}
  deriving (Eq)

data Bound
  = BdNE Atom
  | BdNumCmp BdNumCmp
  | BdStrMatch BdStrMatch
  | BdType BdType
  | BdIsAtom Atom -- helper type
  deriving (Eq)

data BdNumCmpOp
  = BdLT
  | BdLE
  | BdGT
  | BdGE
  deriving (Eq, Enum, Ord)

data Number = NumInt Integer | NumFloat Double
  deriving (Eq)

data BdNumCmp = BdNumCmpCons BdNumCmpOp Number
  deriving (Eq)

data BdStrMatch
  = BdReMatch String
  | BdReNotMatch String
  deriving (Eq)

data BdType
  = BdBool
  | BdInt
  | BdFloat
  | BdNumber
  | BdString
  deriving (Eq, Enum, Bounded)

instance Show Bounds where
  show b = AST.exprStr $ buildBoundsASTExpr b

instance BuildASTExpr Bounds where
  buildASTExpr _ b = return $ buildBoundsASTExpr b

instance Show Bound where
  show b = AST.exprStr $ buildBoundASTExpr b

instance TreeRepBuilder Bound where
  repTree _ b = "(" <> show b <> ")"

instance BuildASTExpr Bound where
  buildASTExpr _ b = return $ buildBoundASTExpr b

buildBoundsASTExpr :: Bounds -> AST.Expression
buildBoundsASTExpr bds = foldr1 (AST.ExprBinaryOp AST.Unify) es
 where
  es = map buildBoundASTExpr (bdsList bds)

buildBoundASTExpr :: Bound -> AST.Expression
buildBoundASTExpr b = case b of
  BdNE a -> litOp AST.NE (aToLiteral a)
  BdNumCmp (BdNumCmpCons o n) -> case o of
    BdLT -> numOp AST.LT n
    BdLE -> numOp AST.LE n
    BdGT -> numOp AST.GT n
    BdGE -> numOp AST.GE n
  BdStrMatch m -> case m of
    BdReMatch s -> litOp AST.ReMatch (AST.StringLit $ AST.SimpleStringLit s)
    BdReNotMatch s -> litOp AST.ReNotMatch (AST.StringLit $ AST.SimpleStringLit s)
  BdType t -> AST.idCons (show t)
  BdIsAtom a -> AST.litCons (aToLiteral a)
 where
  litOp :: AST.RelOp -> AST.Literal -> AST.Expression
  litOp op l =
    AST.ExprUnaryExpr $
      AST.UnaryExprUnaryOp
        (AST.UnaRelOp op)
        (AST.UnaryExprPrimaryExpr . AST.PrimExprOperand . AST.OpLiteral $ l)

  numOp :: AST.RelOp -> Number -> AST.Expression
  numOp op n =
    AST.ExprUnaryExpr $
      AST.UnaryExprUnaryOp
        (AST.UnaRelOp op)
        ( AST.UnaryExprPrimaryExpr . AST.PrimExprOperand . AST.OpLiteral $ case n of
            NumInt i -> AST.IntLit i
            NumFloat f -> AST.FloatLit f
        )

bdRep :: Bound -> String
bdRep b = case b of
  BdNE _ -> show $ AST.NE
  BdNumCmp (BdNumCmpCons o _) -> show o
  BdStrMatch m -> case m of
    BdReMatch _ -> show AST.ReMatch
    BdReNotMatch _ -> show AST.ReNotMatch
  BdType t -> show t
  BdIsAtom _ -> "="

instance Show BdNumCmpOp where
  show o = show $ case o of
    BdLT -> AST.LT
    BdLE -> AST.LE
    BdGT -> AST.GT
    BdGE -> AST.GE

instance Show BdType where
  show BdBool = "bool"
  show BdInt = "int"
  show BdFloat = "float"
  show BdNumber = "number"
  show BdString = "string"

instance Ord Number where
  compare (NumInt i1) (NumInt i2) = compare i1 i2
  compare (NumFloat f1) (NumFloat f2) = compare f1 f2
  compare (NumInt i) (NumFloat f) = compare (fromIntegral i) f
  compare (NumFloat f) (NumInt i) = compare f (fromIntegral i)
