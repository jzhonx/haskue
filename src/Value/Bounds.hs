{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.Bounds where

import qualified AST
import Common (BuildASTExpr (..))
import Control.DeepSeq (NFData (..))
import qualified Data.Text as T
import GHC.Generics (Generic)
import Value.Atom (Atom, aToLiteral)

newtype Bounds = Bounds {bdsList :: [Bound]}
  deriving (Eq, Generic, NFData)

data Bound
  = BdNE Atom
  | BdNumCmp BdNumCmp
  | BdStrMatch BdStrMatch
  | BdType BdType
  | BdIsAtom Atom -- helper type
  deriving (Eq, Generic, NFData)

data BdNumCmpOp
  = BdLT
  | BdLE
  | BdGT
  | BdGE
  deriving (Eq, Enum, Ord, Generic, NFData)

data Number = NumInt Integer | NumFloat Double
  deriving (Eq, Generic, NFData)

data BdNumCmp = BdNumCmpCons BdNumCmpOp Number
  deriving (Eq, Generic, NFData)

data BdStrMatch
  = BdReMatch T.Text
  | BdReNotMatch T.Text
  deriving (Eq, Generic, NFData)

data BdType
  = BdBool
  | BdInt
  | BdFloat
  | BdNumber
  | BdString
  deriving (Eq, Enum, Bounded, Generic, NFData)

instance Show Bounds where
  show b = AST.exprStr $ buildBoundsASTExpr b

instance BuildASTExpr Bounds where
  buildASTExpr _ b = return $ buildBoundsASTExpr b

instance Show Bound where
  show b = AST.exprStr $ buildBoundASTExpr b

instance BuildASTExpr Bound where
  buildASTExpr _ b = return $ buildBoundASTExpr b

buildBoundsASTExpr :: Bounds -> AST.Expression
buildBoundsASTExpr bds = foldl1 (\acc x -> pure $ AST.ExprBinaryOp (pure AST.Unify) acc x) es
 where
  es = map buildBoundASTExpr (bdsList bds)

buildBoundASTExpr :: Bound -> AST.Expression
buildBoundASTExpr b = case b of
  BdNE a -> litOp AST.NE (AST.wpVal $ aToLiteral a)
  BdNumCmp (BdNumCmpCons o n) -> case o of
    BdLT -> numOp AST.LT n
    BdLE -> numOp AST.LE n
    BdGT -> numOp AST.GT n
    BdGE -> numOp AST.GE n
  BdStrMatch m -> case m of
    BdReMatch s -> litOp AST.ReMatch (AST.wpVal $ AST.strToLit s)
    BdReNotMatch s -> litOp AST.ReNotMatch (AST.wpVal $ AST.strToLit s)
  BdType t -> AST.idCons (pure $ T.pack (show t))
  BdIsAtom a -> AST.litCons (aToLiteral a)
 where
  litOp :: AST.RelOpNode -> AST.LiteralNode -> AST.Expression
  litOp op l =
    let uop = pure $ AST.UnaRelOp op
        ue = AST.PrimExprOperand AST.<<^>> AST.OpLiteral AST.<^> pure l
     in AST.ExprUnaryExpr
          AST.<<^>> AST.UnaryExprUnaryOp uop
          AST.<<^>> AST.UnaryExprPrimaryExpr
          AST.<^> ue

  numOp :: AST.RelOpNode -> Number -> AST.Expression
  numOp op n =
    AST.ExprUnaryExpr
      AST.<<^>> AST.UnaryExprUnaryOp (pure $ AST.UnaRelOp op)
      AST.<<^>> AST.UnaryExprPrimaryExpr
      AST.<<^>> AST.PrimExprOperand
      AST.<<^>> AST.OpLiteral
      AST.<^> case n of
        NumInt i -> pure $ AST.IntLit i
        NumFloat f -> pure $ AST.FloatLit f

bdRep :: Bound -> String
bdRep b = case b of
  BdNE _ -> show AST.NE
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
