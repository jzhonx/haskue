{-# LANGUAGE FlexibleContexts #-}

module Transform where

import           AST
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import           Debug.Trace

transform :: Expression -> Expression
transform = transExpr

transExpr :: Expression -> Expression
transExpr e = case e of
  ExprUnaryExpr ue -> ExprUnaryExpr $ transUnaryExpr ue
  ExprBinaryOp op e1 e2 ->
    let _e1 = transExpr e1
        _e2 = transExpr e2
     in ExprBinaryOp op _e1 _e2

transUnaryExpr :: UnaryExpr -> UnaryExpr
transUnaryExpr ue = case ue of
  UnaryExprPrimaryExpr pe -> UnaryExprPrimaryExpr $ transPrimaryExpr pe
  UnaryExprUnaryOp op ue1 -> UnaryExprUnaryOp op (transUnaryExpr ue1)

transPrimaryExpr :: PrimaryExpr -> PrimaryExpr
transPrimaryExpr pe = case pe of
  PrimExprOperand op       -> PrimExprOperand $ transOperand op
  PrimExprSelector pe1 sel -> PrimExprSelector (transPrimaryExpr pe1) sel

transOperand :: Operand -> Operand
transOperand op = case op of
  OpLiteral lit  -> OpLiteral $ transLiteral lit
  OpExpression e -> OpExpression $ transExpr e
  _              -> op

transLiteral :: Literal -> Literal
transLiteral lit = case lit of
  StructLit l -> StructLit $ simplifyStructLit l
  _           -> lit

-- | Simplify struct literals by adding Unify for duplicate fields.
simplifyStructLit :: [(Label, Expression)] -> [(Label, Expression)]
-- Notice foldl is used to keep the order of the fields.
simplifyStructLit lit = fst $ foldl f ([], Set.empty) (trace (show lit) lit)
  where
    unifyFields :: Expression -> Expression -> Expression
    unifyFields = ExprBinaryOp Unify

    fieldsMap = Map.fromListWith unifyFields lit

    f :: ([(Label, Expression)], Set.Set Label) -> (Label, Expression) -> ([(Label, Expression)], Set.Set Label)
    f (xs, visited) (label, _) =
      if label `Set.member` visited
        then (xs, visited)
        else
          let _visited = Set.insert label visited
              _xs = xs ++ [(label, fieldsMap Map.! label)]
           in (_xs, _visited)
