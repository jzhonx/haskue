{-# LANGUAGE FlexibleContexts #-}

module Eval where

import AST
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Unify (unify)
import Value (Value (..))

eval :: (MonadError String m) => Expression -> m Value
eval (UnaryExprCons e) = evalUnaryExpr e
eval (BinaryOpCons op e1 e2) = evalBinary op e1 e2

evalLiteral :: (MonadError String m) => Literal -> m Value
evalLiteral (StringLit s) = return $ String s
evalLiteral (IntLit i) = return $ Int i
evalLiteral (StructLit s) =
  do
    xs <- mapM (mapM eval) s
    let orderedKeys = map fst xs
    m <- sequence $ Map.fromListWith (\mx my -> do x <- mx; y <- my; unify x y) (map (\(k, v) -> (k, return v)) xs)
    let (filteredKeys, _) =
          foldr
            (\k (l, set) -> if Set.notMember k set then (k : l, Set.insert k set) else (l, set))
            ([], Set.empty)
            orderedKeys
    return $
      Struct filteredKeys m

evalUnaryExpr :: (MonadError String m) => UnaryExpr -> m Value
evalUnaryExpr (PrimaryExprCons (Operand (Literal lit))) = evalLiteral lit
evalUnaryExpr (PrimaryExprCons (Operand (OpExpression expr))) = eval expr
evalUnaryExpr (UnaryOpCons op e) = evalUnaryOp op e

evalUnaryOp :: (MonadError String m) => UnaryOp -> UnaryExpr -> m Value
evalUnaryOp op e = do
  v <- evalUnaryExpr e
  case (op, v) of
    (Plus, Int i) -> return $ Int i
    (Minus, Int i) -> return $ Int (-i)
    (Star, _) -> return v
    _ -> throwError "evalUnaryOp: not an integer"

evalBinary :: (MonadError String m) => BinaryOp -> Expression -> Expression -> m Value
evalBinary op e1 e2 = do
  v1 <- eval e1
  v2 <- eval e2
  case (op, v1, v2) of
    (Unify, _, _) -> unify v1 v2
    (AST.Disjunction, _, _) -> return $ case (v1, v2) of
      (Value.Disjunction _ xs, Value.Disjunction _ ys) -> Value.Disjunction Nothing (xs ++ ys)
      (Value.Disjunction _ xs, _) -> Value.Disjunction Nothing (v2 : xs)
      (_, Value.Disjunction _ ys) -> Value.Disjunction Nothing (v1 : ys)
      (_, _) -> Value.Disjunction Nothing [v1, v2]
    (Add, Int i1, Int i2) -> return $ Int (i1 + i2)
    (Sub, Int i1, Int i2) -> return $ Int (i1 - i2)
    (Mul, Int i1, Int i2) -> return $ Int (i1 * i2)
    (Div, Int i1, Int i2) -> return $ Int (i1 `div` i2)
    _ -> throwError "evalBinary: not integers"
