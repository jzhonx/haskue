{-# LANGUAGE FlexibleContexts #-}

module Eval where

import AST
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Unify (unify)
import Value (Value (..))

eval :: (MonadError String m) => Expression -> m Value
eval (UnaryExpr (PrimaryExpr (Operand (Literal lit)))) = evalUnary lit
eval (UnaryExpr (PrimaryExpr (Operand (OpExpression expr)))) = eval expr
eval (BinaryOp op e1 e2) = evalBinary op e1 e2

evalUnary :: (MonadError String m) => Literal -> m Value
evalUnary (StringLit s) = return $ String s
evalUnary (IntLit i) = return $ Int i
evalUnary (StructLit s) =
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
