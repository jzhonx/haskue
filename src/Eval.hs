{-# LANGUAGE FlexibleContexts #-}

module Eval where

import AST
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Unify (unify)
import Value (Value (..))

eval :: (MonadError String m) => Expression -> m Value
eval expr = do
  r <- eval' expr
  return $ fromEvalResult r

data EvalResult = PartialDefault Value | Complete Value

fromEvalResult :: EvalResult -> Value
fromEvalResult (PartialDefault _) = Bottom "marked value should be associated with a disjunction"
fromEvalResult (Complete v) = v

eval' :: (MonadError String m) => Expression -> m EvalResult
eval' (UnaryExprCons e) = evalUnaryExpr e
eval' (BinaryOpCons op e1 e2) = evalBinary op e1 e2

evalLiteral :: (MonadError String m) => Literal -> m EvalResult
evalLiteral lit = fmap Complete (f lit)
  where
    f (StringLit s) = return $ String s
    f (IntLit i) = return $ Int i
    f (BoolLit b) = return $ Bool b
    f TopLit = return Top
    f BottomLit = return $ Bottom ""
    f NullLit = return Null
    f (StructLit s) =
      let convertField (label, e) = do
            v <- eval' e
            return (label, fromEvalResult v)
       in do
            xs <- mapM convertField s
            let orderedKeys = map fst xs
            m <- sequence $ Map.fromListWith (\mx my -> do x <- mx; y <- my; unify x y) (map (\(k, v) -> (k, return v)) xs)
            let (filteredKeys, _) =
                  foldr
                    (\k (l, set) -> if Set.notMember k set then (k : l, Set.insert k set) else (l, set))
                    ([], Set.empty)
                    orderedKeys
            return $ Struct filteredKeys m

evalUnaryExpr :: (MonadError String m) => UnaryExpr -> m EvalResult
evalUnaryExpr (PrimaryExprCons (Operand (Literal lit))) = evalLiteral lit
evalUnaryExpr (PrimaryExprCons (Operand (OpExpression expr))) = eval' expr
evalUnaryExpr (UnaryOpCons op e) = evalUnaryOp op e

evalUnaryOp :: (MonadError String m) => UnaryOp -> UnaryExpr -> m EvalResult
evalUnaryOp op e =
  do
    v <- evalUnaryExpr e
    case v of
      Complete v' -> evalVal v'
      PartialDefault _ -> return $ Complete $ Bottom "marked value should be associated with a disjunction"
  where
    evalVal val = do
      case (op, val) of
        (Plus, Int i) -> return $ Complete $ Int i
        (Minus, Int i) -> return $ Complete $ Int (-i)
        (Star, _) -> return $ PartialDefault val
        (Not, Bool b) -> return $ Complete $ Bool (not b)
        _ -> throwError "evalUnaryOp: not an integer"

evalBinary :: (MonadError String m) => BinaryOp -> Expression -> Expression -> m EvalResult
evalBinary op e1 e2 = do
  r1 <- eval' e1
  r2 <- eval' e2
  evalRes op r1 r2
  where
    evalRes AST.Disjunction r1 r2 = case (r1, r2) of
      (Complete (Value.Disjunction defaults xs), PartialDefault v2) ->
        return $ Complete $ Value.Disjunction (v2 : defaults) xs
      (Complete v1, PartialDefault v2) -> return $ Complete $ Value.Disjunction [v2] [v1]
      (Complete v1, Complete v2) -> return $ Complete $ join v1 v2
      (PartialDefault _, _) -> evalRes op r2 r1
    evalRes _ r1 r2 =
      let v1 = fromEvalResult r1
          v2 = fromEvalResult r2
       in fmap Complete (evalVal v1 v2)
    evalVal v1 v2 = do
      case (op, v1, v2) of
        (Unify, _, _) -> unify v1 v2
        (Add, Int i1, Int i2) -> return $ Int (i1 + i2)
        (Sub, Int i1, Int i2) -> return $ Int (i1 - i2)
        (Mul, Int i1, Int i2) -> return $ Int (i1 * i2)
        (Div, Int i1, Int i2) -> return $ Int (i1 `div` i2)
        _ -> throwError "evalBinary: not integers"
    join (Value.Disjunction df1 xs) (Value.Disjunction df2 ys) = Value.Disjunction (df1 ++ df2) (xs ++ ys)
    join (Value.Disjunction d xs) y = Value.Disjunction d (y : xs)
    join x (Value.Disjunction d ys) = Value.Disjunction d (x : ys)
    join x y = Value.Disjunction [] [x, y]
