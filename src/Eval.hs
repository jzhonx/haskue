{-# LANGUAGE FlexibleContexts #-}

module Eval where

import AST
  ( BinaryOp (..),
    Expression (..),
    Literal (..),
  )
import Control.Monad.Except (MonadError)
import Unify (unify)
import Value (Value (..))

eval :: (MonadError String m) => Expression -> m Value
eval (UnaryExpr lit) = evalUnary lit
eval (BinaryOp op e1 e2) = evalBinary op e1 e2

evalUnary :: (MonadError String m) => Literal -> m Value
evalUnary (StringLit s) = return $ String s
evalUnary (IntLit i) = return $ Int i
evalUnary (StructLit s) = do
  xs <- mapM (mapM evalUnary) s
  return $ Struct xs

evalBinary :: (MonadError String m) => BinaryOp -> Expression -> Expression -> m Value
evalBinary Unify e1 e2 = do
  v1 <- eval e1
  v2 <- eval e2
  unify v1 v2
