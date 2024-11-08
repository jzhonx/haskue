{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Func where

import qualified AST
import Class
import Config
import Control.Monad.Except (throwError)
import Control.Monad.Reader (MonadReader, ask, runReaderT)
import Env
import Path
import Value.TMonad

type FuncEnv s m t = (TMonad s m t, MonadReader (Config t) m)

data Func t = Func
  { fncName :: String
  , fncType :: FuncType
  , -- Args stores the arguments that may or may not need to be evaluated.
    fncArgs :: [t]
  , -- fncExpr is needed because if the function is created dynamically, for example by having a second field in a struct,
    -- no original expression is available.
    fncExpr :: forall m. (Env m) => m AST.Expression
  , -- Note that the return value of the function should be stored in the tree.
    fncFunc :: forall s m. (FuncEnv s m t) => [t] -> m Bool
  , -- fncTempRes stores the temporary non-atom, non-function (isTreeValue true) result of the function.
    -- It is only used for showing purpose. It is not used for evaluation.
    fncTempRes :: Maybe t
  }

data FuncType = RegularFunc | DisjFunc | RefFunc | IndexFunc
  deriving (Eq, Show)

instance (Eq t) => Eq (Func t) where
  (==) f1 f2 =
    fncName f1 == fncName f2
      && fncType f1 == fncType f2
      && fncArgs f1 == fncArgs f2
      && fncTempRes f1 == fncTempRes f2

instance (BuildASTExpr t) => BuildASTExpr (Func t) where
  buildASTExpr c fn = do
    if c || requireFuncConcrete fn
      -- If the expression must be concrete, but due to incomplete evaluation, we need to use original expression.
      then fncExpr fn
      else maybe (fncExpr fn) (buildASTExpr c) (fncTempRes fn)

isFuncRef :: Func t -> Bool
isFuncRef fn = fncType fn == RefFunc

isFuncIndex :: Func t -> Bool
isFuncIndex fn = fncType fn == IndexFunc

requireFuncConcrete :: Func t -> Bool
requireFuncConcrete fn = case fncType fn of
  RegularFunc -> fncName fn `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
  _ -> False

mkStubFunc :: (forall s m. (FuncEnv s m t) => [t] -> m Bool) -> Func t
mkStubFunc f =
  Func
    { fncName = ""
    , fncType = RegularFunc
    , fncArgs = []
    , fncExpr = return $ AST.litCons AST.BottomLit
    , fncFunc = f
    , fncTempRes = Nothing
    }

mkUnaryOp ::
  forall t.
  (BuildASTExpr t) =>
  AST.UnaryOp ->
  (forall s m. (FuncEnv s m t) => t -> m Bool) ->
  t ->
  Func t
mkUnaryOp op f n =
  Func
    { fncFunc = g
    , fncType = RegularFunc
    , fncExpr = buildUnaryExpr op n
    , fncName = show op
    , fncArgs = [n]
    , fncTempRes = Nothing
    }
 where
  g :: (FuncEnv s m t) => [t] -> m Bool
  g [x] = f x
  g _ = throwError "invalid number of arguments for unary function"

buildUnaryExpr :: (Env m, BuildASTExpr t) => AST.UnaryOp -> t -> m AST.Expression
buildUnaryExpr op t = do
  let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
  te <- buildASTExpr c t
  case te of
    (AST.ExprUnaryExpr ue) -> return $ AST.ExprUnaryExpr $ AST.UnaryExprUnaryOp op ue
    e ->
      return $
        AST.ExprUnaryExpr $
          AST.UnaryExprUnaryOp
            op
            (AST.UnaryExprPrimaryExpr . AST.PrimExprOperand $ AST.OpExpression e)

mkBinaryOp ::
  forall t.
  (BuildASTExpr t) =>
  AST.BinaryOp ->
  (forall s m. (FuncEnv s m t) => t -> t -> m Bool) ->
  t ->
  t ->
  Func t
mkBinaryOp op f l r =
  Func
    { fncFunc = g
    , fncType = case op of
        AST.Disjunction -> DisjFunc
        _ -> RegularFunc
    , fncExpr = buildBinaryExpr op l r
    , fncName = show op
    , fncArgs = [l, r]
    , fncTempRes = Nothing
    }
 where
  g :: (FuncEnv s m t) => [t] -> m Bool
  g [x, y] = f x y
  g _ = throwError "invalid number of arguments for binary function"

buildBinaryExpr :: (Env e, BuildASTExpr t) => AST.BinaryOp -> t -> t -> e AST.Expression
buildBinaryExpr op l r = do
  let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
  xe <- buildASTExpr c l
  ye <- buildASTExpr c r
  return $ AST.ExprBinaryOp op xe ye

mkBinaryOpDir ::
  forall t.
  (BuildASTExpr t) =>
  AST.BinaryOp ->
  (forall s m. (FuncEnv s m t) => t -> t -> m Bool) ->
  (BinOpDirect, t) ->
  (BinOpDirect, t) ->
  Func t
mkBinaryOpDir rep op (d1, t1) (_, t2) =
  case d1 of
    L -> mkBinaryOp rep op t1 t2
    R -> mkBinaryOp rep op t2 t1
