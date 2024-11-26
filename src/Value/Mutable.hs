{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Mutable where

import qualified AST
import Class
import Config
import Control.Monad.Reader (MonadReader)
import Env
import Error
import Path
import TMonad

type MutableEnv s m t = (TMonad s m t, MonadReader (Config t) m)

-- | Mutable is a tree node whose value can be changed.
data Mutable t = Mutable
  { mutName :: String
  , mutType :: MutableType
  , mutArgs :: [t]
  -- ^ Args stores the arguments that may or may not need to be evaluated.
  , mutExpr :: forall m. (Env m) => m AST.Expression
  -- ^ mutExpr is needed when the Mutable is created dynamically, for example, dynamically creating a same field
  -- in a struct, {a: string, f: "a", (f): "b"}. In this case, no original expression for the expr, string & "b", is
  -- available.
  -- The return value of the method should be stored in the tree.
  , mutMethod :: forall s m. (MutableEnv s m t) => [t] -> m ()
  , mutValue :: Maybe t
  -- ^ mutValue stores the non-atom, non-Mutable (isTreeValue true) value.
  }

data MutableType = RegularMutable | DisjMutable | RefMutable | IndexMutable
  deriving (Eq, Show)

instance (Eq t) => Eq (Mutable t) where
  (==) f1 f2 =
    mutName f1 == mutName f2
      && mutType f1 == mutType f2
      && mutArgs f1 == mutArgs f2

instance (BuildASTExpr t) => BuildASTExpr (Mutable t) where
  buildASTExpr c mut = do
    if c || requireMutableConcrete mut
      -- If the expression must be concrete, but due to incomplete evaluation, we need to use original expression.
      then mutExpr mut
      else maybe (mutExpr mut) (buildASTExpr c) (mutValue mut)

isMutableRef :: Mutable t -> Bool
isMutableRef mut = mutType mut == RefMutable

isMutableIndex :: Mutable t -> Bool
isMutableIndex mut = mutType mut == IndexMutable

requireMutableConcrete :: Mutable t -> Bool
requireMutableConcrete mut = case mutType mut of
  RegularMutable -> mutName mut `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
  _ -> False

setMutableState :: Mutable t -> t -> Mutable t
setMutableState mut t = mut{mutValue = Just t}

resetMutableVal :: Mutable t -> Mutable t
resetMutableVal mut = mut{mutValue = Nothing}

invokeMutMethod :: (MutableEnv s m t) => Mutable t -> m ()
invokeMutMethod mut = mutMethod mut (mutArgs mut)

mkStubMutable :: (forall s m. (MutableEnv s m t) => [t] -> m ()) -> Mutable t
mkStubMutable f =
  Mutable
    { mutName = ""
    , mutType = RegularMutable
    , mutArgs = []
    , mutExpr = throwErrSt "stub mutable"
    , mutMethod = f
    , mutValue = Nothing
    }

mkUnaryOp ::
  forall t.
  (BuildASTExpr t) =>
  AST.UnaryOp ->
  (forall s m. (MutableEnv s m t) => t -> m ()) ->
  t ->
  Mutable t
mkUnaryOp op f n =
  Mutable
    { mutMethod = g
    , mutType = RegularMutable
    , mutExpr = buildUnaryExpr op n
    , mutName = show op
    , mutArgs = [n]
    , mutValue = Nothing
    }
 where
  g :: (MutableEnv s m t) => [t] -> m ()
  g [x] = f x
  g _ = throwErrSt "invalid number of arguments for unary function"

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
  (forall s m. (MutableEnv s m t) => t -> t -> m ()) ->
  t ->
  t ->
  Mutable t
mkBinaryOp op f l r =
  Mutable
    { mutMethod = g
    , mutType = case op of
        AST.Disjunction -> DisjMutable
        _ -> RegularMutable
    , mutExpr = buildBinaryExpr op l r
    , mutName = show op
    , mutArgs = [l, r]
    , mutValue = Nothing
    }
 where
  g :: (MutableEnv s m t) => [t] -> m ()
  g [x, y] = f x y
  g _ = throwErrSt "invalid number of arguments for binary function"

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
  (forall s m. (MutableEnv s m t) => t -> t -> m ()) ->
  (BinOpDirect, t) ->
  (BinOpDirect, t) ->
  Mutable t
mkBinaryOpDir rep op (d1, t1) (_, t2) =
  case d1 of
    L -> mkBinaryOp rep op t1 t2
    R -> mkBinaryOp rep op t2 t1
