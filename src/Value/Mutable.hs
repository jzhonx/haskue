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
data Mutable t
  = SFunc (StatefulFunc t)
  | Ref (Reference t)

-- | StatefulFunc is a tree node whose value can be changed.
data StatefulFunc t = StatefulFunc
  { sfnName :: String
  , sfnType :: MutableType
  , sfnArgs :: [t]
  -- ^ Args stores the arguments that may or may not need to be evaluated.
  , sfnExpr :: forall m. (Env m) => m AST.Expression
  -- ^ sfnExpr is needed when the Mutable is created dynamically, for example, dynamically creating a same field
  -- in a struct, {a: string, f: "a", (f): "b"}. In this case, no original expression for the expr, string & "b", is
  -- available.
  -- The return value of the method should be stored in the tree.
  , sfnMethod :: forall s m. (MutableEnv s m t) => [t] -> m ()
  , sfnValue :: Maybe t
  -- ^ sfnValue stores the non-atom, non-Mutable (isTreeValue true) value.
  }

data MutableType = RegularMutable | DisjMutable | IndexMutable
  deriving (Eq, Show)

data Reference t = Reference
  { refPath :: Path
  , refValue :: Maybe t
  }

instance (Eq t) => Eq (Mutable t) where
  (==) (SFunc m1) (SFunc m2) = m1 == m2
  (==) (Ref r1) (Ref r2) = r1 == r2
  (==) _ _ = False

instance (BuildASTExpr t) => BuildASTExpr (Mutable t) where
  buildASTExpr c (SFunc m) = buildASTExpr c m
  buildASTExpr c (Ref r) = buildASTExpr c r

instance (Eq t) => Eq (StatefulFunc t) where
  (==) f1 f2 =
    sfnName f1 == sfnName f2
      && sfnType f1 == sfnType f2
      && sfnArgs f1 == sfnArgs f2

instance (BuildASTExpr t) => BuildASTExpr (StatefulFunc t) where
  buildASTExpr c mut = do
    if c || requireMutableConcrete mut
      -- If the expression must be concrete, but due to incomplete evaluation, we need to use original expression.
      then sfnExpr mut
      else maybe (sfnExpr mut) (buildASTExpr c) (sfnValue mut)

instance (Eq t) => Eq (Reference t) where
  (==) r1 r2 = refPath r1 == refPath r2

instance (BuildASTExpr t) => BuildASTExpr (Reference t) where
  buildASTExpr _ _ = throwErrSt "AST should not be built from Reference"

isMutableRef :: Mutable t -> Bool
isMutableRef mut = case mut of
  Ref _ -> True
  _ -> False

isMutableIndex :: Mutable t -> Bool
isMutableIndex mut = case mut of
  SFunc m -> sfnType m == IndexMutable
  _ -> False

requireMutableConcrete :: StatefulFunc t -> Bool
requireMutableConcrete mut
  | RegularMutable <- sfnType mut = sfnName mut `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
requireMutableConcrete _ = False

getMutName :: Mutable t -> String
getMutName (SFunc mut) = sfnName mut
getMutName (Ref ref) = "ref " ++ show (refPath ref)

getMutVal :: Mutable t -> Maybe t
getMutVal (SFunc mut) = sfnValue mut
getMutVal (Ref ref) = refValue ref

setMutVal :: Mutable t -> t -> Mutable t
setMutVal (SFunc mut) t = SFunc $ mut{sfnValue = Just t}
setMutVal (Ref ref) t = Ref $ ref{refValue = Just t}

resetMutVal :: Mutable t -> Mutable t
resetMutVal (SFunc mut) = SFunc $ mut{sfnValue = Nothing}
resetMutVal (Ref ref) = Ref $ ref{refValue = Nothing}

invokeMutMethod :: (MutableEnv s m t) => StatefulFunc t -> m ()
invokeMutMethod mut = sfnMethod mut (sfnArgs mut)

modifyRegMut :: (StatefulFunc t -> StatefulFunc t) -> Mutable t -> Mutable t
modifyRegMut f (SFunc m) = SFunc $ f m
modifyRegMut _ r = r

mutValStub :: Mutable t
mutValStub =
  SFunc $
    stubRegMutable
      { sfnName = "mvStub"
      , sfnMethod = \_ -> throwErrSt "mutateValStub: sfnMethod should not be called"
      }

stubRegMutable :: StatefulFunc t
stubRegMutable =
  StatefulFunc
    { sfnName = ""
    , sfnType = RegularMutable
    , sfnArgs = []
    , sfnExpr = throwErrSt "stub mutable"
    , sfnMethod = \_ -> throwErrSt "stub mutable"
    , sfnValue = Nothing
    }

mkUnaryOp ::
  forall t.
  (BuildASTExpr t) =>
  AST.UnaryOp ->
  (forall s m. (MutableEnv s m t) => t -> m ()) ->
  t ->
  Mutable t
mkUnaryOp op f n =
  SFunc $
    StatefulFunc
      { sfnMethod = g
      , sfnType = RegularMutable
      , sfnExpr = buildUnaryExpr op n
      , sfnName = show op
      , sfnArgs = [n]
      , sfnValue = Nothing
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
  SFunc $
    StatefulFunc
      { sfnMethod = g
      , sfnType = case op of
          AST.Disjunction -> DisjMutable
          _ -> RegularMutable
      , sfnExpr = buildBinaryExpr op l r
      , sfnName = show op
      , sfnArgs = [l, r]
      , sfnValue = Nothing
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

mkRefMutable :: Path -> Mutable t
mkRefMutable tp =
  Ref $
    Reference
      { refPath = tp
      , refValue = Nothing
      }
