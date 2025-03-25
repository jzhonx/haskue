{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Mutable where

import qualified AST
import Common (BuildASTExpr (..), Env)
import Exception (throwErrSt)
import MutEnv (MutableEnv)
import Value.Comprehension
import Value.Reference

-- | Mutable is a tree node whose value can be changed.
data Mutable t
  = SFunc (StatefulFunc t)
  | Ref (Reference t)
  | Compreh (Comprehension t)
  | UEmbeds (UnifyEmbeds t)

data MutableType = RegularMutable | DisjMutable
  deriving (Eq, Show)

-- | StatefulFunc is a tree node that represents a function.
data StatefulFunc t = StatefulFunc
  { sfnName :: String
  , sfnType :: MutableType
  , sfnArgs :: [t]
  -- ^ Args stores the arguments that may or may not need to be evaluated.
  , sfnExpr :: forall r m. (Env r m) => m AST.Expression
  -- ^ sfnExpr is needed when the Mutable is created dynamically, for example, dynamically creating a same field
  -- in a struct, {a: string, f: "a", (f): "b"}. In this case, no original expression for the expr, string & "b", is
  -- available.
  -- The return value of the method should be stored in the tree.
  , sfnMethod :: forall s r m. (MutableEnv s r t m) => [t] -> m ()
  , sfnValue :: Maybe t
  -- ^ sfnValue stores the non-atom, non-Mutable (isTreeValue true) value.
  }

-- | UnifyEmbeds is a stateful function node that unifies the embeds of a struct with itself.
data UnifyEmbeds t = UnifyEmbeds
  { ueStruct :: t
  , ueValue :: Maybe t
  }

instance (Eq t) => Eq (Mutable t) where
  (==) (SFunc m1) (SFunc m2) = m1 == m2
  (==) (Ref r1) (Ref r2) = r1 == r2
  (==) (Compreh c1) (Compreh c2) = c1 == c2
  (==) (UEmbeds u1) (UEmbeds u2) = u1 == u2
  (==) _ _ = False

instance (BuildASTExpr t) => BuildASTExpr (Mutable t) where
  buildASTExpr c (SFunc m) = buildASTExpr c m
  buildASTExpr _ (Ref _) = throwErrSt "AST should not be built from Reference"
  buildASTExpr _ (Compreh _) = throwErrSt "AST should not be built from Comprehension"
  buildASTExpr _ (UEmbeds _) = throwErrSt "AST should not be built from UnifyEmbeds"

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

instance (Eq t) => Eq (UnifyEmbeds t) where
  (==) u1 u2 = ueStruct u1 == ueStruct u2

getRefFromMutable :: Mutable t -> Maybe (Reference t)
getRefFromMutable mut = case mut of
  Ref ref -> Just ref
  _ -> Nothing

getSFuncFromMutable :: Mutable t -> Maybe (StatefulFunc t)
getSFuncFromMutable mut = case mut of
  SFunc s -> Just s
  _ -> Nothing

requireMutableConcrete :: StatefulFunc t -> Bool
requireMutableConcrete mut
  | RegularMutable <- sfnType mut = sfnName mut `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
requireMutableConcrete _ = False

getMutName :: Mutable t -> (t -> Maybe String) -> String
getMutName (SFunc mut) _ = sfnName mut
getMutName (Ref ref) f = showRefArg (refArg ref) f
getMutName (Compreh _) _ = "comprehend"
getMutName (UEmbeds _) _ = "embeds_unifier"

getMutVal :: Mutable t -> Maybe t
getMutVal (SFunc mut) = sfnValue mut
getMutVal (Ref ref) = refValue ref
getMutVal (Compreh c) = cphValue c
getMutVal (UEmbeds u) = ueValue u

setMutVal :: Maybe t -> Mutable t -> Mutable t
setMutVal m (SFunc mut) = SFunc $ mut{sfnValue = m}
setMutVal m (Ref ref) = Ref $ ref{refValue = m}
setMutVal m (Compreh c) = Compreh $ c{cphValue = m}
setMutVal m (UEmbeds u) = UEmbeds $ u{ueValue = m}

invokeMutMethod :: (MutableEnv s r t m) => StatefulFunc t -> m ()
invokeMutMethod mut = sfnMethod mut (sfnArgs mut)

modifyRegMut :: (StatefulFunc t -> StatefulFunc t) -> Mutable t -> Mutable t
modifyRegMut f (SFunc m) = SFunc $ f m
modifyRegMut _ r = r

emptySFunc :: StatefulFunc t
emptySFunc =
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
  (forall s r m. (MutableEnv s r t m) => t -> m ()) ->
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
  g :: (MutableEnv s r t m) => [t] -> m ()
  g [x] = f x
  g _ = throwErrSt "invalid number of arguments for unary function"

buildUnaryExpr :: (Env r m, BuildASTExpr t) => AST.UnaryOp -> t -> m AST.Expression
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
  (forall s r m. (MutableEnv s r t m) => t -> t -> m ()) ->
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
  g :: (MutableEnv s r t m) => [t] -> m ()
  g [x, y] = f x y
  g _ = throwErrSt "invalid number of arguments for binary function"

buildBinaryExpr :: (Env r e, BuildASTExpr t) => AST.BinaryOp -> t -> t -> e AST.Expression
buildBinaryExpr op l r = do
  let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
  xe <- buildASTExpr c l
  ye <- buildASTExpr c r
  return $ AST.ExprBinaryOp op xe ye

mkRefMutable :: String -> [t] -> Mutable t
mkRefMutable var ts =
  Ref $
    Reference
      { refArg = RefPath var ts
      , refOrigAddrs = Nothing
      , refValue = Nothing
      }

mkUnaryEmbeds :: forall t. (BuildASTExpr t) => t -> Mutable t
mkUnaryEmbeds t =
  UEmbeds $
    UnifyEmbeds
      { ueStruct = t
      , ueValue = Nothing
      }
