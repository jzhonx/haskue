{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Mutable where

import qualified AST
import Common (BuildASTExpr (..), Env)
import Exception (throwErrSt)
import Value.Comprehension
import Value.DisjoinOp
import Value.Reference
import Value.UnifyOp

-- | Mutable is a tree node whose value can be changed.
data Mutable t
  = RegOp (RegularOp t)
  | Ref (Reference t)
  | Compreh (Comprehension t)
  | DisjOp (DisjoinOp t)
  | UOp (UnifyOp t)

instance (Eq t) => Eq (Mutable t) where
  (==) (RegOp m1) (RegOp m2) = m1 == m2
  (==) (Ref r1) (Ref r2) = r1 == r2
  (==) (Compreh c1) (Compreh c2) = c1 == c2
  (==) (DisjOp d1) (DisjOp d2) = d1 == d2
  (==) (UOp u1) (UOp u2) = u1 == u2
  (==) _ _ = False

instance (BuildASTExpr t) => BuildASTExpr (Mutable t) where
  buildASTExpr c (RegOp m) = buildASTExpr c m
  buildASTExpr _ (Ref _) = throwErrSt "AST should not be built from Reference"
  buildASTExpr _ (Compreh _) = throwErrSt "AST should not be built from Comprehension"
  buildASTExpr _ (DisjOp _) = throwErrSt "AST should not be built from DisjoinOp"
  buildASTExpr c (UOp u) = buildASTExpr c u

data OpType
  = UnaryOpType AST.UnaryOp
  | BinOpType AST.BinaryOp
  | CloseFunc
  | InvalidOpType

-- | RegularOp is a tree node that represents a function.
data RegularOp t = RegularOp
  { ropName :: String
  , ropOpType :: OpType
  , ropArgs :: [t]
  -- ^ Args stores the arguments that may or may not need to be evaluated.
  , ropExpr :: forall r s m. (Env r s m) => m AST.Expression
  -- ^ ropExpr is needed when the Mutable is created dynamically, for example, dynamically creating a same field
  -- in a struct, {a: string, f: "a", (f): "b"}. In this case, no original expression for the expr, string & "b", is
  -- available.
  -- The return value of the method should be stored in the tree.
  , ropValue :: Maybe t
  -- ^ ropValue stores the non-atom, non-Mutable (isTreeValue true) value.
  }

instance (Eq t) => Eq (RegularOp t) where
  (==) f1 f2 = ropName f1 == ropName f2 && ropArgs f1 == ropArgs f2

instance (BuildASTExpr t) => BuildASTExpr (RegularOp t) where
  buildASTExpr c mut = do
    if c || requireMutableConcrete mut
      -- If the expression must be concrete, but due to incomplete evaluation, we need to use original expression.
      then ropExpr mut
      else maybe (ropExpr mut) (buildASTExpr c) (ropValue mut)

getRefFromMutable :: Mutable t -> Maybe (Reference t)
getRefFromMutable mut = case mut of
  Ref ref -> Just ref
  _ -> Nothing

getSFuncFromMutable :: Mutable t -> Maybe (RegularOp t)
getSFuncFromMutable mut = case mut of
  RegOp s -> Just s
  _ -> Nothing

requireMutableConcrete :: RegularOp t -> Bool
requireMutableConcrete mut = ropName mut `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]

getMutName :: Mutable t -> (t -> Maybe String) -> String
getMutName (RegOp mut) _ = ropName mut
getMutName (Ref ref) f = "ref_" ++ showRefArg (refArg ref) f
getMutName (Compreh _) _ = "comprehend"
getMutName (DisjOp _) _ = "disjoin"
getMutName (UOp _) _ = "unify"

getMutVal :: Mutable t -> Maybe t
getMutVal (RegOp mut) = ropValue mut
getMutVal (Ref ref) = refValue ref
getMutVal (Compreh c) = cphValue c
getMutVal (DisjOp d) = djoValue d
getMutVal (UOp u) = ufValue u

setMutVal :: Maybe t -> Mutable t -> Mutable t
setMutVal m (RegOp mut) = RegOp $ mut{ropValue = m}
setMutVal m (Ref ref) = Ref $ ref{refValue = m}
setMutVal m (Compreh c) = Compreh $ c{cphValue = m}
setMutVal m (DisjOp d) = DisjOp $ d{djoValue = m}
setMutVal m (UOp u) = UOp $ u{ufValue = m}

getMutArgs :: Mutable t -> [t]
getMutArgs (RegOp rop) = ropArgs rop
getMutArgs (Ref ref) = subRefArgs $ refArg ref
getMutArgs (Compreh _) = []
getMutArgs (DisjOp d) = map dstValue (djoTerms d)
getMutArgs (UOp u) = ufConjuncts u

modifyRegMut :: (RegularOp t -> RegularOp t) -> Mutable t -> Mutable t
modifyRegMut f (RegOp m) = RegOp $ f m
modifyRegMut _ r = r

emptyRegularOp :: RegularOp t
emptyRegularOp =
  RegularOp
    { ropName = ""
    , ropOpType = InvalidOpType
    , ropArgs = []
    , ropExpr = throwErrSt "stub mutable"
    , ropValue = Nothing
    }

mkUnaryOp ::
  forall t. (BuildASTExpr t) => AST.UnaryOp -> t -> Mutable t
mkUnaryOp op n =
  RegOp $
    RegularOp
      { ropExpr = buildUnaryExpr op n
      , ropName = show op
      , ropOpType = UnaryOpType op
      , ropArgs = [n]
      , ropValue = Nothing
      }

buildUnaryExpr :: (Env r s m, BuildASTExpr t) => AST.UnaryOp -> t -> m AST.Expression
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
  forall t. (BuildASTExpr t) => AST.BinaryOp -> t -> t -> Mutable t
mkBinaryOp op l r =
  RegOp $
    RegularOp
      { ropExpr = buildBinaryExpr op l r
      , ropName = show op
      , ropOpType = BinOpType op
      , ropArgs = [l, r]
      , ropValue = Nothing
      }

buildBinaryExpr :: (Env r s m, BuildASTExpr t) => AST.BinaryOp -> t -> t -> m AST.Expression
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

mkDisjoinOp :: [DisjTerm t] -> Mutable t
mkDisjoinOp ts = DisjOp $ DisjoinOp{djoTerms = ts, djoValue = Nothing}

mkUnifyOp :: [t] -> Mutable t
mkUnifyOp ts = UOp $ emptyUnifyOp{ufConjuncts = ts}

buildArgsExpr :: (Env r s m, BuildASTExpr t) => String -> [t] -> m AST.Expression
buildArgsExpr func ts = do
  ets <- mapM (buildASTExpr False) ts
  return $
    AST.ExprUnaryExpr $
      AST.UnaryExprPrimaryExpr $
        AST.PrimExprArguments (AST.PrimExprOperand $ AST.OpLiteral $ AST.StringLit $ AST.SimpleStringLit func) ets