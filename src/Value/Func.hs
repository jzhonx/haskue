{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Func where

import qualified AST
import Control.Monad (unless)
import Control.Monad.Except (throwError)
import Path
import Text.Printf (printf)
import Util
import Value.Class
import Value.Env
import Value.TMonad

data Func t = Func
  { fncName :: String
  , fncType :: FuncType
  , -- Args stores the arguments that may or may not need to be evaluated.
    fncArgs :: [t]
  , fncExprGen :: forall m c. (Env m c) => m AST.Expression
  , -- Note that the return value of the function should be stored in the tree.
    fncFunc :: forall s m. (TMonad s m t) => [t] -> m Bool
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
      then fncExprGen fn
      else maybe (fncExprGen fn) (buildASTExpr c) (fncTempRes fn)

isFuncRef :: Func t -> Bool
isFuncRef fn = fncType fn == RefFunc

isFuncIndex :: Func t -> Bool
isFuncIndex fn = fncType fn == IndexFunc

requireFuncConcrete :: Func t -> Bool
requireFuncConcrete fn = case fncType fn of
  RegularFunc -> fncName fn `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
  _ -> False

mkStubFunc :: (forall s m. (TMonad s m t) => [t] -> m Bool) -> Func t
mkStubFunc f =
  Func
    { fncName = ""
    , fncType = RegularFunc
    , fncArgs = []
    , fncExprGen = return $ AST.litCons AST.BottomLit
    , fncFunc = f
    , fncTempRes = Nothing
    }

mkUnaryOp ::
  forall t. (BuildASTExpr t) => AST.UnaryOp -> (forall s m. (TMonad s m t) => t -> m Bool) -> t -> Func t
mkUnaryOp op f n =
  Func
    { fncFunc = g
    , fncType = RegularFunc
    , fncExprGen = gen
    , fncName = show op
    , fncArgs = [n]
    , fncTempRes = Nothing
    }
 where
  g :: (TMonad s m t) => [t] -> m Bool
  g [x] = f x
  g _ = throwError "invalid number of arguments for unary function"

  gen :: (Env m c) => m AST.Expression
  gen = buildUnaryExpr n

  buildUnaryExpr :: (Env m c) => t -> m AST.Expression
  buildUnaryExpr t = do
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
  forall t. (BuildASTExpr t) => AST.BinaryOp -> (forall s m. (TMonad s m t) => t -> t -> m Bool) -> t -> t -> Func t
mkBinaryOp op f l r =
  Func
    { fncFunc = g
    , fncType = case op of
        AST.Disjunction -> DisjFunc
        _ -> RegularFunc
    , fncExprGen = gen
    , fncName = show op
    , fncArgs = [l, r]
    , fncTempRes = Nothing
    }
 where
  g :: (TMonad s m t) => [t] -> m Bool
  g [x, y] = f x y
  g _ = throwError "invalid number of arguments for binary function"

  gen :: (Env e c) => e AST.Expression
  gen = do
    let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
    xe <- buildASTExpr c l
    ye <- buildASTExpr c r
    return $ AST.ExprBinaryOp op xe ye

mkBinaryOpDir ::
  forall t.
  (BuildASTExpr t) =>
  AST.BinaryOp ->
  (forall s m. (TMonad s m t) => t -> t -> m Bool) ->
  (BinOpDirect, t) ->
  (BinOpDirect, t) ->
  Func t
mkBinaryOpDir rep op (d1, t1) (_, t2) =
  case d1 of
    L -> mkBinaryOp rep op t1 t2
    R -> mkBinaryOp rep op t2 t1

{- | Call the function. It returns the result of the function.
 - This does not modify the tree, i.e. the function is not reduced.
 -
 - TODO: consider whether putting back the fn accidentally left the unwanted changes in Monad.
-}
callFunc :: (TMonad s m t, Show t) => (t -> Maybe (Func t)) -> (Func t -> t) -> m (Maybe t)
callFunc getFunc newFnTree = withTree $ \t -> case getFunc t of
  Just fn -> do
    let name = fncName fn
    withDebugInfo $ \path _ ->
      logDebugStr $ printf "callFunc: path: %s, function %s, tip:\n%s" (show path) (show name) (show t)

    -- modified is not equivalent to reducible. For example, if the unification generates a new struct, it is not
    -- enough to replace the function with the new struct.
    modified <- fncFunc fn (fncArgs fn)

    res <- getTMTree
    withDebugInfo $ \path _ ->
      logDebugStr $
        printf
          "callFunc: path: %s, function %s, modified: %s, result:\n%s"
          (show path)
          (show name)
          (show modified)
          (show res)

    if modified
      then case getFunc res of
        Just _ -> do
          -- recursively call the function until the result is not a function.
          -- the tip is already the res.
          callFunc getFunc newFnTree
        Nothing -> do
          -- we need to restore the original tree with the new function result.
          putTMTree (newFnTree $ fn{fncTempRes = Just res})
          return (Just res)
      else return Nothing
  Nothing -> throwError "callFunc: function not found"

-- Try to reduce the function by using the function result to replace the function node.
-- This should be called after the function is evaluated.
reduceFunc :: (TMonad s m t, Show t) => (t -> Maybe (Func t)) -> t -> (Func t -> t) -> m Bool
reduceFunc getFunc val newFuncTree = withTree $ \t -> case getFunc t of
  Just fn ->
    if isTreeFunc val
      -- If the function returns another function, then the function is not reducible.
      then putTMTree val >> return False
      else do
        let
          -- the original function can not have references.
          hasNoRef = not (treeHasRef (newFuncTree fn))
          reducible = isTreeAtom val || isTreeBottom val || isTreeCnstr val || isTreeRefCycle val || hasNoRef
        withDebugInfo $ \path _ ->
          logDebugStr $
            printf
              "reduceFunc: func %s, path: %s, is reducible: %s, hasNoRef: %s, args: %s"
              (show $ fncName fn)
              (show path)
              (show reducible)
              (show hasNoRef)
              (show $ fncArgs fn)
        if reducible
          then do
            putTMTree val
            path <- getTMAbsPath
            -- we need to delete receiver starting with the path, not only is the path. For example, if the function is
            -- index and the first argument is a reference, then the first argument dependency should also be deleted.
            delNotifRecvs path
          -- restore the original function
          else putTMTree . newFuncTree $ fn
        return reducible
  Nothing -> throwError "reduceFunc: function not found"
