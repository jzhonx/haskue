{-# LANGUAGE FlexibleContexts #-}

module Eval where

import AST
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, get, runStateT)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import qualified Data.Set as Set
import Unify (unify)
import Value (Value (..))

data Selector = StringSelector String | IntSelector Int

type Path = [Selector]

-- Pending means that the value can not be evaluated because of unresolved dependencies.
-- the first argument is the value that is being evaluated.
data PendingValue = PendingValue ValueZipper [Path] ([Value] -> Value)

-- | ValueCrumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type ValueCrumb = (String, Value)

type ValueZipper = (Value, [ValueCrumb])

data Env = Env
  { getStruct :: ValueZipper,
    getPendings :: [PendingValue]
  }

goUp :: ValueZipper -> Maybe ValueZipper
goUp (_, []) = Nothing
goUp (_, (_, v') : vs) = Just (v', vs)

goTo :: String -> ValueZipper -> Maybe ValueZipper
goTo name (val@(Struct _ edges _), vs) = do
  val' <- Map.lookup name edges
  return (val', (name, val) : vs)
goTo _ (_, _) = Nothing

-- modify :: (Value -> Value) -> ValueZipper -> Maybe ValueZipper
-- modify f (v, vs) = Just (f v, vs)

searchUp :: String -> ValueZipper -> Maybe Value
searchUp name (Struct _ edges _, []) = Map.lookup name edges
searchUp _ (_, []) = Nothing
searchUp name z = do
  z' <- goUp z
  searchUp name z'

initEnv :: ValueZipper
initEnv = (Top, [])

eval :: (MonadError String m) => Expression -> m Value
eval expr = fst <$> runStateT (eval' expr) initEnv

eval' :: (MonadError String m, MonadState ValueZipper m) => Expression -> m Value
eval' (UnaryExprCons e) = evalUnaryExpr e
eval' (BinaryOpCons op e1 e2) = evalBinary op e1 e2

evalLiteral :: (MonadError String m, MonadState ValueZipper m) => Literal -> m Value
evalLiteral = f
  where
    f (StringLit (SimpleStringLit s)) = return $ String s
    f (IntLit i) = return $ Int i
    f (BoolLit b) = return $ Bool b
    f TopLit = return Top
    f BottomLit = return $ Bottom ""
    f NullLit = return Null
    f (StructLit s) = evalStructLit s

evalStructLit :: (MonadError String m, MonadState ValueZipper m) => [(Label, Expression)] -> m Value
evalStructLit s = do
  fields <- mapM evalField s
  let orderedKeys = map fst fields
  let (filteredKeys, _) =
        foldr
          (\k (l, set) -> if Set.notMember k set then (k : l, Set.insert k set) else (l, set))
          ([], Set.empty)
          orderedKeys
  unified' <- unifySameKeys fields
  return $ Struct filteredKeys unified' (Set.fromList (getVarLabels s))
  where
    evalField (Label (LabelName ln), e) =
      let name = case ln of
            LabelID ident -> ident
            LabelString ls -> ls
       in do
            v <- eval' e
            return (name, v)
    unifySameKeys :: (MonadError String m, MonadState ValueZipper m) => [(String, Value)] -> m (Map.Map String Value)
    unifySameKeys fields = sequence $ Map.fromListWith (\mx my -> do x <- mx; y <- my; unify x y) (map (\(k, v) -> (k, return v)) fields)

    fetchVarLabel :: Label -> Maybe String
    fetchVarLabel (Label (LabelName (LabelID var))) = Just var
    fetchVarLabel _ = Nothing

    getVarLabels :: [(Label, Expression)] -> [String]
    getVarLabels xs = map (\(l, _) -> fromJust (fetchVarLabel l)) (filter (\(l, _) -> isJust (fetchVarLabel l)) xs)

evalUnaryExpr :: (MonadError String m, MonadState ValueZipper m) => UnaryExpr -> m Value
evalUnaryExpr (PrimaryExprCons (Operand (Literal lit))) = evalLiteral lit
evalUnaryExpr (PrimaryExprCons (Operand (OpExpression expr))) = eval' expr
evalUnaryExpr (PrimaryExprCons (Operand (OperandName (Identifier ident)))) = lookupVar ident
evalUnaryExpr (UnaryOpCons op e) = evalUnaryOp op e

evalUnaryOp :: (MonadError String m, MonadState ValueZipper m) => UnaryOp -> UnaryExpr -> m Value
evalUnaryOp op e = do
  val <- evalUnaryExpr e
  case (op, val) of
    (Plus, Int i) -> return $ Int i
    (Minus, Int i) -> return $ Int (-i)
    (Not, Bool b) -> return $ Bool (not b)
    _ -> throwError "evalUnaryOp: not correct type"

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (MonadError String m, MonadState ValueZipper m) => BinaryOp -> Expression -> Expression -> m Value
evalBinary AST.Disjunction e1 e2 = evalDisjunction e1 e2
evalBinary op e1 e2 = do
  v1 <- eval' e1
  v2 <- eval' e2
  case (op, v1, v2) of
    (Unify, _, _) -> unify v1 v2
    (Add, Int i1, Int i2) -> return $ Int (i1 + i2)
    (Sub, Int i1, Int i2) -> return $ Int (i1 - i2)
    (Mul, Int i1, Int i2) -> return $ Int (i1 * i2)
    (Div, Int i1, Int i2) -> return $ Int (i1 `div` i2)
    _ -> throwError "evalBinary: not integers"

data DisjunctItem = DisjunctDefault Value | DisjunctRegular Value

-- evalDisjunction is used to evaluate a disjunction.
evalDisjunction :: (MonadError String m, MonadState ValueZipper m) => Expression -> Expression -> m Value
evalDisjunction e1 e2 = case (e1, e2) of
  (UnaryExprCons (UnaryOpCons Star e1'), UnaryExprCons (UnaryOpCons Star e2')) ->
    evalExprPair (evalUnaryExpr e1') DisjunctDefault (evalUnaryExpr e2') DisjunctDefault
  (UnaryExprCons (UnaryOpCons Star e1'), _) ->
    evalExprPair (evalUnaryExpr e1') DisjunctDefault (eval' e2) DisjunctRegular
  (_, UnaryExprCons (UnaryOpCons Star e2')) ->
    evalExprPair (eval' e1) DisjunctRegular (evalUnaryExpr e2') DisjunctDefault
  (_, _) -> evalExprPair (eval' e1) DisjunctRegular (eval' e2) DisjunctRegular
  where
    -- evalExprPair is used to evaluate a disjunction with both sides still being unevaluated.
    evalExprPair :: (MonadError String m, MonadState ValueZipper m) => m Value -> (Value -> DisjunctItem) -> m Value -> (Value -> DisjunctItem) -> m Value
    evalExprPair m1 cons1 m2 cons2 = do
      v1 <- m1
      v2 <- m2
      evalDisjPair (cons1 v1) (cons2 v2)

    -- evalDisjPair is used to evaluate a disjunction whose both sides are evaluated.
    evalDisjPair :: (MonadError String m, MonadState ValueZipper m) => DisjunctItem -> DisjunctItem -> m Value
    evalDisjPair (DisjunctDefault v1) r2 =
      evalLeftPartial (\(df1, ds1, df2, ds2) -> newDisj df1 ds1 df2 ds2) v1 r2
    -- reverse v2 r1 and also the order to the disjCons.
    evalDisjPair r1@(DisjunctRegular _) (DisjunctDefault v2) =
      evalLeftPartial (\(df2, ds2, df1, ds1) -> newDisj df1 ds1 df2 ds2) v2 r1
    evalDisjPair (DisjunctRegular v1) (DisjunctRegular v2) = evalRegularDisj v1 v2

    -- evalLeftPartial is used to evaluate a disjunction whose left side is a default.
    -- the first argument is a function that takes the four lists of values and returns a disjunction.
    evalLeftPartial :: (MonadError String m) => (([Value], [Value], [Value], [Value]) -> m Value) -> Value -> DisjunctItem -> m Value
    evalLeftPartial disjCons (Value.Disjunction df1 ds1) (DisjunctRegular (Value.Disjunction _ ds2)) =
      -- This is rule M2 and M3. We eliminate the defaults from the right side.
      disjCons (df1, ds1, [], ds2)
    evalLeftPartial disjCons v1 (DisjunctRegular (Value.Disjunction df2 ds2)) =
      -- This is rule M1.
      disjCons ([v1], [v1], df2, ds2)
    evalLeftPartial disjCons v1 (DisjunctRegular v2) =
      disjCons ([v1], [v1], [], [v2])
    evalLeftPartial disjCons v1 (DisjunctDefault v2) =
      disjCons ([], [v1], [], [v2])

    -- evalFullDisj is used to evaluate a disjunction whose both sides are regular.
    -- Rule: D1, D2
    evalRegularDisj (Value.Disjunction df1 ds1) (Value.Disjunction df2 ds2) = newDisj df1 ds1 df2 ds2
    evalRegularDisj (Value.Disjunction d ds) y = newDisj d ds [] [y]
    evalRegularDisj x (Value.Disjunction d ds) = newDisj [] [x] d ds
    -- Rule D0
    evalRegularDisj x y = newDisj [] [x] [] [y]

    -- dedupAppend appends unique elements in ys to the xs list, but only if they are not already in xs.
    -- xs and ys are guaranteed to be unique.
    dedupAppend :: [Value] -> [Value] -> [Value]
    dedupAppend xs ys = xs ++ foldr (\y acc -> if y `elem` xs then acc else y : acc) [] ys

    newDisj df1 ds1 df2 ds2 = return $ Value.Disjunction (dedupAppend df1 df2) (dedupAppend ds1 ds2)

lookupVar :: (MonadError String m, MonadState ValueZipper m) => String -> m Value
lookupVar name = do
  z <- get
  case searchUp name z of
    Just v -> return v
    Nothing -> throwError $ "variable " ++ name ++ " is not defined"
