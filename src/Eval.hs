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

data EvalResult
  = PartialDefault Value
  | Complete Value

fromEvalResult :: EvalResult -> Value
fromEvalResult (PartialDefault _) = Bottom "marked value should be associated with a disjunction"
fromEvalResult (Complete v) = v

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
eval expr = fst <$> runStateT m initEnv
  where
    m = do
      r <- eval' expr
      return $ fromEvalResult r

eval' :: (MonadError String m, MonadState ValueZipper m) => Expression -> m EvalResult
eval' (UnaryExprCons e) = evalUnaryExpr e
eval' (BinaryOpCons op e1 e2) = evalBinary op e1 e2

evalLiteral :: (MonadError String m, MonadState ValueZipper m) => Literal -> m EvalResult
evalLiteral lit = fmap Complete (f lit)
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
            return (name, fromEvalResult v)
    unifySameKeys :: (MonadError String m, MonadState ValueZipper m) => [(String, Value)] -> m (Map.Map String Value)
    unifySameKeys fields = sequence $ Map.fromListWith (\mx my -> do x <- mx; y <- my; unify x y) (map (\(k, v) -> (k, return v)) fields)

    fetchVarLabel :: Label -> Maybe String
    fetchVarLabel (Label (LabelName (LabelID var))) = Just var
    fetchVarLabel _ = Nothing

    getVarLabels :: [(Label, Expression)] -> [String]
    getVarLabels xs = map (\(l, _) -> fromJust (fetchVarLabel l)) (filter (\(l, _) -> isJust (fetchVarLabel l)) xs)

evalUnaryExpr :: (MonadError String m, MonadState ValueZipper m) => UnaryExpr -> m EvalResult
evalUnaryExpr (PrimaryExprCons (Operand (Literal lit))) = evalLiteral lit
evalUnaryExpr (PrimaryExprCons (Operand (OpExpression expr))) = eval' expr
evalUnaryExpr (PrimaryExprCons (Operand (OperandName (Identifier ident)))) = lookupVar ident
evalUnaryExpr (UnaryOpCons op e) = evalUnaryOp op e

evalUnaryOp :: (MonadError String m, MonadState ValueZipper m) => UnaryOp -> UnaryExpr -> m EvalResult
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
        _ -> throwError "evalUnaryOp: not correct type"

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (MonadError String m, MonadState ValueZipper m) => BinaryOp -> Expression -> Expression -> m EvalResult
evalBinary op e1 e2 = do
  r1 <- eval' e1
  r2 <- eval' e2
  evalRes op r1 r2
  where
    evalRes AST.Disjunction r1 r2 = evalDisjunction r1 r2
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

evalDisjunction :: (MonadError String m, MonadState ValueZipper m) => EvalResult -> EvalResult -> m EvalResult
evalDisjunction = f
  where
    f (PartialDefault v1) r2 =
      evalLeftPartial (\(df1, ds1, df2, ds2) -> newDisj df1 ds1 df2 ds2) v1 r2
    -- reverse v2 r1 and also the order to the disjCons.
    f r1@(Complete _) (PartialDefault v2) =
      evalLeftPartial (\(df2, ds2, df1, ds1) -> newDisj df1 ds1 df2 ds2) v2 r1
    f (Complete v1) (Complete v2) = evalFullDisj v1 v2

    -- evalLeftPartial is used to evaluate a disjunction whose left side is a partial default.
    evalLeftPartial :: (MonadError String m) => (([Value], [Value], [Value], [Value]) -> m EvalResult) -> Value -> EvalResult -> m EvalResult
    evalLeftPartial disjCons (Value.Disjunction df1 ds1) (Complete (Value.Disjunction _ ds2)) =
      -- This is rule M2 and M3. We eliminate the defaults from the right side.
      disjCons (df1, ds1, [], ds2)
    evalLeftPartial disjCons v1 (Complete (Value.Disjunction df2 ds2)) =
      -- This is rule M1.
      disjCons ([v1], [v1], df2, ds2)
    evalLeftPartial disjCons v1 (Complete v2) =
      disjCons ([v1], [v1], [], [v2])
    evalLeftPartial disjCons v1 (PartialDefault v2) =
      disjCons ([], [v1], [], [v2])

    -- Rule: D1, D2
    evalFullDisj (Value.Disjunction df1 ds1) (Value.Disjunction df2 ds2) = newDisj df1 ds1 df2 ds2
    evalFullDisj (Value.Disjunction d ds) y = newDisj d ds [] [y]
    evalFullDisj x (Value.Disjunction d ds) = newDisj [] [x] d ds
    -- Rule D0
    evalFullDisj x y = newDisj [] [x] [] [y]

    -- dedupAppend appends unique elements in ys to the xs list, but only if they are not already in xs.
    -- xs and ys are guaranteed to be unique.
    dedupAppend :: [Value] -> [Value] -> [Value]
    dedupAppend xs ys = xs ++ foldr (\y acc -> if y `elem` xs then acc else y : acc) [] ys

    newDisj df1 ds1 df2 ds2 = return $ Complete $ Value.Disjunction (dedupAppend df1 df2) (dedupAppend ds1 ds2)

lookupVar :: (MonadError String m, MonadState ValueZipper m) => String -> m EvalResult
lookupVar name = do
  z <- get
  case searchUp name z of
    Just v -> return $ Complete v
    Nothing -> throwError $ "variable " ++ name ++ " is not defined"
