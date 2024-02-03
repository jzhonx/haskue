{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Eval where

import AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, get, modify, put, runStateT)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import qualified Data.Set as Set
import Debug.Trace
import Parser (parseCUE)
import Path
import Text.Printf (printf)
import Transform (transform)
import Unify (unify)
import Value

initState :: Context
initState = Context (emptyStruct, []) Map.empty

run :: String -> Either String Value
run s = do
  parsedE <- parseCUE s
  eval (transform parsedE) emptyPath

eval :: (MonadError String m) => Expression -> Path -> m Value
eval expr path = fst <$> runStateT (doEval expr path) initState

doEval :: (MonadError String m, MonadState Context m) => Expression -> Path -> m Value
doEval (ExprUnaryExpr e) = evalUnaryExpr e
doEval (ExprBinaryOp op e1 e2) = evalBinary op e1 e2

evalLiteral :: (MonadError String m, MonadState Context m) => Literal -> Path -> m Value
evalLiteral = f
  where
    f :: (MonadError String m, MonadState Context m) => Literal -> Path -> m Value
    f (StringLit (SimpleStringLit s)) _ = return $ String s
    f (IntLit i) _ = return $ Int i
    f (BoolLit b) _ = return $ Bool b
    f TopLit _ = return Top
    f BottomLit _ = return $ Bottom ""
    f NullLit _ = return Null
    f (StructLit s) path = evalStructLit s path

-- | The struct is guaranteed to have unique labels by transform.
evalStructLit :: (MonadError String m, MonadState Context m) => [(Label, Expression)] -> Path -> m Value
evalStructLit lit path =
  let labels = map evalLabel lit
      fieldsStub = foldr (\k acc -> Map.insert k (mkUnevaluated (appendSel (Path.StringSelector k) path)) acc) Map.empty labels
      idSet = Set.fromList (getVarLabels lit)
      structStub = StructValue labels fieldsStub idSet Set.empty
   in do
        trace (printf "new struct, path: %s" (show path)) pure ()
        -- create a new block since we are entering a new struct.
        putValueInCtx path (Struct structStub)
        bm <- foldM evalField Nothing (zipWith (\name (_, e) -> (name, e)) labels lit)
        case bm of
          Just b -> return b
          Nothing -> getValueFromCtx path
  where
    evalLabel (Label (LabelName ln), _) = case ln of
      LabelID ident -> ident
      LabelString ls -> ls

    -- evalField evaluates a field in a struct. It returns whether the evaluated value is Bottom.
    evalField :: (MonadError String m, MonadState Context m) => Maybe Value -> (String, Expression) -> m (Maybe Value)
    evalField acc (name, e) =
      let fieldPath = appendSel (Path.StringSelector name) path
       in if isJust acc
            then return acc
            else do
              v <- doEval e fieldPath
              putValueInCtx fieldPath v
              trace ("evalField: " ++ show fieldPath ++ ", " ++ show v) pure ()
              tryEvalPen (fieldPath, v)
              case v of
                Bottom {} -> return $ Just v
                _ -> return Nothing

    fetchVarLabel :: Label -> Maybe String
    fetchVarLabel (Label (LabelName (LabelID var))) = Just var
    fetchVarLabel _ = Nothing

    getVarLabels :: [(Label, Expression)] -> [String]
    getVarLabels xs = map (\(l, _) -> fromJust (fetchVarLabel l)) (filter (\(l, _) -> isJust (fetchVarLabel l)) xs)

evalUnaryExpr :: (MonadError String m, MonadState Context m) => UnaryExpr -> Path -> m Value
evalUnaryExpr (UnaryExprPrimaryExpr primExpr) = evalPrimExpr primExpr
evalUnaryExpr (UnaryExprUnaryOp op e) = evalUnaryOp op e

evalPrimExpr :: (MonadError String m, MonadState Context m) => PrimaryExpr -> Path -> m Value
evalPrimExpr (PrimExprOperand op) = case op of
  OpLiteral lit -> evalLiteral lit
  OpExpression expr -> doEval expr
  OperandName (Identifier ident) -> lookupVar ident
evalPrimExpr (PrimExprSelector primExpr sel) = \path -> do
  val <- evalPrimExpr primExpr path
  evalSelector sel val path

evalSelector :: (MonadError String m, MonadState Context m) => AST.Selector -> Value -> Path -> m Value
evalSelector sel val path = case sel of
  IDSelector ident -> evalF ident
  AST.StringSelector str -> evalF str
  where
    evalF s = case val of
      pendV@(Pending {}) -> unaFunc (dot s path) pendV
      _ -> dot s path val

evalUnaryOp :: (MonadError String m, MonadState Context m) => UnaryOp -> UnaryExpr -> Path -> m Value
evalUnaryOp op e path = do
  val <- evalUnaryExpr e path
  f val
  where
    f v@(Pending {}) = unaFunc (conEval op) v
    f v = conEval op v
    -- conEval evaluates non-pending operands.
    conEval :: (MonadError String m, MonadState Context m) => UnaryOp -> Value -> m Value
    conEval Plus (Int i) = return $ Int i
    conEval Minus (Int i) = return $ Int (-i)
    conEval Not (Bool b) = return $ Bool (not b)
    conEval _ _ = throwError "conEval: unsupported unary operator"

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (MonadError String m, MonadState Context m) => BinaryOp -> Expression -> Expression -> Path -> m Value
evalBinary AST.Disjunction e1 e2 path = evalDisjunction e1 e2 path
evalBinary op e1 e2 path = do
  v1 <- doEval e1 path
  v2 <- doEval e2 path
  trace (printf "eval binary (%s %s %s)" (show v1) (show op) (show v2)) pure ()
  binOp v1 v2
  where
    intf :: (MonadError String m, MonadState Context m) => (Integer -> Integer -> Integer) -> Value -> Value -> m Value
    intf f = binFunc g
      where
        g :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
        g (Int i1) (Int i2) = do
          trace (printf "exec (%s %s %s)" (show i1) (show op) (show i2)) pure ()
          return $ Int (f i1 i2)
        g Top (Int _) = return Top
        g (Int _) Top = return Top
        g v1 v2 = throwError $ "intf: unsupported binary operator for values: " ++ show v1 ++ ", " ++ show v2

    binOp :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
    binOp
      | op == Unify = binFunc unify
      | op == Add = intf (+)
      | op == Sub = intf (-)
      | op == Mul = intf (*)
      | op == Div = intf div
      | otherwise = \_ _ -> throwError $ "binOp: unsupported binary operator: " ++ show op

data DisjunctItem = DisjunctDefault Value | DisjunctRegular Value

-- evalDisjunction is used to evaluate a disjunction.
evalDisjunction :: (MonadError String m, MonadState Context m) => Expression -> Expression -> Path -> m Value
evalDisjunction e1 e2 path = case (e1, e2) of
  (ExprUnaryExpr (UnaryExprUnaryOp Star e1'), ExprUnaryExpr (UnaryExprUnaryOp Star e2')) ->
    evalExprPair (evalUnaryExpr e1' path) DisjunctDefault (evalUnaryExpr e2' path) DisjunctDefault
  (ExprUnaryExpr (UnaryExprUnaryOp Star e1'), _) ->
    evalExprPair (evalUnaryExpr e1' path) DisjunctDefault (doEval e2 path) DisjunctRegular
  (_, ExprUnaryExpr (UnaryExprUnaryOp Star e2')) ->
    evalExprPair (doEval e1 path) DisjunctRegular (evalUnaryExpr e2' path) DisjunctDefault
  (_, _) -> evalExprPair (doEval e1 path) DisjunctRegular (doEval e2 path) DisjunctRegular
  where
    -- evalExprPair is used to evaluate a disjunction with both sides still being unevaluated.
    evalExprPair :: (MonadError String m, MonadState Context m) => m Value -> (Value -> DisjunctItem) -> m Value -> (Value -> DisjunctItem) -> m Value
    evalExprPair m1 cons1 m2 cons2 = do
      v1 <- m1
      v2 <- m2
      evalDisjPair (cons1 v1) (cons2 v2)

    -- evalDisjPair is used to evaluate a disjunction whose both sides are evaluated.
    evalDisjPair :: (MonadError String m, MonadState Context m) => DisjunctItem -> DisjunctItem -> m Value
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
