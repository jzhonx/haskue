{-# LANGUAGE FlexibleContexts #-}

module Eval where

import AST
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, get, modify, put, runStateT)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import qualified Data.Set as Set
import Debug.Trace
import Unify (unify)
import Value

data EvalState = EvalState
  { -- path is the path to the current expression.
    -- the path should be the full path.
    path :: Path,
    -- curBlock is the current block that contains the variables.
    -- A new block will replace the current one when a new block is entered.
    -- A new block is entered when one of the following is encountered:
    -- - The "{" token
    -- - for and let clauses
    curBlockZ :: Zipper
  }

initEnv :: EvalState
initEnv = EvalState [] (Top, [])

eval :: (MonadError String m) => Expression -> m Value
eval expr = fst <$> runStateT (eval' expr) initEnv

eval' :: (MonadError String m, MonadState EvalState m) => Expression -> m Value
eval' (UnaryExprCons e) = evalUnaryExpr e
eval' (BinaryOpCons op e1 e2) = evalBinary op e1 e2

evalLiteral :: (MonadError String m, MonadState EvalState m) => Literal -> m Value
evalLiteral = f
  where
    f (StringLit (SimpleStringLit s)) = return $ String s
    f (IntLit i) = return $ Int i
    f (BoolLit b) = return $ Bool b
    f TopLit = return Top
    f BottomLit = return $ Bottom ""
    f NullLit = return Null
    f (StructLit s) = evalStructLit s

evalStructLit :: (MonadError String m, MonadState EvalState m) => [(Label, Expression)] -> m Value
evalStructLit s =
  let orderedKeys = map evalLabel s
      (filteredKeys, _) =
        foldr
          (\k (l, set) -> if Set.notMember k set then (k : l, Set.insert k set) else (l, set))
          ([], Set.empty)
          orderedKeys
      emptyStructValue = Struct [] (Map.fromList (map (\k -> (k, Unevaluated)) filteredKeys)) Set.empty
      identifiers' = Set.fromList (getVarLabels s)
   in do
        estate@(EvalState path' cblock) <- get
        let newBlock = addSubZipper (last path') emptyStructValue cblock
        put $ estate {curBlockZ = newBlock}

        fields' <- mapM evalField (zipWith (\name (_, e) -> (name, e)) orderedKeys s)
        evaled <- unifySameKeys fields' >>= evalPendings

        let newStruct = Struct filteredKeys evaled identifiers'
        -- restore the current block.
        put $ estate {curBlockZ = attach newStruct cblock}
        return newStruct
  where
    evalLabel (Label (LabelName ln), _) =
      let name = case ln of
            LabelID ident -> ident
            LabelString ls -> ls
       in name

    evalField (name, e) = do
      -- push the current field to the path.
      modify (\estate -> estate {path = path estate ++ [StringSelector name]})
      v <- eval' e
      -- pop the current field from the path.
      modify (\estate -> estate {path = init (path estate)})
      return (name, v)

    unifySameKeys :: (MonadError String m, MonadState EvalState m) => [(String, Value)] -> m (Map.Map String Value)
    unifySameKeys fields' = sequence $ Map.fromListWith (\mx my -> do x <- mx; y <- my; unify x y) (map (\(k, v) -> (k, return v)) fields')

    fetchVarLabel :: Label -> Maybe String
    fetchVarLabel (Label (LabelName (LabelID var))) = Just var
    fetchVarLabel _ = Nothing

    getVarLabels :: [(Label, Expression)] -> [String]
    getVarLabels xs = map (\(l, _) -> fromJust (fetchVarLabel l)) (filter (\(l, _) -> isJust (fetchVarLabel l)) xs)

    evalPending mx k (Pending [x] evlt) = do
      EvalState path' _ <- get
      case relPath x path' of
        [] -> throwError "evalPending: empty path"
        [StringSelector name] -> case Map.lookup name mx of
          Just v -> return $ evlt [v]
          Nothing -> throwError "evalPending: not found"
        _ -> throwError $ "evalPending: TODO" ++ show x ++ ", path: " ++ show path'
    evalPending _ _ (Pending _ _) = throwError "evalPending: TODO"
    evalPending _ _ v = return v

    -- TODO:
    evalPendings :: (MonadError String m, MonadState EvalState m) => Map.Map String Value -> m (Map.Map String Value)
    evalPendings mx = sequence $ Map.mapWithKey (evalPending mx) mx

evalUnaryExpr :: (MonadError String m, MonadState EvalState m) => UnaryExpr -> m Value
evalUnaryExpr (PrimaryExprCons (Operand (Literal lit))) = evalLiteral lit
evalUnaryExpr (PrimaryExprCons (Operand (OpExpression expr))) = eval' expr
evalUnaryExpr (PrimaryExprCons (Operand (OperandName (Identifier ident)))) = lookupVar ident
evalUnaryExpr (UnaryOpCons op e) = evalUnaryOp op e

evalUnaryOp :: (MonadError String m, MonadState EvalState m) => UnaryOp -> UnaryExpr -> m Value
evalUnaryOp op e = do
  val <- evalUnaryExpr e
  f val
  where
    f (Pending d ef) = return $ Pending d (ce op . ef)
    f v = return $ ce op v
    -- ce is short for concrete evaluation.
    ce Plus (Int i) = Int i
    ce Minus (Int i) = Int (-i)
    ce Not (Bool b) = Bool (not b)
    ce _ _ = Bottom "evalUnaryOp: not correct type"

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (MonadError String m, MonadState EvalState m) => BinaryOp -> Expression -> Expression -> m Value
evalBinary AST.Disjunction e1 e2 = evalDisjunction e1 e2
evalBinary op e1 e2 = do
  v1 <- eval' e1
  v2 <- eval' e2
  f v1 v2
  where
    f v1 v2
      | op == Unify = unify v1 v2
      | op == Add = return $ h (+) v1 v2
      | op == Sub = return $ h (-) v1 v2
      | op == Mul = return $ h (*) v1 v2
      | op == Div = return $ h div v1 v2
      | otherwise = throwError "evalBinary: unsupported binary operator"

    h bin (Int l) (Int r) = Int $ bin l r
    h bin li@(Int _) (Pending d ef) = Pending d (\xs -> h bin li (ef xs))
    h bin (Pending d ef) ri@(Int _) = Pending d (\xs -> h bin (ef xs) ri)
    h bin (Pending d1 ef1) (Pending d2 ef2) =
      Pending (mergePaths d1 d2) (\xs -> h bin (ef1 xs) (ef2 xs))
    h _ _ _ = Bottom "evalBinary: not of type Int"

data DisjunctItem = DisjunctDefault Value | DisjunctRegular Value

-- evalDisjunction is used to evaluate a disjunction.
evalDisjunction :: (MonadError String m, MonadState EvalState m) => Expression -> Expression -> m Value
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
    evalExprPair :: (MonadError String m, MonadState EvalState m) => m Value -> (Value -> DisjunctItem) -> m Value -> (Value -> DisjunctItem) -> m Value
    evalExprPair m1 cons1 m2 cons2 = do
      v1 <- m1
      v2 <- m2
      evalDisjPair (cons1 v1) (cons2 v2)

    -- evalDisjPair is used to evaluate a disjunction whose both sides are evaluated.
    evalDisjPair :: (MonadError String m, MonadState EvalState m) => DisjunctItem -> DisjunctItem -> m Value
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

lookupVar :: (MonadError String m, MonadState EvalState m) => String -> m Value
lookupVar name = do
  EvalState path' block <- get
  case searchUp name block of
    Just Unevaluated -> return $ Pending [init path' ++ [StringSelector name]] head
    Just v -> return v
    Nothing -> throwError $ "lookupVar: " ++ name ++ " not found" ++ ", path: " ++ show path' ++ ", block: " ++ show block
