{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Eval
  ( run,
    eval,
    tryEvalPen,
    applyPen,
    bindBinary,
  )
where

import AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, get, gets, modify, runStateT)
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
      fieldsStub =
        foldr
          ( \(k, e) acc ->
              Map.insert
                k
                ( mkUnevaluated (appendSel (Path.StringSelector k) path) e
                )
                acc
          )
          Map.empty
          (map (\x -> (evalLabel x, snd x)) lit)
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
evalUnaryExpr (UnaryExprPrimaryExpr primExpr) = \path -> evalPrimExpr primExpr path >>= pure . snd
evalUnaryExpr (UnaryExprUnaryOp op e) = evalUnaryOp op e

evalPrimExpr :: (MonadError String m, MonadState Context m) => PrimaryExpr -> Path -> m (Path, Value)
evalPrimExpr (PrimExprOperand op) path = case op of
  OpLiteral lit -> (path,) <$> evalLiteral lit path
  OpExpression expr -> (path,) <$> doEval expr path
  OperandName (Identifier ident) -> lookupVar ident path
evalPrimExpr e@(PrimExprSelector primExpr sel) path = do
  valPair <- evalPrimExpr primExpr path
  res <- evalSelector e sel valPair path
  return (path, res)

-- | Looks up the variable denoted by the name in the current scope or the parent scopes.
-- If the variable is not concrete, a new pending value is created and returned. The reason is that if the referenced
-- var was given a value, the pending value should be updated with the value.
-- Parameters:
--   var denotes the variable name.
--   exprPath is the path to the current expression that contains the selector.
-- For example,
--  { a: b: x+y }
-- If the name is "y", and the exprPath is "a.b".
lookupVar :: (MonadError String m, MonadState Context m) => String -> Path -> m (Path, Value)
lookupVar var exprPath = do
  ctx <- get
  let scope = case goToScope (ctxCurBlock ctx) exprPath of
        Just b -> b
        Nothing -> ctxCurBlock ctx
  case searchUpVar var scope of
    Just (valPath, v) -> getVarPair scope valPath v
    Nothing ->
      throwError $
        printf "variable %s is not found, path: %s, scope: %s" var (show exprPath) (show scope)
  where
    getVarPair :: (MonadError String m, MonadState Context m) => TreeCursor -> Path -> Value -> m (Path, Value)
    getVarPair scope valPath v
      | isValueConcrete v = do
          trace (printf "lookupVar found var %s, scope: %s, value: %s" (show var) (show scope) (show v)) pure ()
          return (valPath, v)
    -- valPath is only a placeholder here.
    getVarPair _ valPath (Pending v) = (valPath,) <$> depend (exprPath, AST.idCons var) v
    -- This is the case when the value is not concrete, and it is not pending.
    -- valPath is only a placeholder here.
    getVarPair _ valPath _ = return (valPath, mkPending (AST.idCons var) exprPath valPath)

evalSelector ::
  (MonadError String m, MonadState Context m) =>
  PrimaryExpr ->
  AST.Selector ->
  (Path, Value) ->
  Path ->
  m Value
evalSelector pe sel valPair@(_, val) path = case sel of
  IDSelector ident -> f ident
  AST.StringSelector str -> f str
  where
    expr = ExprUnaryExpr (UnaryExprPrimaryExpr pe)
    f s = case val of
      pendV@(Pending {}) -> bindUnary (\nv -> dot (path, expr) (path, nv) s) (\_ -> Just expr) pendV
      _ -> dot (path, expr) valPair s

-- | Access the named field of the struct.
-- Parameters:
--   field is the name of the field.
--   path is the path to the current expression that contains the selector.
--   value is the struct value.
dot :: (MonadError String m, MonadState Context m) => (Path, AST.Expression) -> (Path, Value) -> String -> m Value
dot (path, expr) (structPath, structVal) field = case structVal of
  -- Default disjunction case.
  Value.Disjunction [x] _ -> lookupStructField x
  _ -> lookupStructField structVal
  where
    lookupStructField (Struct sv) = case Map.lookup field (svFields sv) of
      Just v -> getField v
      -- The "incomplete" selector case.
      Nothing -> return $ mkPending expr path (appendSel (Path.StringSelector field) structPath)
    lookupStructField _ =
      return $
        Bottom $
          printf
            "dot: path: %s, sel: %s, value: %s is not a struct"
            (show path)
            (show field)
            (show structVal)

    getField :: (MonadError String m, MonadState Context m) => Value -> m Value
    -- The referenced value could be a pending value. Once the pending value is evaluated, the selector should be
    -- populated with the value.
    getField (Pending v) = depend (path, idCons field) v
    getField v@(Struct _) = return v
    getField v
      | isValueConcrete v = return v
    -- The value is incomplete, so we create a new pending value.
    getField v =
      let newPath = appendSel (Path.StringSelector field) path
       in do
            trace
              ( printf
                  "dot: path: %s, sel: %s, value %s is not concrete"
                  (show newPath)
                  (show field)
                  (show v)
              )
              pure
              ()
            return $ mkPending expr path newPath

evalUnaryOp :: (MonadError String m, MonadState Context m) => UnaryOp -> UnaryExpr -> Path -> m Value
evalUnaryOp op e path = do
  val <- evalUnaryExpr e path
  evalUnary op val
  where
    evalUnary :: (MonadError String m, MonadState Context m) => UnaryOp -> Value -> m Value
    evalUnary _ v@(Pending {}) = bindUnary (evalUnary op) (unaryOpCons op) v
    evalUnary _ v
      | not $ isValueConcrete v =
          return $
            Bottom $
              printf
                "%s cannot be used for %s"
                (show op)
                (show v)
    evalUnary Plus (Int i) = return $ Int i
    evalUnary Minus (Int i) = return $ Int (-i)
    evalUnary Not (Bool b) = return $ Bool (not b)
    evalUnary _ v = throwError $ printf "%s is cannot be used for value %s" (show op) (show v)

-- | Bind a pending value to a function.
-- The first argument is the function that takes the value and returns a value.
bindUnary ::
  (MonadError String m, MonadState Context m) =>
  (Value -> EvalMonad Value) ->
  (AST.Expression -> Maybe AST.Expression) ->
  Value ->
  m Value
bindUnary f exprF (Pending v) = case v of
  pv@(PendingValue {}) -> do
    expr <- transExpr exprF (pvExpr pv)
    return $ Pending $ pv {pvEvaluator = bindEval (pvEvaluator pv) f, pvExpr = expr}
  cb@(CycleBegin {}) -> do
    expr <- transExpr exprF (cbExpr cb)
    return $ mkPending expr (cbPath cb) (cbPath cb)
  _ -> throwError $ printf "bindUnary: value %s is not PendingValue or CycleBegin" (show v)
bindUnary _ _ v = throwError $ printf "bindUnary: value %s is not pending" (show v)

transExpr :: MonadError String m => (AST.Expression -> Maybe AST.Expression) -> AST.Expression -> m AST.Expression
transExpr f e = case f e of
  Just _e -> return _e
  Nothing -> throwError "bindUnary: exprF returns Nothing"

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (MonadError String m, MonadState Context m) => BinaryOp -> Expression -> Expression -> Path -> m Value
evalBinary AST.Disjunction e1 e2 path = evalDisjunction e1 e2 path
evalBinary op e1 e2 path = do
  v1 <- doEval e1 path
  v2 <- doEval e2 path
  trace (printf "eval binary (%s %s %s)" (show v1) (show op) (show v2)) pure ()
  evalBin v1 v2
  where
    addf :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
    addf (Int i1) (Int i2) = do
      trace (printf "exec (+ %s %s)" (show i1) (show i2)) pure ()
      return $ Int (i1 + i2)
    addf v1 v2 = throwError $ printf "values %s and %s cannot be used for +" (show v1) (show v2)

    minf :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
    minf (Int i1) (Int i2) = do
      trace (printf "exec (- %s %s)" (show i1) (show i2)) pure ()
      return $ Int (i1 - i2)
    minf v1 v2 = throwError $ printf "values %s and %s cannot be used for -" (show v1) (show v2)

    mulf :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
    mulf (Int i1) (Int i2) = do
      trace (printf "exec (* %s %s)" (show i1) (show i2)) pure ()
      return $ Int (i1 * i2)
    mulf v1 v2 = throwError $ printf "values %s and %s cannot be used for *" (show v1) (show v2)

    divf :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
    divf (Int i1) (Int i2) = do
      trace (printf "exec (/ %s %s)" (show i1) (show i2)) pure ()
      return $ Int (i1 `div` i2)
    divf v1 v2 = throwError $ printf "values %s and %s cannot be used for div" (show v1) (show v2)

    evalAtoms :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
    evalAtoms v1 v2 = case op of
      AST.Add -> addf v1 v2
      AST.Sub -> minf v1 v2
      AST.Mul -> mulf v1 v2
      AST.Div -> divf v1 v2
      _ -> throwError $ "unsupported binary operator: " ++ show op

    evalBin :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
    evalBin v1 v2
      | op == Unify = bindBinary unify v1 v2
      | isValuePending v1 && isValuePending v2 = bindBinary evalAtoms v1 v2
      | isValuePending v1 = bindUnary (`evalAtoms` v2) (binExpr op (Right v2)) v1
      | isValuePending v2 = bindUnary (evalAtoms v1) (binExpr op (Left v1)) v2
      | not $ isValueConcrete v1 || not (isValueConcrete v2) =
          return $ Bottom $ printf "%s cannot be supported for %s and %s" (show op) (show v1) (show v2)
      | otherwise = evalAtoms v1 v2

binExpr :: AST.BinaryOp -> Either Value Value -> AST.Expression -> Maybe AST.Expression
binExpr op (Left v) e2 = do
  e1 <- toExpr v
  return $ AST.binaryOpCons op e1 e2
binExpr op (Right v) e1 = do
  e2 <- toExpr v
  return $ AST.binaryOpCons op e1 e2

-- | Bind a pending value to a function.
bindBinary ::
  (MonadError String m, MonadState Context m) =>
  (Value -> Value -> EvalMonad Value) ->
  Value ->
  Value ->
  m Value
bindBinary bin (Pending (PendingValue p1 d1 a1 e1 ex1)) (Pending (PendingValue p2 d2 a2 e2 _))
  | p1 == p2 =
      return $
        Pending $
          PendingValue
            p1
            (mergePaths d1 d2)
            (mergeArgs a1 a2)
            ( \xs -> do
                v1 <- e1 xs
                v2 <- e2 xs
                bin v1 v2
            )
            -- TODO: use expr1 for now
            ex1
  | otherwise =
      throwError $
        printf "binFunc: two pending values have different paths, p1: %s, p2: %s" (show p1) (show p2)
bindBinary _ v1 v2 = throwError $ printf "bindBinary: value %s and %s are not both pending" (show v1) (show v2)

-- | Checks whether the given value is concrete to be applied to other dependents. If it can, then apply the value to
-- the pending value.
tryEvalPen ::
  (MonadError String m, MonadState Context m) => (Path, Value) -> m ()
tryEvalPen (path, Pending {}) = do
  trace (printf "tryEvalPen skip pending value, path: %s" (show path)) pure ()
  return ()
-- tryEvalPen (_, v)
--   -- If the value is not concrete, then we don't need to do anything.
--   | not $ isValueConcrete v = return ()
tryEvalPen (valPath, val) = do
  revDeps <- gets ctxReverseDeps
  case Map.lookup valPath revDeps of
    Nothing -> return ()
    Just penPath -> do
      penVal <- getValueFromCtx penPath
      trace
        ( printf
            "tryEvalPen pre: %s->%s, val: %s, penVal: %s"
            (show valPath)
            (show penPath)
            (show val)
            (show penVal)
        )
        pure
        ()
      newPenVal <- applyPen (penPath, penVal) (valPath, val)
      case newPenVal of
        Pending {} -> pure ()
        -- Once the pending value is evaluated, we should trigger the fillPen for other pending values that depend
        -- on this value.
        v -> tryEvalPen (penPath, v)
      -- update the pending block.
      putValueInCtx penPath newPenVal
      trace
        ( printf
            "tryEvalPen post: %s->%s, val: %s, penVal: %s, newPenVal: %s"
            (show valPath)
            (show penPath)
            (show val)
            (show penVal)
            (show newPenVal)
        )
        pure
        ()

-- | Apply value to the pending value. It returns the new updated value.
-- It keeps applying the value to the pending value until the pending value is evaluated.
applyPen :: (MonadError String m, MonadState Context m) => (Path, Value) -> (Path, Value) -> m Value
applyPen (penPath, penV@(Pending {})) pair = go penV pair
  where
    go :: (MonadError String m, MonadState Context m) => Value -> (Path, Value) -> m Value
    go (Pending pv@(PendingValue {})) (valPath, val) =
      let newDeps = filter (\(_, depPath) -> depPath /= valPath) (pvDeps pv)
          newArgs = ((valPath, val) : pvArgs pv)
       in do
            trace
              ( printf
                  "applyPen: %s->%s, args: %s, newDeps: %s"
                  (show valPath)
                  (show penPath)
                  (show newArgs)
                  (show newDeps)
              )
              pure
              ()
            if null newDeps
              then pvEvaluator pv newArgs >>= \v -> go v pair
              else return $ Pending $ pv {pvDeps = newDeps, pvArgs = newArgs}
    go v _ = return v
applyPen (_, v) _ = throwError $ printf "applyPen expects a pending value, but got %s" (show v)

-- | Creates a pending value that depends on another pending value. The expression will be used to create the new
-- pending value.
-- If there is a cycle, the CycleBegin is returned.
depend :: (MonadError String m, MonadState Context m) => (Path, AST.Expression) -> PendingValue -> m Value
depend (exprPath, expr) dstVal = case dstVal of
  uv@(Unevaluated {}) ->
    if uePath uv == exprPath
      then do
        trace (printf "depend self Cycle detected: path: %s" (show exprPath)) pure ()
        return $ mkCycleBegin exprPath expr
      else do
        trace (printf "depend unevaluated is %s" (show uv)) pure ()
        createDepVal (uePath uv)
  pv@(PendingValue {}) -> do
    trace (printf "depend pendingVal is %s" (show pv)) pure ()
    createDepVal (pvPath pv)
  _ -> throwError $ printf "depend: value %s is not a pending value" (show dstVal)
  where
    checkCycle :: (MonadError String m, MonadState Context m) => (Path, Path) -> m Bool
    checkCycle (src, dst) = do
      Context _ revDeps <- get
      -- we have to reverse the new edge because the graph is reversed.
      return $ depsHasCycle ((dst, src) : Map.toList revDeps)

    -- createDepVal creates a pending value that depends on the value of the depPath.
    createDepVal :: (MonadError String m, MonadState Context m) => Path -> m Value
    createDepVal depPath = do
      cycleDetected <- checkCycle (exprPath, depPath)
      if cycleDetected
        then do
          trace (printf "depend Cycle detected: %s->%s" (show exprPath) (show depPath)) pure ()
          let v = mkCycleBegin depPath expr
          trace (printf "created cycle begin: %s" (show v)) pure ()
          return v
        else do
          modify (\ctx -> ctx {ctxReverseDeps = Map.insert depPath exprPath (ctxReverseDeps ctx)})
          -- TODO: fix the expr
          let v = mkPending expr exprPath depPath
          trace (printf "created pending value: %s" (show v)) pure ()
          return v

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
