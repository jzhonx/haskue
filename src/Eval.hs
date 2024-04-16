{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Eval
  ( runIO,
    eval,
    propagate,
    resolve,
  )
where

import AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (MonadLogger, runStderrLoggingT)
import Control.Monad.State (get, gets, modify, runStateT)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust, isNothing)
import qualified Data.Set as Set
import Parser (parseCUE)
import Path
import Text.Printf (printf)
import Transform (transform)
import Unify (unify)
import Value


initState :: Context
initState = Context [] (undefined, []) Map.empty

runIO :: (MonadIO m, MonadError String m) => String -> m Value
runIO s = runStderrLoggingT $ runStr s

runStr :: (MonadError String m, MonadLogger m) => String -> m Value
runStr s = do
  parsedE <- parseCUE s
  -- eval (transform parsedE) emptyPath
  eval parsedE emptyPath

eval :: (MonadError String m, MonadLogger m) => Expression -> Path -> m Value
eval expr path = fst <$> runStateT (doEval expr path) initState

doEval :: Runtime m => Expression -> Path -> m Value
doEval = evalExpr

evalExpr :: Runtime m => Expression -> Path -> m Value
evalExpr (ExprUnaryExpr e) = evalUnaryExpr e
evalExpr (ExprBinaryOp op e1 e2) = evalBinary op e1 e2

evalLiteral :: Runtime m => Literal -> Path -> m Value
evalLiteral = f
  where
    f :: Runtime m => Literal -> Path -> m Value
    f (StringLit (SimpleStringLit s)) _ = return $ String s
    f (IntLit i) _ = return $ Int i
    f (BoolLit b) _ = return $ Bool b
    f TopLit _ = return Top
    f BottomLit _ = return $ Bottom ""
    f NullLit _ = return Null
    f (StructLit s) path = evalStructLit s path

enterNewScope :: Runtime m => Path -> [String] -> m ()
enterNewScope path labels = do
  stack <- gets ctxScopeStack
  updated <- pushScope path (Set.fromList labels) stack
  modify $ \ctx -> ctx {ctxScopeStack = updated}

leaveScope :: Runtime m => m ()
leaveScope = do
  stack <- gets ctxScopeStack
  updated <- popScope stack
  modify $ \ctx -> ctx {ctxScopeStack = updated}

-- | The struct is guaranteed to have unique labels by transform.
evalStructLit :: Runtime m => [(Label, Expression)] -> Path -> m Value
evalStructLit lit path =
  let labels = map evalLabel lit
   in -- fieldsStub =
      --   foldr
      --     (\(k, _) acc -> Map.insert k Stub acc)
      --     Map.empty
      --     (map (\x -> (evalLabel x, snd x)) lit)
      -- idSet = Set.fromList (getVarLabels lit)
      -- structStub = StructValue labels fieldsStub idSet Set.empty
      do
        dump $ printf "new struct, path: %s" (show path)
        -- create a new block since we are entering a new struct.
        enterNewScope path labels
        bm <- foldM evalField Nothing (zipWith (\name (_, e) -> (name, e)) labels lit)
        v <- case bm of
          Just b -> return b
          -- Nothing -> fromJust <$> getValueFromCtx path
          Nothing -> undefined
        dump $ printf "new struct, path: %s, evaluated to %s" (show path) (show v)
        leaveScope
        return v
  where
    evalLabel (Label (LabelName ln), _) = case ln of
      LabelID ident -> ident
      LabelString ls -> ls

    -- evalField evaluates a field in a struct. It returns whether the evaluated value is Bottom.
    evalField :: Runtime m => Maybe Value -> (String, Expression) -> m (Maybe Value)
    evalField acc (name, e) =
      let fieldPath = appendSel (Path.StringSelector name) path
       in if isJust acc
            then return acc
            else do
              dump $ printf "evalField: path: %s, starts, expr: %s" (show fieldPath) (show e)
              v <- doEval e fieldPath
              dump $ printf "evalField: path: %s, evaluated, expr is evaluated to %s" (show fieldPath) (show v)
              storeValueInCtx fieldPath v
              -- The reason we need to propagate here, not after once a value is evaluated, is that the value could be
              -- part of a binary or unary operation.
              propagate (fieldPath, v)
              dump $ printf "evalField: path: %s, done" (show fieldPath)
              case v of
                Bottom {} -> return $ Just v
                _ -> return Nothing

-- fetchVarLabel :: Label -> Maybe String
-- fetchVarLabel (Label (LabelName (LabelID var))) = Just var
-- fetchVarLabel _ = Nothing
--
-- getVarLabels :: [(Label, Expression)] -> [String]
-- getVarLabels xs = map (\(l, _) -> fromJust (fetchVarLabel l)) (filter (\(l, _) -> isJust (fetchVarLabel l)) xs)

-- | Put the value in the context with the path. If there already exists a value with the same path, it will be unified.
storeValueInCtx :: (Runtime m) => Path -> Value -> m ()
storeValueInCtx path val = do
  -- mv <- getValueFromCtx path
  mv <- undefined
  case mv of
    Just v -> do
      dump $ printf "storeValueInCtx: path: %s, unify %s with %s" (show path) (show v) (show val)
      u <- unify v val
      return undefined
      -- putValueInCtx path u
    -- Nothing -> putValueInCtx path val
    Nothing -> undefined

evalUnaryExpr :: Runtime m => UnaryExpr -> Path -> m Value
evalUnaryExpr (UnaryExprPrimaryExpr primExpr) = \path -> evalPrimExpr primExpr path >>= pure . snd
evalUnaryExpr (UnaryExprUnaryOp op e) = evalUnaryOp op e

evalPrimExpr :: Runtime m => PrimaryExpr -> Path -> m (Path, Value)
evalPrimExpr (PrimExprOperand op) path = case op of
  OpLiteral lit -> (path,) <$> evalLiteral lit path
  OpExpression expr -> (path,) <$> doEval expr path
  OperandName (Identifier ident) -> lookupVar ident path
evalPrimExpr e@(PrimExprSelector primExpr sel) path = do
  valPair <- evalPrimExpr primExpr path
  res <- evalSelector e sel valPair path
  return (path, res)

-- | Looks up the variable denoted by the name in the current scope or the parent scopes.
-- If the variable is not atom, a new pending value is created and returned. The reason is that if the referenced
-- var was updated with a new value, the pending value should be updated with the value.
-- Parameters:
--   var denotes the variable name.
--   exprPath is the path to the current expression that contains the selector.
-- For example,
--  { a: b: x+y }
-- If the name is "y", and the exprPath is "a.b".
lookupVar :: Runtime m => String -> Path -> m (Path, Value)
lookupVar var exprPath = do
  dump $ printf "lookupVar: path: %s, looks up var: %s" (show exprPath) var
  stack <- gets ctxScopeStack
  case searchUpVar var stack of
    Nothing -> do
      throwError $ printf "variable %s is not found, path: %s" var (show exprPath)
    Just varPath -> do
      -- vm <- getValueFromCtx varPath
      vm <- undefined
      case vm of
        Nothing -> throwError $ printf "variable %s is not found, path: %s" var (show exprPath)
        Just varVal -> do
          res <- (varPath,) <$> mkRef (exprPath, AST.idCons var) (varPath, varVal)
          dump $ printf "lookupVar: path: %s, found var: %s, value: %s" (show exprPath) var (show res)
          return res

-- let scope = case goToScope (ctxCurBlock ctx) exprPath of
--       Just b -> b
--       Nothing -> ctxCurBlock ctx
-- case searchUpVar var scope of
--   -- varPath is only a placeholder here.
--   Just (varPath, varVal) -> do
--     res <- (varPath,) <$> mkRef (exprPath, AST.idCons var) (varPath, varVal)
--     dump $ printf "lookupVar: path: %s, found var: %s, value: %s" (show exprPath) var (show res)
--     return res
--   Nothing ->
--     throwError $
--       printf "variable %s is not found, path: %s, scope: %s" var (show exprPath) (show scope)

-- | Evaluates the selector.
-- Parameters:
--  pe is the primary expression.
--  sel is the selector.
--  soPair is the path and the value of struct like object.
--  path is the path to the current expression that contains the selector.
-- For example,
--  { a: b: x.y }
-- If the field is "y", and the exprPath is "a.b", expr is "x.y", the structPath is "x".
evalSelector ::
  Runtime m => PrimaryExpr -> AST.Selector -> (Path, Value) -> Path -> m Value
evalSelector pe sel (soPath, soVal) path = case sel of
  IDSelector ident -> select ident soVal
  AST.StringSelector str -> select str soVal
  where
    expr = ExprUnaryExpr (UnaryExprPrimaryExpr pe)
    --  Access the named field of the struct.
    -- Parameters:
    -- sPath is the path to the struct.
    -- sv is the struct value.
    -- For example,
    --  { a: b: x.y }
    -- If the field is "y", and the exprPath is "a.b", expr is "x.y", the structPath is "x".
    dot :: Runtime m => (Path, StructValue) -> String -> m Value
    dot (sPath, sv) field =
      let fieldPath = appendSel (Path.StringSelector field) sPath
          fieldVal = case Map.lookup field (svFields sv) of
            Just v -> v
            -- The incomplete selector case.
            Nothing -> Stub
       in do
            dump $
              printf "dot: path: %s, spath: %s, field: %s, fieldVal: %s" (show path) (show sPath) field (show fieldVal)
            mkRef (path, expr) (fieldPath, fieldVal)

    select :: Runtime m => String -> Value -> m Value
    -- {x: y, a: x, y: {}}, where y is stub and we are evaluating a.
    select field (Pending pv) =
      let temp = pvTemp pv
       in case temp of
            Stub -> do
              dump $ printf "evalSelector: %s is stub" (show soVal)
              delayUnaryOp expr (select field) pv
            _ -> select field temp
    select field (Struct sv) = dot (soPath, sv) field
    select field (Value.Disjunction [x] _) = select field x
    -- {a: x.c, x: {}}, where x is stub.
    select _ Stub = throwError $ printf "evalSelector: %s is stub" (show soVal)
    select _ _ = return . Bottom $ printf "%s is not a struct" (show soVal)

-- | Evaluates the unary operator.
-- unary operator should only be applied to atoms.
evalUnaryOp :: Runtime m => UnaryOp -> UnaryExpr -> Path -> m Value
evalUnaryOp op e path = do
  val <- evalUnaryExpr e path
  go op val
  where
    go :: Runtime m => UnaryOp -> Value -> m Value
    go _ (Pending pv) = delayUnaryOp (ExprUnaryExpr $ UnaryExprUnaryOp op e) (go op) pv
    go _ v
      | not $ isValueAtom v =
          return . Bottom $ printf "%s cannot be used for %s" (show op) (show v)
    go Plus (Int i) = return $ Int i
    go Minus (Int i) = return $ Int (-i)
    go Not (Bool b) = return $ Bool (not b)
    go _ v = throwError $ printf "%s cannot be used for value %s" (show op) (show v)

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: Runtime m => BinaryOp -> Expression -> Expression -> Path -> m Value
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjunction e1 e2 path = evalDisj e1 e2 path
evalBinary op e1 e2 path = do
  v1 <- doEval e1 path
  v2 <- doEval e2 path
  dump $ printf "eval binary (%s %s %s)" (show op) (show v1) (show v2)
  case op of
    AST.Unify -> unify v1 v2
    AST.Add -> arith v1 v2
    AST.Sub -> arith v1 v2
    AST.Mul -> arith v1 v2
    AST.Div -> arith v1 v2
  where
    expr = ExprBinaryOp op e1 e2

    arith :: Runtime m => Value -> Value -> m Value
    arith v1 v2 =
      let f :: Runtime m => Value -> Value -> m Value
          f = calcNum op
       in case (v1, v2) of
            -- For arithmetic operations, they could only be applied to atoms. If any of the values is pending, we do
            -- not need to verify if the temp value is concrete or not. The reason is that the temp value can not be
            -- atoms.
            (Pending p1, Pending p2) -> delayBinaryOp op f p1 p2
            (Pending p1, _) -> delayUnaryOp expr (`f` v2) p1
            (_, Pending p2) -> delayUnaryOp expr (f v1) p2
            (_, _) -> f v1 v2

calcNum :: (Runtime m) => BinaryOp -> Value -> Value -> m Value
calcNum op v1 v2 = do
  dump $ printf "exec (%s %s %s)" (show op) (show v1) (show v2)
  case (v1, v2) of
    (Int i1, Int i2) -> do
      f <- numOp op
      return $ Int (f i1 i2)
    _ ->
      throwError $
        printf "values %s and %s cannot be used for %s" (show v1) (show v2) (show op)

numOp :: (Runtime m, Integral a) => BinaryOp -> m (a -> a -> a)
numOp AST.Add = return (+)
numOp AST.Sub = return (-)
numOp AST.Mul = return (*)
numOp AST.Div = return div
numOp op = throwError $ printf "unsupported binary operator: %s" (show op)

-- | Checks whether the given value can be applied to other dependents. If it can, then apply the value to
-- the pending value, and propagate the value to other dependents.
-- Parameters:
--  path is the path to the trigger value.
propagate :: Runtime m => (Path, Value) -> m ()
propagate (path, val) = do
  rvDeps <- gets ctxReverseDeps
  dump $ printf "propagate: path: %s, value: %s, revDeps: %s" (show path) (show val) (prettyRevDeps rvDeps)
  case val of
    Stub -> throwError $ printf "propagate: path: %s, stub value: %s" (show path) (show val)
    Pending pv@(PendingValue {}) ->
      let temp = pvTemp pv
       in if isValueStub temp
            then dump $ printf "propagate: path: %s, skip stub pending value" (show path)
            else do
              dump $ printf "propagate: path: %s, pending value has evaluated temp: %s" (show path) (show temp)
              prop
    _ -> prop
  where
    prop = do
      revDeps <- gets ctxReverseDeps
      case Map.lookup path revDeps of
        Nothing -> do
          dump $ printf "propagate: path: %s, no reverse dependency, revDeps: %s" (show path) (prettyRevDeps revDeps)
          return ()
        Just penPath -> do
          -- pendVal <- fromJust <$> getValueFromCtx penPath
          pendVal <- undefined
          dump $
            printf
              "propagate: path: %s, pre: %s->%s, val: %s, pendVal: %s"
              (show path)
              (show path)
              (show penPath)
              (show val)
              (show pendVal)

          newPendVal <- resolve pendVal (path, val)
          -- Once the pending value is evaluated, we should trigger the fillPen for other pending values that depend
          -- on this value.
          propagate (penPath, newPendVal)
          -- update the pending block.
          storeValueInCtx penPath newPendVal
          dump $
            printf
              "propagate: path: %s, post: %s->%s, val: %s, pendVal: %s, newPendVal: %s"
              (show path)
              (show path)
              (show penPath)
              (show val)
              (show pendVal)
              (show newPendVal)

-- | Tries to re-evaluate the pending value with the new value once all the dependencies are available. If not all
-- available, the new value is added to the dependencies of the pending value.
-- Parameters:
--  value is the pending value that is to be resolved.
--  pair is the new (path, value) pair that is used to re-evaluate the pending value.
resolve :: Runtime m => Value -> (Path, Value) -> m Value
resolve Stub _ =
  throwError $ printf "resolve: can not resolve a stub value"
resolve (Pending pv@(PendingValue {})) (tgPath, tg)
  | isNothing $ find (== tgPath) (pvDeps pv) =
      throwError $
        printf
          "resolve: path: %s, trigger value, tgpath: %s, is not found in the dependency list"
          (show (pvPath pv))
          (show tgPath)
  | otherwise =
      let pendPath = pvPath pv
          newArgs =
            if isNothing $ lookup tgPath (pvArgs pv)
              then (tgPath, tg) : pvArgs pv
              else (tgPath, tg) : filter (\(p, _) -> p /= tgPath) (pvArgs pv)
       in do
            -- arguments are enough, no matter whether all of them are atoms, concrete or not.
            if length newArgs == length (pvDeps pv)
              then do
                dump $
                  printf
                    "resolve: path: %s, arguments are enough, pending value is temporarily evaluated"
                    (show pendPath)
                newTemp <- pvEvaluator pv newArgs
                dump $
                  printf
                    "resolve: path: %s, arguments are enough, pending value is temporarily evaluated to %s"
                    (show pendPath)
                    (show newTemp)
                if
                    | isValueAtom newTemp -> do
                        tidyRevDeps pendPath
                        revDeps <- gets ctxReverseDeps
                        dump $
                          printf
                            "resolve: path: %s, evaluated to atom, new revDeps: %s"
                            (show pendPath)
                            (prettyRevDeps revDeps)
                        return newTemp
                    -- If the new temp value is also pending, this means the evaluator evaluates to an updated pending
                    -- value that have new dependencies. The original dependencies should be discarded.
                    | isValuePending newTemp -> do
                        tidyRevDeps pendPath
                        revDeps <- gets ctxReverseDeps
                        dump $
                          printf
                            "resolve: path: %s, evaluated to another pending, new revDeps: %s"
                            (show pendPath)
                            (prettyRevDeps revDeps)
                        return newTemp
                    -- The new temp value is either concrete or incomplete. For example, if the new temp value is a
                    -- struct, the dependencies should be kept.
                    | otherwise -> return $ Pending $ pv {pvArgs = newArgs, pvTemp = newTemp}
              else do
                dump $
                  printf
                    "resolve: path: %s, args are not enough to trigger, new val: %s, %s->%s, newArgs: %s"
                    (show pendPath)
                    (show tg)
                    (show tgPath)
                    (show pendPath)
                    (show newArgs)
                return $ Pending $ pv {pvArgs = newArgs}
  where
    tidyRevDeps :: Runtime m => Path -> m ()
    tidyRevDeps p = do
      modify $ \ctx -> ctx {ctxReverseDeps = Map.filter (/= p) (ctxReverseDeps ctx)}
resolve v _ = throwError $ printf "resolve cannot resolve a non-pending value: %s" (show v)

data DisjItem = DisjDefault Value | DisjRegular Value

evalDisj :: Runtime m => Expression -> Expression -> Path -> m Value
evalDisj e1 e2 path = case (e1, e2) of
  (ExprUnaryExpr (UnaryExprUnaryOp Star se1), ExprUnaryExpr (UnaryExprUnaryOp Star se2)) ->
    evalExprPair (DisjDefault, evalUnaryExpr se1 path) (DisjDefault, evalUnaryExpr se2 path)
  (ExprUnaryExpr (UnaryExprUnaryOp Star se1), _) ->
    evalExprPair (DisjDefault, evalUnaryExpr se1 path) (DisjRegular, doEval e2 path)
  (_, ExprUnaryExpr (UnaryExprUnaryOp Star se2)) ->
    evalExprPair (DisjRegular, doEval e1 path) (DisjDefault, evalUnaryExpr se2 path)
  (_, _) -> evalExprPair (DisjRegular, doEval e1 path) (DisjRegular, doEval e2 path)
  where
    -- evalExprPair is used to evaluate a disjunction with both sides still being stub.
    evalExprPair ::
      Runtime m => (Value -> DisjItem, m Value) -> (Value -> DisjItem, m Value) -> m Value
    evalExprPair (cons1, m1) (cons2, m2) = do
      v1 <- m1
      v2 <- m2
      evalDisjPair (cons1 v1) (cons2 v2)

    -- evalDisjPair is used to evaluate a disjunction whose both sides are evaluated.
    evalDisjPair :: Runtime m => DisjItem -> DisjItem -> m Value
    evalDisjPair (DisjDefault v1) r2 =
      evalLeftPartial (\(df1, ds1, df2, ds2) -> newDisj df1 ds1 df2 ds2) v1 r2
    -- reverse v2 r1 and also the order to the disjCons.
    evalDisjPair r1@(DisjRegular _) (DisjDefault v2) =
      evalLeftPartial (\(df2, ds2, df1, ds1) -> newDisj df1 ds1 df2 ds2) v2 r1
    evalDisjPair (DisjRegular v1) (DisjRegular v2) = evalRegularDisj v1 v2

    -- evalLeftPartial is used to evaluate a disjunction whose left side is a default.
    -- the first argument is a function that takes the four lists of values and returns a disjunction.
    evalLeftPartial ::
      (MonadError String m) => (([Value], [Value], [Value], [Value]) -> m Value) -> Value -> DisjItem -> m Value
    evalLeftPartial disjCons (Value.Disjunction df1 ds1) (DisjRegular (Value.Disjunction _ ds2)) =
      -- This is rule M2 and M3. We eliminate the defaults from the right side.
      disjCons (df1, ds1, [], ds2)
    evalLeftPartial disjCons v1 (DisjRegular (Value.Disjunction df2 ds2)) =
      -- This is rule M1.
      disjCons ([v1], [v1], df2, ds2)
    evalLeftPartial disjCons v1 (DisjRegular v2) =
      disjCons ([v1], [v1], [], [v2])
    evalLeftPartial disjCons v1 (DisjDefault v2) =
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
