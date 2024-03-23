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
import Control.Monad.Except (MonadError, runExceptT, throwError)
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
initState = Context (emptyStruct, []) Map.empty

runIO :: (MonadIO m) => String -> m (Either String Value)
runIO s = runStderrLoggingT $ runExceptT $ runStr s

runStr :: (MonadError String m, MonadLogger m) => String -> m Value
runStr s = do
  parsedE <- parseCUE s
  eval (transform parsedE) emptyPath

eval :: (MonadError String m, MonadLogger m) => Expression -> Path -> m Value
eval expr path = fst <$> runStateT (doEval expr path) initState

doEval :: Runtime m => Expression -> Path -> m Value
doEval (ExprUnaryExpr e) = evalUnaryExpr e
doEval (ExprBinaryOp op e1 e2) = evalBinary op e1 e2

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

-- | The struct is guaranteed to have unique labels by transform.
evalStructLit :: Runtime m => [(Label, Expression)] -> Path -> m Value
evalStructLit lit path =
  let labels = map evalLabel lit
      fieldsStub =
        foldr
          ( \(k, _) acc ->
              Map.insert
                k
                ( Unevaluated (appendSel (Path.StringSelector k) path)
                )
                acc
          )
          Map.empty
          (map (\x -> (evalLabel x, snd x)) lit)
      idSet = Set.fromList (getVarLabels lit)
      structStub = StructValue labels fieldsStub idSet Set.empty
   in do
        dump $ printf "new struct, path: %s" (show path)
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
    evalField :: Runtime m => Maybe Value -> (String, Expression) -> m (Maybe Value)
    evalField acc (name, e) =
      let fieldPath = appendSel (Path.StringSelector name) path
       in if isJust acc
            then return acc
            else do
              dump $ printf "evalField: path: %s, starts, expr: %s" (show fieldPath) (show e)
              v <- doEval e fieldPath
              dump $ printf "evalField: path: %s, evaluated, expr is evaluated to %s" (show fieldPath) (show v)
              putValueInCtx fieldPath v
              propagate (fieldPath, v)
              dump $ printf "evalField: path: %s, done" (show fieldPath)
              case v of
                Bottom {} -> return $ Just v
                _ -> return Nothing

    fetchVarLabel :: Label -> Maybe String
    fetchVarLabel (Label (LabelName (LabelID var))) = Just var
    fetchVarLabel _ = Nothing

    getVarLabels :: [(Label, Expression)] -> [String]
    getVarLabels xs = map (\(l, _) -> fromJust (fetchVarLabel l)) (filter (\(l, _) -> isJust (fetchVarLabel l)) xs)

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
  ctx <- get
  let scope = case goToScope (ctxCurBlock ctx) exprPath of
        Just b -> b
        Nothing -> ctxCurBlock ctx
  case searchUpVar var scope of
    -- varPath is only a placeholder here.
    Just (varPath, varVal) -> do
      res <- (varPath,) <$> mkRef (exprPath, AST.idCons var) (varPath, varVal)
      dump $ printf "lookupVar: path: %s, found var: %s, value: %s" (show exprPath) var (show res)
      return res
    Nothing ->
      throwError $
        printf "variable %s is not found, path: %s, scope: %s" var (show exprPath) (show scope)

-- where
--   getVarPair :: (MonadError String m, MonadState Context m) => TreeCursor -> Path -> Value -> m (Path, Value)
--   getVarPair scope valPath v
--     | isValueAtom v = do
--         trace (printf "lookupVar found atom %s, scope: %s, value: %s" (show var) (show scope) (show v)) pure ()
--         return (valPath, v)
--   -- valPath is only a placeholder here.
--   getVarPair _ valPath (Pending v) = (valPath,) <$> depend (exprPath, AST.idCons var) v
--   -- This is the case when the value is not atom, nor pending.
--   -- valPath is only a placeholder here.
--   getVarPair _ valPath v = return (valPath, mkReference (AST.idCons var) exprPath valPath v)

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
            Nothing -> Unevaluated fieldPath
       in do
            dump $
              printf "dot: path: %s, spath: %s, field: %s, fieldVal: %s" (show path) (show sPath) field (show fieldVal)
            mkRef (path, expr) (fieldPath, fieldVal)

    select :: Runtime m => String -> Value -> m Value
    -- {x: y, a: x, y: {}}, where y is unevaluated and we are evaluating a.
    select field (Pending pv) =
      let temp = pvTemp pv
       in case temp of
            Unevaluated {} -> do
              dump $ printf "evalSelector: %s is unevaluated" (show soVal)
              delayUnaryOp expr (select field) pv
            _ -> select field temp
    select field (Struct sv) = dot (soPath, sv) field
    select field (Value.Disjunction [x] _) = select field x
    -- {a: x.c, x: {}}, where x is unevaluated.
    select _ (Unevaluated _) = throwError $ printf "evalSelector: %s is unevaluated" (show soVal)
    select _ _ = return . Bottom $ printf "%s is not a struct" (show soVal)

-- refField (path, expr) (_, uv@(Unevaluated {})) =
--   if uePath uv == path
--     then do
--       dump $ printf "depend: self cycle detected. path: %s" (show path)
--       return Top
--     else do
--       dump $ printf "depend: unevaluated is %s" (show uv)
--       createDepVal (uePath uv)
-- refField (path, expr) (_, Pending pv) = do
--   dump $ printf "refField: %s is referencing pending %s" (show path) (show pv)
--   depend (path, expr) pv
-- refField (path, expr) (valPath, val) = return $ mkReference expr path valPath val

-- | Access the named field of the struct.
-- Parameters:
--   field is the name of the field.
--   path is the path to the current expression that contains the selector.
--   value is the struct value.
-- For example,
--  { a: b: x.y }
-- If the field is "y", and the exprPath is "a.b", expr is "x.y", the structPath is "x".
-- TODO:
-- Value.Disjunction [x] _ -> lookupStructField x
-- dot :: Runtime m => (Path, AST.Expression) -> (Path, StructValue) -> String -> m Value
-- dot (path, expr) (structPath, sv) field = case Map.lookup field (svFields sv) of
--   Just v -> refField (path, expr) (fieldPath, v)
--   -- The incomplete selector case.
--   Nothing ->
--     return $
--       mkReference expr path fieldPath (mkUnevaluated path)
--   where
--     fieldPath = appendSel (Path.StringSelector field) structPath

--   lookupStructField _ =
--     return $
--       Bottom $
--         printf
--           "dot: path: %s, sel: %s, value: %s is not a struct"
--           (show path)
--           (show field)
--           (show structVal)
-- _ -> lookupStructField structVal
-- where
--   fieldPath = appendSel (Path.StringSelector field) structPath
--   lookupStructField (Struct sv) = case Map.lookup field (svFields sv) of
--     Just v -> refField (path, expr) (fieldPath, v)
--     -- The incomplete selector case.
--     Nothing ->
--       return $
--         mkReference expr path fieldPath (mkUnevaluated path)
--   lookupStructField _ =
--     return $
--       Bottom $
--         printf
--           "dot: path: %s, sel: %s, value: %s is not a struct"
--           (show path)
--           (show field)
--           (show structVal)

-- getField :: (MonadError String m, MonadState Context m) => Value -> m Value
-- -- The referenced value could be a pending value. Once the pending value is evaluated, the selector should be
-- -- populated with the value.
-- getField (Pending v) = depend (path, idCons field) v
-- getField v@(Struct _) = return v
-- getField v
--   | isValueConcrete v = return v
-- -- The value is incomplete, so we create a new pending value.
-- getField v =
--   let newPath = appendSel (Path.StringSelector field) path
--    in do
--         trace
--           ( printf
--               "dot: path: %s, sel: %s, value %s is not concrete"
--               (show newPath)
--               (show field)
--               (show v)
--           )
--           pure
--           ()
--         return $ mkReference expr path newPath

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

-- -- | Bind a pending value to a function.
-- -- The first argument is the function that takes the value and returns a value.
-- bindUnary ::
--   Runtime m =>
--   (Value -> EvalMonad Value) ->
--   (AST.Expression -> Maybe AST.Expression) ->
--   Value ->
--   m Value
-- bindUnary f exprF (Pending v) = case v of
--   pv@(PendingValue {}) -> do
--     expr <- transExpr exprF (pvExpr pv)
--     newTemp <-
--       if isValueConcrete (pvTemp pv)
--         then f (pvTemp pv)
--         else return $ mkUnevaluated (pvPath pv)
--     return $ Pending $ pv {pvEvaluator = bindEval (pvEvaluator pv) f, pvTemp = newTemp, pvExpr = expr, pvIsRef = False}
--   _ -> throwError $ printf "bindUnary: value %s is not PendingValue" (show v)
-- bindUnary _ _ v = throwError $ printf "bindUnary: value %s is not pending" (show v)
--
-- transExpr :: MonadError String m => (AST.Expression -> Maybe AST.Expression) -> AST.Expression -> m AST.Expression
-- transExpr f e = case f e of
--   Just _e -> return _e
--   Nothing -> throwError "bindUnary: exprF returns Nothing"

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

-- unifyOp :: Runtime m => Value -> Value -> m Value
-- unifyOp v1@(Pending p1) v2@(Pending p2) = case (p1, p2) of
--   (PendingValue {}, PendingValue {}) ->
--     if
--         | isValueUnevaluated (pvTemp p1) && isValueUnevaluated (pvTemp p2) -> delayBinaryOp op unify p1 p2
--         | isValueUnevaluated (pvTemp p1) -> delayUnaryOp expr (`unify` v2) p1
--         | isValueUnevaluated (pvTemp p2) -> delayUnaryOp expr (unify v1) p2
--         | otherwise -> unify v1 v2
--   _ -> return $ Bottom $ printf "%s and %s can not be unified" (show v1) (show v2)
-- unifyOp v1@(Pending p1) v2 = case p1 of
--   PendingValue {} ->
--     if isValueUnevaluated (pvTemp p1)
--       then delayUnaryOp expr (`unify` v2) p1
--       else unify (pvTemp p1) v2
--   _ -> return $ Bottom $ printf "%s and %s can not be unified" (show v1) (show v2)

-- unifyOp v1 v2
--   | isValuePending v1 && isValuePending v2 =
--       if hasConcreteTemp v1 && hasConcreteTemp v2
--         then do
--           tv1 <- getTemp v1
--           tv2 <- getTemp v2
--           dispatch op tv1 tv2
--         else -- since both values are pending, we should bind both, not bind one of them because both can be updated.
--           bindBinary (ExprBinaryOp op e1 e2) (dispatch op) v1 v2
--   | isValuePending v1 = let f = dispatch op in bindUnary (`f` v2) (binExpr op (Right v2)) v1
--   | isValuePending v2 = let f = dispatch op in bindUnary (f v1) (binExpr op (Left v1)) v2
--   | otherwise = dispatch op v1 v2

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

-- binExpr :: AST.BinaryOp -> Either Value Value -> AST.Expression -> Maybe AST.Expression
-- binExpr op (Left v) e2 = do
--   e1 <- toExpr v
--   return $ AST.binaryOpCons op e1 e2
-- binExpr op (Right v) e1 = do
--   e2 <- toExpr v
--   return $ AST.binaryOpCons op e1 e2

-- | Checks whether the given value can be applied to other dependents. If it can, then apply the value to
-- the pending value, and propagate the value to other dependents.
-- Parameters:
--  path is the path to the trigger value.
propagate :: Runtime m => (Path, Value) -> m ()
propagate (path, val) = do
  _revDeps <- gets ctxReverseDeps
  dump $ printf "propagate: path: %s, value: %s, revDeps: %s" (show path) (show val) (prettyRevDeps _revDeps)
  case val of
    Pending pv@(PendingValue {}) ->
      let temp = pvTemp pv
       in if not $ isValueDep temp
            then -- If the pending value has a non-pending temp value, use that value to try to evaluate the pending value.
            -- This works because the reverse dependency is always a 1-1 mapping.
            do
              dump $ printf "propagate: path: %s, pending value uses temp %s" (show path) (show temp)
              propagate (path, temp)
            else dump $ printf "propagate: path: %s, skip pending value with pending temp value" (show path)
    Unevaluated {} -> throwError $ printf "propagate: path: %s, unevaluated value: %s" (show path) (show val)
    _ -> do
      revDeps <- gets ctxReverseDeps
      case Map.lookup path revDeps of
        Nothing -> do
          dump $ printf "propagate: path: %s, no reverse dependency, revDeps: %s" (show path) (prettyRevDeps revDeps)
          return ()
        Just penPath -> do
          pendVal <- getValueFromCtx penPath
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
          putValueInCtx penPath newPendVal
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
--  penPath is the path to the pending value.
--  penV is the pending value.
--  pair is the new (path, value) pair that is used to re-evaluate the pending value.
resolve :: Runtime m => Value -> (Path, Value) -> m Value
resolve _ (_, val@(Pending {})) =
  throwError $
    printf "resolve expects a non-pending value to trigger re-evaluation, but got %s" (show val)
resolve uv@(Unevaluated {}) _ =
  throwError $ printf "resolve: can not resolve an unevaluated value: %s" (show uv)
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
       in -- atomsNum =
          --   foldr (\(_, v) acc -> if isValueAtom v then acc + 1 else acc) 0 newArgs
          do
            -- \| atomsNum == length (pvDeps pv) = do
            --     dump $
            --       printf "resolve: path: %s, all atoms, pending value is to be evaluated to atom" (show pendPath)
            --     res <- pvEvaluator pv newArgs
            --     dump $ printf "resolve: path: %s, pending value is fully evaluated to: %s" (show pendPath) (show res)
            --     -- TODO: If the result is an atom, we should remove all the reverse dependencies.
            --     return res
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
    -- evalExprPair is used to evaluate a disjunction with both sides still being unevaluated.
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
