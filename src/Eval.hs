{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Eval
  ( runIO,
    eval,
  )
where

import AST
import Control.Monad (foldM_, mapM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (MonadLogger, runStderrLoggingT)
import Control.Monad.State (get, gets, modify, put, runStateT)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust, isNothing)
import qualified Data.Set as Set
import Parser (parseCUE)
import Path
import Text.Printf (printf)
import Unify (unify)
import Value

initState :: Context
initState = Context (TNRoot $ mkTreeLeaf Top, []) Map.empty

runIO :: (MonadIO m, MonadError String m) => String -> m TreeCursor
runIO s = runStderrLoggingT $ runStr s

runStr :: (EvalEnv m) => String -> m TreeCursor
runStr s = do
  parsedE <- parseCUE s
  eval parsedE startPath

eval :: (EvalEnv m) => Expression -> Path -> m TreeCursor
eval expr path = do
  (_, ctx) <- runStateT (doEval expr path) initState
  let tc = ctxEvalTree ctx
  rootTC <- propTopTC tc
  dump $ printf "starting finalize:\n%s" (showTreeCursor rootTC)
  n <- finalizeTC rootTC
  dump $ printf "finalized:\n%s" (showTreeCursor n)
  return n

doEval :: (Runtime m) => Expression -> Path -> m ()
doEval = evalExpr

evalExpr :: (Runtime m) => Expression -> Path -> m ()
evalExpr (ExprUnaryExpr e) = evalUnaryExpr e
evalExpr (ExprBinaryOp op e1 e2) = evalBinary op e1 e2

evalLiteral :: (Runtime m) => Literal -> Path -> m ()
evalLiteral (StructLit s) path = evalStructLit s path
evalLiteral lit path =
  let parSel = fromJust $ lastSel path
   in do
        v <- f lit
        pushNewNode $ insertTCLeafValue parSel v
        leaveCurNode
  where
    f :: (Runtime m) => Literal -> m Value
    f (StringLit (SimpleStringLit s)) = return $ String s
    f (IntLit i) = return $ Int i
    f (BoolLit b) = return $ Bool b
    f TopLit = return Top
    f BottomLit = return $ Bottom ""
    f NullLit = return Null
    f _ = throwError $ printf "literal %s is not possible" (show lit)

-- | The struct is guaranteed to have unique labels by transform.
evalStructLit :: (Runtime m) => [(Label, Expression)] -> Path -> m ()
evalStructLit lit path =
  let labels = map evalLabel lit

      fetchVarLabel :: Label -> Maybe String
      fetchVarLabel (Label (LabelName (LabelID var))) = Just var
      fetchVarLabel _ = Nothing

      getVarLabels :: [(Label, Expression)] -> [String]
      getVarLabels xs = map (\(l, _) -> fromJust (fetchVarLabel l)) (filter (\(l, _) -> isJust (fetchVarLabel l)) xs)

      idSet = Set.fromList (getVarLabels lit)
      parSel = fromJust $ lastSel path
   in do
        dump $ printf "new struct, path: %s" (show path)
        -- create a new block since we are entering a new struct.
        pushNewNode $ insertTCScope parSel labels idSet
        -- bm <- foldM evalField Nothing (zipWith (\name (_, e) -> (name, e)) labels lit)
        mapM_ evalField (zipWith (\name (_, e) -> (name, e)) labels lit)
        -- v <- case bm of
        --   Just b -> return b
        --   -- Nothing -> fromJust <$> getValueFromCtx path
        --   Nothing -> undefined
        leaveCurNode
        dump $ printf "new struct, path: %s, evaluated" (show path)
  where
    evalLabel (Label (LabelName ln), _) = case ln of
      LabelID ident -> ident
      LabelString ls -> ls

    -- evalField evaluates a field in a struct.
    evalField :: (Runtime m) => (String, Expression) -> m ()
    evalField (name, e) =
      let fieldPath = appendSel (Path.StringSelector name) path
       in do
            dump $ printf "evalField: path: %s, starts, expr: %s" (show fieldPath) (show e)
            v <- doEval e fieldPath
            dump $ printf "evalField: path: %s, evaluated, expr is evaluated to %s" (show fieldPath) (show v)
            -- storeValueInCtx fieldPath v
            -- The reason we need to propagate here, not after once a value is evaluated, is that the value could be
            -- part of a binary or unary operation.
            -- propagate (fieldPath, v)
            dump $ printf "evalField: path: %s, done" (show fieldPath)

evalUnaryExpr :: (Runtime m) => UnaryExpr -> Path -> m ()
evalUnaryExpr (UnaryExprPrimaryExpr primExpr) = \path -> evalPrimExpr primExpr path
evalUnaryExpr (UnaryExprUnaryOp op e) = evalUnaryOp op e

evalPrimExpr :: (Runtime m) => PrimaryExpr -> Path -> m ()
evalPrimExpr (PrimExprOperand op) path = case op of
  OpLiteral lit -> evalLiteral lit path
  OpExpression expr -> doEval expr path
  OperandName (Identifier ident) -> lookupVar ident path
evalPrimExpr e@(PrimExprSelector primExpr sel) path = do
  _ <- evalPrimExpr primExpr path
  evalSelector e sel path

-- | Looks up the variable denoted by the name in the current scope or the parent scopes.
-- If the variable is not atom, a new pending value is created and returned. The reason is that if the referenced
-- var was updated with a new value, the pending value should be updated with the value.
-- Parameters:
--   var denotes the variable name.
--   exprPath is the path to the current expression that contains the selector.
-- For example,
--  { a: b: x+y }
-- If the name is "y", and the exprPath is "a.b".
lookupVar :: (Runtime m) => String -> Path -> m ()
lookupVar var path =
  let parSel = fromJust $ lastSel path
   in do
        dump $ printf "lookupVar: path: %s, looks up var: %s" (show path) var
        tc <- gets ctxEvalTree
        case searchTCVar var tc of
          Nothing -> throwError $ printf "variable %s is not found, path: %s" var (show path)
          Just tarTC -> do
            pushNewNode $ insertTCLink parSel (pathFromTC tarTC)
            leaveCurNode

-- lookupVar :: (Runtime m) => String -> Path -> m (Path, Value)
-- lookupVar var exprPath = do
--   dump $ printf "lookupVar: path: %s, looks up var: %s" (show exprPath) var
--   stack <- gets ctxScopeStack
--   case searchUpVar var stack of
--     Nothing -> do
--       throwError $ printf "variable %s is not found, path: %s" var (show exprPath)
--     Just varPath -> do
--       -- vm <- getValueFromCtx varPath
--       vm <- undefined
--       case vm of
--         Nothing -> throwError $ printf "variable %s is not found, path: %s" var (show exprPath)
--         Just varVal -> do
--           res <- (varPath,) <$> mkRef (exprPath, AST.idCons var) (varPath, varVal)
--           dump $ printf "lookupVar: path: %s, found var: %s, value: %s" (show exprPath) var (show res)
--           return res

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
  (Runtime m) => PrimaryExpr -> AST.Selector -> Path -> m ()
evalSelector pe astSel path =
  let parSel = fromJust $ lastSel path
      sel = case astSel of
        IDSelector ident -> ident
        AST.StringSelector str -> str
   in -- dot :: (EvalEnv m) => String -> Value -> m Value
      -- dot field (Struct sv) = do
      --   case Map.lookup field (svFields sv) of
      --     Just v -> return v
      --     -- The incomplete selector case.
      --     Nothing -> return $ Bottom $ printf "field %s is not found" field
      -- dot field (Value.Disjunction [x] _) = dot field x
      -- dot _ v = return . Bottom $ printf "%s is not a struct" (show v)
      do
        pushNewNode $ insertTCDot parSel (Path.StringSelector sel) (UnaryExprPrimaryExpr pe)
        leaveCurNode

-- expr = ExprUnaryExpr (UnaryExprPrimaryExpr pe)
-- dot :: (EvalEnv m) => (Path, StructValue) -> String -> m Value
-- dot (sPath, sv) field =
-- let fieldPath = appendSel (Path.StringSelector field) sPath
--     fieldVal = case Map.lookup field (svFields sv) of
--       Just v -> v
--       -- The incomplete selector case.
--       Nothing -> Stub
--  in do
--       dump $
--         printf "dot: path: %s, spath: %s, field: %s, fieldVal: %s" (show path) (show sPath) field (show fieldVal)
--       -- mkRef (path, expr) (fieldPath, fieldVal)
--       undefined

-- select :: (EvalEnv m) => String -> Value -> m Value
-- -- {x: y, a: x, y: {}}, where y is stub and we are evaluating a.
-- select field (Pending pv) =
--   let temp = pvTemp pv
--    in case temp of
--         Stub -> do
--           dump $ printf "evalSelector: %s is stub" (show soVal)
--           delayUnaryOp expr (select field) pv
--         _ -> select field temp
-- select field (Struct sv) = dot (soPath, sv) field
-- select field (Value.Disjunction [x] _) = select field x
-- -- {a: x.c, x: {}}, where x is stub.
-- select _ Stub = throwError $ printf "evalSelector: %s is stub" (show soVal)
-- select _ _ = return . Bottom $ printf "%s is not a struct" (show soVal)

-- | Evaluates the unary operator.
-- unary operator should only be applied to atoms.
evalUnaryOp :: (Runtime m) => UnaryOp -> UnaryExpr -> Path -> m ()
evalUnaryOp op e path =
  let parSel = fromJust $ lastSel path
      nextPath = appendSel UnaryOpSelector path
   in do
        pushNewNode $ insertTCUnaryOp parSel (show op) (UnaryExprUnaryOp op e) (dispUnaryFunc op)
        _ <- evalUnaryExpr e nextPath
        dump $ printf "leaving evalUnaryOp"
        leaveCurNode

dispUnaryFunc :: (EvalEnv m) => UnaryOp -> TreeNode -> m TreeNode
dispUnaryFunc = go
  where
    go Plus (TNLeaf (TreeLeaf (Int i))) = return $ mkTreeLeaf $ Int i
    go Minus (TNLeaf (TreeLeaf (Int i))) = return $ mkTreeLeaf$ Int (-i)
    go Not (TNLeaf (TreeLeaf (Bool b))) = return $ mkTreeLeaf $ Bool (not b)
    go op t = throwError $ printf "%s cannot be used for value %s" (show op) (show t)

-- go :: (Runtime m) => UnaryOp -> Value -> m Value
-- go _ (Pending pv) = delayUnaryOp (ExprUnaryExpr $ UnaryExprUnaryOp op e) (go op) pv
-- go _ v
--   | not $ isValueAtom v =
--       return . Bottom $ printf "%s cannot be used for %s" (show op) (show v)

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (Runtime m) => BinaryOp -> Expression -> Expression -> Path -> m ()
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjunction e1 e2 path = evalDisj e1 e2 path
evalBinary op e1 e2 path =
  let parSel = fromJust $ lastSel path
   in do
        pushNewNode $ insertTCBinaryOp parSel (show op) (ExprBinaryOp op e1 e2) (dispBinFunc op)
        v1 <- doEval e1 $ appendSel (BinOpSelector L) path
        v2 <- doEval e2 $ appendSel (BinOpSelector R) path
        dump $ printf "eval binary (%s %s %s)" (show op) (show v1) (show v2)
        leaveCurNode

-- case op of
--   AST.Unify -> unify v1 v2
--   AST.Add -> arith v1 v2
--   AST.Sub -> arith v1 v2
--   AST.Mul -> arith v1 v2
--   AST.Div -> arith v1 v2
-- where
--   expr = ExprBinaryOp op e1 e2
--
--   arith :: (Runtime m) => Value -> Value -> m Value
--   arith v1 v2 =
--     let f :: (Runtime m) => Value -> Value -> m Value
--         f = calcNum op
--      in case (v1, v2) of
--           -- For arithmetic operations, they could only be applied to atoms. If any of the values is pending, we do
--           -- not need to verify if the temp value is concrete or not. The reason is that the temp value can not be
--           -- atoms.
--           (Pending p1, Pending p2) -> delayBinaryOp op f p1 p2
--           (Pending p1, _) -> delayUnaryOp expr (`f` v2) p1
--           (_, Pending p2) -> delayUnaryOp expr (f v1) p2
--           (_, _) -> f v1 v2

dispBinFunc :: (EvalEnv m) => BinaryOp -> TreeNode -> TreeNode -> m TreeNode
dispBinFunc op = case op of
  AST.Unify -> unify
  _ -> calcNum op

calcNum :: (EvalEnv m) => BinaryOp -> TreeNode -> TreeNode -> m TreeNode 
calcNum op t1 t2 = case (t1, t2) of 
  (TNLeaf l1, TNLeaf l2) -> let
    v1 = trfValue l1
    v2 = trfValue l2
    in do
      dump $ printf "exec (%s %s %s)" (show op) (show v1) (show v2)
      case (v1, v2) of
        (Int i1, Int i2) -> do
          f <- numOp op
          return $ mkTreeLeaf $ Int (f i1 i2)
        _ ->
          throwError $ printf "values %s and %s cannot be used for %s" (show v1) (show v2) (show op)
  _ -> throwError $ printf "values %s and %s cannot be used for %s" (show t1) (show t2) (show op)

numOp :: (EvalEnv m, Integral a) => BinaryOp -> m (a -> a -> a)
numOp AST.Add = return (+)
numOp AST.Sub = return (-)
numOp AST.Mul = return (*)
numOp AST.Div = return div
numOp op = throwError $ printf "unsupported binary operator: %s" (show op)

-- -- | Checks whether the given value can be applied to other dependents. If it can, then apply the value to
-- -- the pending value, and propagate the value to other dependents.
-- -- Parameters:
-- --  path is the path to the trigger value.
-- propagate :: (Runtime m) => (Path, Value) -> m ()
-- propagate (path, val) = do
--   rvDeps <- gets ctxReverseDeps
--   dump $ printf "propagate: path: %s, value: %s, revDeps: %s" (show path) (show val) (prettyRevDeps rvDeps)
--   case val of
--     Stub -> throwError $ printf "propagate: path: %s, stub value: %s" (show path) (show val)
--     Pending pv@(PendingValue {}) ->
--       let temp = pvTemp pv
--        in if isValueStub temp
--             then dump $ printf "propagate: path: %s, skip stub pending value" (show path)
--             else do
--               dump $ printf "propagate: path: %s, pending value has evaluated temp: %s" (show path) (show temp)
--               prop
--     _ -> prop
--   where
--     prop = do
--       revDeps <- gets ctxReverseDeps
--       case Map.lookup path revDeps of
--         Nothing -> do
--           dump $ printf "propagate: path: %s, no reverse dependency, revDeps: %s" (show path) (prettyRevDeps revDeps)
--           return ()
--         Just penPath -> do
--           -- pendVal <- fromJust <$> getValueFromCtx penPath
--           pendVal <- undefined
--           dump $
--             printf
--               "propagate: path: %s, pre: %s->%s, val: %s, pendVal: %s"
--               (show path)
--               (show path)
--               (show penPath)
--               (show val)
--               (show pendVal)
--
--           newPendVal <- resolve pendVal (path, val)
--           -- Once the pending value is evaluated, we should trigger the fillPen for other pending values that depend
--           -- on this value.
--           propagate (penPath, newPendVal)
--           -- update the pending block.
--           storeValueInCtx penPath newPendVal
--           dump $
--             printf
--               "propagate: path: %s, post: %s->%s, val: %s, pendVal: %s, newPendVal: %s"
--               (show path)
--               (show path)
--               (show penPath)
--               (show val)
--               (show pendVal)
--               (show newPendVal)

-- -- | Tries to re-evaluate the pending value with the new value once all the dependencies are available. If not all
-- -- available, the new value is added to the dependencies of the pending value.
-- -- Parameters:
-- --  value is the pending value that is to be resolved.
-- --  pair is the new (path, value) pair that is used to re-evaluate the pending value.
-- resolve :: (Runtime m) => Value -> (Path, Value) -> m Value
-- resolve Stub _ =
--   throwError $ printf "resolve: can not resolve a stub value"
-- resolve (Pending pv@(PendingValue {})) (tgPath, tg)
--   | isNothing $ find (== tgPath) (pvDeps pv) =
--       throwError $
--         printf
--           "resolve: path: %s, trigger value, tgpath: %s, is not found in the dependency list"
--           (show (pvPath pv))
--           (show tgPath)
--   | otherwise =
--       let pendPath = pvPath pv
--           newArgs =
--             if isNothing $ lookup tgPath (pvArgs pv)
--               then (tgPath, tg) : pvArgs pv
--               else (tgPath, tg) : filter (\(p, _) -> p /= tgPath) (pvArgs pv)
--        in do
--             -- arguments are enough, no matter whether all of them are atoms, concrete or not.
--             if length newArgs == length (pvDeps pv)
--               then do
--                 dump $
--                   printf
--                     "resolve: path: %s, arguments are enough, pending value is temporarily evaluated"
--                     (show pendPath)
--                 newTemp <- pvEvaluator pv newArgs
--                 dump $
--                   printf
--                     "resolve: path: %s, arguments are enough, pending value is temporarily evaluated to %s"
--                     (show pendPath)
--                     (show newTemp)
--                 if
--                   | isValueAtom newTemp -> do
--                       tidyRevDeps pendPath
--                       revDeps <- gets ctxReverseDeps
--                       dump $
--                         printf
--                           "resolve: path: %s, evaluated to atom, new revDeps: %s"
--                           (show pendPath)
--                           (prettyRevDeps revDeps)
--                       return newTemp
--                   -- If the new temp value is also pending, this means the evaluator evaluates to an updated pending
--                   -- value that have new dependencies. The original dependencies should be discarded.
--                   | isValuePending newTemp -> do
--                       tidyRevDeps pendPath
--                       revDeps <- gets ctxReverseDeps
--                       dump $
--                         printf
--                           "resolve: path: %s, evaluated to another pending, new revDeps: %s"
--                           (show pendPath)
--                           (prettyRevDeps revDeps)
--                       return newTemp
--                   -- The new temp value is either concrete or incomplete. For example, if the new temp value is a
--                   -- struct, the dependencies should be kept.
--                   | otherwise -> return $ Pending $ pv {pvArgs = newArgs, pvTemp = newTemp}
--               else do
--                 dump $
--                   printf
--                     "resolve: path: %s, args are not enough to trigger, new val: %s, %s->%s, newArgs: %s"
--                     (show pendPath)
--                     (show tg)
--                     (show tgPath)
--                     (show pendPath)
--                     (show newArgs)
--                 return $ Pending $ pv {pvArgs = newArgs}
--   where
--     tidyRevDeps :: (Runtime m) => Path -> m ()
--     tidyRevDeps p = do
--       modify $ \ctx -> ctx {ctxReverseDeps = Map.filter (/= p) (ctxReverseDeps ctx)}
-- resolve v _ = throwError $ printf "resolve cannot resolve a non-pending value: %s" (show v)

data DisjItem = DisjDefault TreeNode | DisjRegular TreeNode

evalDisj :: (Runtime m) => Expression -> Expression -> Path -> m ()
evalDisj e1 e2 path =
  let parSel = fromJust $ lastSel path
   in do
        pushNewNode $ insertTCDisj parSel (ExprBinaryOp AST.Disjunction e1 e2) evalDisjAdapt
        _ <- case (e1, e2) of
          (ExprUnaryExpr (UnaryExprUnaryOp Star se1), ExprUnaryExpr (UnaryExprUnaryOp Star se2)) -> do
            _ <- evalUnaryExpr se1 $ appendSel (BinOpSelector L) path
            evalUnaryExpr se2 $ appendSel (BinOpSelector R) path
          (ExprUnaryExpr (UnaryExprUnaryOp Star se1), _) -> do
            _ <- evalUnaryExpr se1 $ appendSel (BinOpSelector L) path
            doEval e2 $ appendSel (BinOpSelector R) path
          (_, ExprUnaryExpr (UnaryExprUnaryOp Star se2)) -> do
            _ <- doEval e1 $ appendSel (BinOpSelector L) path
            evalUnaryExpr se2 $ appendSel (BinOpSelector R) path
          (_, _) -> do
            _ <- doEval e1 $ appendSel (BinOpSelector L) path
            doEval e2 $ appendSel (BinOpSelector R) path
        leaveCurNode
  where
    -- evalDisjPair is used to evaluate a disjunction whose both sides are evaluated.
    evalDisjPair :: (EvalEnv m) => DisjItem -> DisjItem -> m TreeNode
    evalDisjPair (DisjDefault v1) r2 =
      evalLeftPartial (\(df1, ds1, df2, ds2) -> newDisj df1 ds1 df2 ds2) v1 r2
    -- reverse v2 r1 and also the order to the disjCons.
    evalDisjPair r1@(DisjRegular _) (DisjDefault v2) =
      evalLeftPartial (\(df2, ds2, df1, ds1) -> newDisj df1 ds1 df2 ds2) v2 r1
    evalDisjPair (DisjRegular v1) (DisjRegular v2) = evalRegularDisj v1 v2

    -- evalLeftPartial is used to evaluate a disjunction whose left side is a default.
    -- the first argument is a function that takes the four lists of values and returns a disjunction.
    evalLeftPartial ::
      (MonadError String m) => (([TreeNode], [TreeNode], [TreeNode], [TreeNode]) -> m TreeNode) -> TreeNode -> DisjItem -> m TreeNode
    evalLeftPartial disjCons (TNDisj dj1) (DisjRegular (TNDisj dj2)) =
      -- This is rule M2 and M3. We eliminate the defaults from the right side.
      disjCons ((trdDefaults dj1), (trdDisjuncts dj1), [], (trdDisjuncts dj2))
    evalLeftPartial disjCons v1 (DisjRegular (TNDisj dj2)) =
      -- This is rule M1.
      disjCons ([v1], [v1], (trdDefaults dj2), (trdDisjuncts dj2))
    evalLeftPartial disjCons v1 (DisjRegular v2) =
      disjCons ([v1], [v1], [], [v2])
    evalLeftPartial disjCons v1 (DisjDefault v2) =
      disjCons ([], [v1], [], [v2])

    -- evalFullDisj is used to evaluate a disjunction whose both sides are regular.
    -- Rule: D1, D2
    evalRegularDisj :: (EvalEnv m) => TreeNode -> TreeNode -> m TreeNode
    evalRegularDisj (TNDisj dj1) (TNDisj dj2) = 
      newDisj (trdDefaults dj1) (trdDisjuncts dj1) (trdDefaults dj2) (trdDisjuncts dj2)
    evalRegularDisj (TNDisj dj) y = newDisj (trdDefaults dj) (trdDisjuncts dj) [] [y]
    evalRegularDisj x (TNDisj dj) = newDisj [] [x] (trdDefaults dj) (trdDisjuncts dj)
    -- Rule D0
    evalRegularDisj x y = newDisj [] [x] [] [y]

    -- dedupAppend appends unique elements in ys to the xs list, but only if they are not already in xs.
    -- xs and ys are guaranteed to be unique.
    dedupAppend :: [TreeNode] -> [TreeNode] -> [TreeNode]
    dedupAppend xs ys = xs ++ foldr (\y acc -> if y `elem` xs then acc else y : acc) [] ys

    newDisj :: (EvalEnv m) => [TreeNode] -> [TreeNode] -> [TreeNode] -> [TreeNode] -> m TreeNode
    newDisj df1 ds1 df2 ds2 = return $ mkTreeDisj (dedupAppend df1 df2) (dedupAppend ds1 ds2)

    evalDisjAdapt :: (EvalEnv m) => TreeNode -> TreeNode -> m TreeNode
    evalDisjAdapt v1 v2 =
      case (e1, e2) of
        (ExprUnaryExpr (UnaryExprUnaryOp Star _), ExprUnaryExpr (UnaryExprUnaryOp Star _)) ->
          evalDisjPair (DisjDefault v1) (DisjDefault v2)
        (ExprUnaryExpr (UnaryExprUnaryOp Star _), _) ->
          evalDisjPair (DisjDefault v1) (DisjRegular v2)
        (_, ExprUnaryExpr (UnaryExprUnaryOp Star _)) ->
          evalDisjPair (DisjRegular v1) (DisjDefault v2)
        (_, _) -> evalDisjPair (DisjRegular v1) (DisjRegular v2)
