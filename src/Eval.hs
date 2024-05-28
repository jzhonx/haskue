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
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (runStderrLoggingT)
import Control.Monad.State (gets, runStateT)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import qualified Data.Set as Set
import Parser (parseCUE)
import Path
import Text.Printf (printf)
import Tree
import Unify (unify)

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
        mapM_ evalField (zipWith (\name (_, e) -> (name, e)) labels lit)
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
            doEval e fieldPath
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
   in do
        pushNewNode $ insertTCDot parSel (Path.StringSelector sel) (UnaryExprPrimaryExpr pe)
        leaveCurNode

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
    go Minus (TNLeaf (TreeLeaf (Int i))) = return $ mkTreeLeaf $ Int (-i)
    go Not (TNLeaf (TreeLeaf (Bool b))) = return $ mkTreeLeaf $ Bool (not b)
    go op t = throwError $ printf "%s cannot be used for value %s" (show op) (show t)

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (Runtime m) => BinaryOp -> Expression -> Expression -> Path -> m ()
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjunction e1 e2 path = evalDisj e1 e2 path
evalBinary op e1 e2 path =
  let parSel = fromJust $ lastSel path
   in do
        pushNewNode $ insertTCBinaryOp parSel (show op) (ExprBinaryOp op e1 e2) (dispBinFunc op) (dispBinCond op)
        v1 <- doEval e1 $ appendSel (BinOpSelector L) path
        v2 <- doEval e2 $ appendSel (BinOpSelector R) path
        dump $ printf "eval binary (%s %s %s)" (show op) (show v1) (show v2)
        leaveCurNode

dispBinFunc :: (EvalEnv m) => BinaryOp -> TreeNode -> TreeNode -> m TreeNode
dispBinFunc op = case op of
  AST.Unify -> unify
  _ -> calcNum op

dispBinCond :: BinaryOp -> TreeNode -> TreeNode -> Bool
dispBinCond op = case op of
  AST.Unify -> \x y -> isValueNode x && isValueNode y
  _ -> \x y -> isArithOperand x && isArithOperand y
  where
    isArithOperand :: TreeNode -> Bool
    isArithOperand (TNLeaf leaf) = case trfValue leaf of
      Int _ -> True
      _ -> False
    isArithOperand _ = False

calcNum :: (EvalEnv m) => BinaryOp -> TreeNode -> TreeNode -> m TreeNode
calcNum op t1 t2 = case (t1, t2) of
  (TNLeaf l1, TNLeaf l2) ->
    let v1 = trfValue l1
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
