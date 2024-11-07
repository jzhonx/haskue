{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module EvalExpr where

import AST
import Control.Monad (foldM)
import Control.Monad.Except (throwError)
import qualified Data.Map.Strict as Map
import Path
import Reduction
import Text.Printf (printf)
import Util
import Value.Tree

type EvalEnv m = EvalEnvState (Context Tree) m Config

{- | evalExpr and all expr* should return the same level tree cursor.
The label and the evaluated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every eval* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the path of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
evalExpr :: (EvalEnv m) => Expression -> m Tree
evalExpr (ExprUnaryExpr e) = evalUnaryExpr e
evalExpr (ExprBinaryOp op e1 e2) = evalBinary op e1 e2

evalLiteral :: (EvalEnv m) => Literal -> m Tree
evalLiteral (StructLit s) = evalStructLit s
evalLiteral (ListLit l) = evalListLit l
evalLiteral lit = return v
 where
  v = case lit of
    StringLit (SimpleStringLit s) -> mkAtomTree $ String s
    IntLit i -> mkAtomTree $ Int i
    FloatLit a -> mkAtomTree $ Float a
    BoolLit b -> mkAtomTree $ Bool b
    NullLit -> mkAtomTree Null
    TopLit -> mkNewTree TNTop
    BottomLit -> mkBottomTree ""

-- | The struct is guaranteed to have unique labels by transform.
evalStructLit :: (EvalEnv m) => [Declaration] -> m Tree
evalStructLit decls = do
  (struct, ts) <- foldM evalDecl (emptyStruct, []) decls
  let v =
        if null ts
          then mkNewTree (TNStruct struct)
          else
            foldl (\acc t -> mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify acc t)) (mkNewTree (TNStruct struct)) ts
  return v
 where
  --  Evaluates a declaration in a struct.
  --  It returns the updated struct and the list of to be unified trees, which are embeddings.
  evalDecl :: (EvalEnv m) => (Struct Tree, [Tree]) -> Declaration -> m (Struct Tree, [Tree])
  evalDecl (scp, ts) (Embedding e) = do
    v <- evalExpr e
    return (scp, v : ts)
  evalDecl (struct, ts) (FieldDecl fd) = case fd of
    Field ls e -> do
      sfa <- evalFdLabels ls e
      let newStruct = insertUnifyStruct sfa struct
      return (newStruct, ts)

  evalFdLabels :: (EvalEnv m) => [AST.Label] -> AST.Expression -> m (StructElemAdder Tree)
  evalFdLabels lbls e =
    case lbls of
      [] -> throwError "empty labels"
      [l1] ->
        do
          logDebugStr $ printf "evalFdLabels: lb1: %s" (show l1)
          val <- evalExpr e
          adder <- mkAdder l1 val
          logDebugStr $ printf "evalFdLabels: adder: %s" (show adder)
          return adder
      l1 : l2 : rs ->
        do
          logDebugStr $ printf "evalFdLabels, nested: lb1: %s" (show l1)
          sf2 <- evalFdLabels (l2 : rs) e
          let val = mkNewTree . TNStruct $ mkStructFromAdders [sf2]
          adder <- mkAdder l1 val
          logDebugStr $ printf "evalFdLabels, nested: adder: %s" (show adder)
          return adder

  mkAdder :: (EvalEnv m) => Label -> Tree -> m (StructElemAdder Tree)
  mkAdder (Label le) val = case le of
    AST.LabelName ln c ->
      let attr = LabelAttr{lbAttrType = slFrom c, lbAttrIsVar = isVar ln}
       in case ln of
            (sselFrom -> Just key) -> return $ Static key (StaticStructField val attr)
            (dselFrom -> Just se) -> do
              selTree <- evalExpr se
              return $ Dynamic (DynamicStructField attr selTree se val)
            _ -> throwError "invalid label"
    AST.LabelPattern pe -> do
      pat <- evalExpr pe
      return (Pattern pat val)

  -- Returns the label name and the whether the label is static.
  sselFrom :: LabelName -> Maybe Path.StructSelector
  sselFrom (LabelID ident) = Just (Path.StringSelector ident)
  sselFrom (LabelString ls) = Just (Path.StringSelector ls)
  sselFrom _ = Nothing

  dselFrom :: LabelName -> Maybe AST.Expression
  dselFrom (LabelNameExpr e) = Just e
  dselFrom _ = Nothing

  slFrom :: AST.LabelConstraint -> StructLabelType
  slFrom c = case c of
    RegularLabel -> SLRegular
    OptionalLabel -> SLOptional
    RequiredLabel -> SLRequired

  isVar :: LabelName -> Bool
  isVar (LabelID _) = True
  -- Labels which are quoted or expressions are not variables.
  isVar _ = False

-- Insert a new field into the struct. If the field is already in the struct, then unify the field with the new field.
insertUnifyStruct ::
  StructElemAdder Tree -> Struct Tree -> Struct Tree
insertUnifyStruct adder struct = case adder of
  (Static sel sf) -> case subs Map.!? sel of
    Just extSF ->
      let
        unifySFOp =
          StaticStructField
            { ssfField = mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify (ssfField extSF) (ssfField sf))
            , ssfAttr = mergeAttrs (ssfAttr extSF) (ssfAttr sf)
            }
       in
        struct{stcSubs = Map.insert sel unifySFOp subs}
    Nothing ->
      struct
        { stcOrdLabels = stcOrdLabels struct ++ [sel]
        , stcSubs = Map.insert sel sf subs
        }
  (Dynamic dsf) -> struct{stcPendSubs = stcPendSubs struct ++ [DynamicField dsf]}
  (Pattern pattern val) -> struct{stcPendSubs = stcPendSubs struct ++ [PatternField pattern val]}
 where
  subs = stcSubs struct

evalListLit :: (EvalEnv m) => AST.ElementList -> m Tree
evalListLit (AST.EmbeddingList es) = do
  xs <- mapM evalExpr es
  return $ mkListTree xs

evalUnaryExpr :: (EvalEnv m) => UnaryExpr -> m Tree
evalUnaryExpr (UnaryExprPrimaryExpr primExpr) = evalPrimExpr primExpr
evalUnaryExpr (UnaryExprUnaryOp op e) = evalUnaryOp op e

builtinOpNameTable :: [(String, Bound)]
builtinOpNameTable = map (\b -> (show b, BdType b)) [minBound :: BdType .. maxBound :: BdType]

evalPrimExpr :: (EvalEnv m) => PrimaryExpr -> m Tree
evalPrimExpr e@(PrimExprOperand op) = case op of
  OpLiteral lit -> evalLiteral lit
  OpExpression expr -> evalExpr expr
  OperandName (Identifier ident) -> case lookup ident builtinOpNameTable of
    Nothing -> mkVarLinkTree ident (AST.UnaryExprPrimaryExpr e)
    Just b -> return $ mkBoundsTree [b]
evalPrimExpr e@(PrimExprSelector primExpr sel) = do
  p <- evalPrimExpr primExpr
  evalSelector e sel p
evalPrimExpr e@(PrimExprIndex primExpr idx) = do
  p <- evalPrimExpr primExpr
  evalIndex e idx p

{- | Evaluates the selector.
Parameters:
- pe is the primary expression.
- sel is the selector.
- path is the path to the current expression that contains the selector.
For example, { a: b: x.y }
If the field is "y", and the path is "a.b", expr is "x.y", the structPath is "x".
-}
evalSelector ::
  (EvalEnv m) => PrimaryExpr -> AST.Selector -> Tree -> m Tree
evalSelector pe astSel tree =
  return $
    mkIndexFuncTree tree (mkAtomTree (String sel)) (UnaryExprPrimaryExpr pe)
 where
  sel = case astSel of
    IDSelector ident -> ident
    AST.StringSelector str -> str

evalIndex ::
  (EvalEnv m) => PrimaryExpr -> AST.Index -> Tree -> m Tree
evalIndex pe (AST.Index e) tree = do
  sel <- evalExpr e
  return $ mkIndexFuncTree tree sel (UnaryExprPrimaryExpr pe)

{- | Evaluates the unary operator.
unary operator should only be applied to atoms.
-}
evalUnaryOp :: (EvalEnv m) => UnaryOp -> UnaryExpr -> m Tree
evalUnaryOp op e = do
  t <- evalUnaryExpr e
  return $ mkNewTree (TNFunc $ mkUnaryOp op (dispUnaryFunc op) t)

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (EvalEnv m) => BinaryOp -> Expression -> Expression -> m Tree
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjunction e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  return $ mkNewTree (TNFunc $ mkBinaryOp op (dispBinFunc op) lt rt)

evalDisj :: (EvalEnv m) => Expression -> Expression -> m Tree
evalDisj e1 e2 = do
  (lt, rt) <- case (e1, e2) of
    (ExprUnaryExpr (UnaryExprUnaryOp Star se1), ExprUnaryExpr (UnaryExprUnaryOp Star se2)) -> do
      l <- evalUnaryExpr se1
      r <- evalUnaryExpr se2
      return (l, r)
    (ExprUnaryExpr (UnaryExprUnaryOp Star se1), _) -> do
      l <- evalUnaryExpr se1
      r <- evalExpr e2
      return (l, r)
    (_, ExprUnaryExpr (UnaryExprUnaryOp Star se2)) -> do
      l <- evalExpr e1
      r <- evalUnaryExpr se2
      return (l, r)
    (_, _) -> do
      l <- evalExpr e1
      r <- evalExpr e2
      return (l, r)
  return $ mkNewTree (TNFunc $ mkBinaryOp AST.Disjunction evalDisjAdapt lt rt)
 where
  evalDisjAdapt :: (TreeMonad s m) => Tree -> Tree -> m Bool
  evalDisjAdapt unt1 unt2 = do
    t1 <- evalFuncArg binOpLeftSelector unt1 False
    t2 <- evalFuncArg binOpRightSelector unt2 False
    if not (isTreeValue t1) || not (isTreeValue t2)
      then do
        logDebugStr $ printf "evalDisjAdapt: %s, %s are not value nodes, delay" (show t1) (show t2)
        return False
      else do
        u <- case (e1, e2) of
          (AST.ExprUnaryExpr (AST.UnaryExprUnaryOp AST.Star _), AST.ExprUnaryExpr (AST.UnaryExprUnaryOp AST.Star _)) ->
            evalDisjPair (DisjDefault t1) (DisjDefault t2)
          (AST.ExprUnaryExpr (AST.UnaryExprUnaryOp AST.Star _), _) ->
            evalDisjPair (DisjDefault t1) (DisjRegular t2)
          (_, AST.ExprUnaryExpr (AST.UnaryExprUnaryOp AST.Star _)) ->
            evalDisjPair (DisjRegular t1) (DisjDefault t2)
          (_, _) -> evalDisjPair (DisjRegular t1) (DisjRegular t2)
        logDebugStr $ printf "evalDisjAdapt: evaluated to %s" (show u)
        putTMTree u
        return True
