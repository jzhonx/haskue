{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Eval (
  runIO,
  eval,
)
where

import AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (MonadLogger, runStderrLoggingT)
import Control.Monad.Reader (ReaderT (runReaderT))
import Data.Maybe (catMaybes, fromJust, isJust)
import qualified Data.Set as Set
import Parser (parseCUE)
import Path
import Text.Printf (printf)
import Tree
import Unify (unify)

runIO :: (MonadIO m, MonadError String m) => String -> m TreeCursor
runIO s = runStderrLoggingT $ runStr s

runStr :: (MonadError String m, MonadLogger m) => String -> m TreeCursor
runStr s = do
  parsedE <- parseCUE s
  eval parsedE startPath

eval :: (MonadError String m, MonadLogger m) => Expression -> Path -> m TreeCursor
eval expr path = do
  rootTC <-
    runReaderT
      ( ( do
            r <- evalExpr expr path initTC >>= propUpTCSel StartSelector
            dump $ printf "--- evaluated to rootTC: ---\n%s" (showTreeCursor r)
            r2 <- setOrigNodesTC r
            dump $ printf "--- start resolving links ---"
            res <- evalTC r2
            dump $ printf "--- resolved: ---\n%s" (showTreeCursor res)
            return res
        )
      )
      Config{cfUnify = unify, cfCreateCnstr = True}
  finalized <-
    runReaderT
      (evalTC rootTC)
      Config{cfUnify = unify, cfCreateCnstr = False}
  dump $ printf "--- constraints evaluated: ---\n%s" (showTreeCursor finalized)
  return finalized
 where
  initTC :: TreeCursor
  initTC = (mkTree (TNRoot $ TreeRoot (mkTreeAtom Top Nothing)) Nothing, [])

{- | evalExpr and all expr* should return the same level tree cursor.
Every eval* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the path of the input tree cursor is /a/b, then the output tree cursor should also have /a/b.
-}
evalExpr :: (EvalEnv m) => Expression -> Path -> TreeCursor -> m TreeCursor
evalExpr (ExprUnaryExpr e) = evalUnaryExpr e
evalExpr (ExprBinaryOp op e1 e2) = evalBinary op e1 e2

evalLiteral :: (EvalEnv m) => Literal -> Path -> TreeCursor -> m TreeCursor
evalLiteral (StructLit s) path tc = evalStructLit s path tc
evalLiteral (ListLit l) path tc = evalListLit l path tc
evalLiteral lit path tc =
  let parSel = fromJust $ lastSel path
   in do
        v <- f lit
        insertTCAtom parSel v tc >>= propUpTCSel parSel
 where
  f :: (EvalEnv m) => Literal -> m Atom
  f (StringLit (SimpleStringLit s)) = return $ String s
  f (IntLit i) = return $ Int i
  f (FloatLit a) = return $ Float a
  f (BoolLit b) = return $ Bool b
  f TopLit = return Top
  f BottomLit = return $ Bottom ""
  f NullLit = return Null
  f _ = throwError $ printf "literal %s is not supported" (show lit)

-- | The struct is guaranteed to have unique labels by transform.
evalStructLit :: (EvalEnv m) => [Declaration] -> Path -> TreeCursor -> m TreeCursor
evalStructLit decls path tc = do
  -- create a new block since we are entering a new struct.
  -- It inserts all the field labels to the current scope.
  u <- insertTCScope parSel dedupLabels idSet tc
  v <- foldM evalDecl u decls >>= propUpTCSel parSel
  return v
 where
  parSel = fromJust $ lastSel path

  -- evalField evaluates a declaration in a struct.
  evalDecl :: (EvalEnv m) => TreeCursor -> Declaration -> m TreeCursor
  evalDecl x (Embedding e) =
    do
      -- go up to the parent node.
      par <- propUpTCSel parSel x
      -- Replace the original node with a binary op node, with the left side being the original node and the right side
      -- being a stub.
      updateTCSub
        parSel
        ( mkTree
            ( TNBinaryOp $
                TreeBinaryOp
                  { trbRep = AST.Unify
                  , trbOp = unify
                  , trbArgL = (fst x)
                  , trbArgR = mkTree TNStub Nothing
                  }
            )
            Nothing
        )
        par
      -- evaluate the embedding expression.
      >>= evalExpr e (appendSel (BinOpSelector R) path)
      -- go back to the original node.
      >>= goDownTCSelErr (BinOpSelector L) "cannot go back to original struct"
  evalDecl x (FieldDecl fd) = case fd of
    Field label e ->
      let
        name = fromJust $ fetchLabel label
        fieldPath = appendSel (Path.StringSelector name) path
       in
        evalExpr e fieldPath x

  labels :: [String]
  labels = catMaybes $ map (evalLabel fetchLabel) decls

  idSet = Set.fromList (catMaybes $ map (evalLabel fetchVarLabel) decls)

  dedupLabels =
    snd $
      foldr
        ( \l (s, acc) -> if l `Set.member` s then (s, acc) else (Set.insert l s, l : acc)
        )
        (Set.empty, [])
        labels

  evalLabel :: (Label -> Maybe String) -> Declaration -> Maybe String
  evalLabel f decl = case decl of
    FieldDecl fd -> case fd of
      Field label _ -> f label
    _ -> Nothing

  fetchLabel :: Label -> Maybe String
  fetchLabel (Label (LabelName label)) = case label of
    LabelID ident -> Just ident
    LabelString ls -> Just ls

  fetchVarLabel :: Label -> Maybe String
  fetchVarLabel (Label (LabelName (LabelID var))) = Just var
  fetchVarLabel _ = Nothing

evalListLit :: (EvalEnv m) => AST.ElementList -> Path -> TreeCursor -> m TreeCursor
evalListLit (AST.EmbeddingList es) path tc =
  let
    parSel = fromJust $ lastSel path
    ies = zip [0 ..] es
   in
    do
      u <- insertTCList parSel (length es) tc
      foldM evalElement u ies >>= propUpTCSel parSel
 where
  evalElement :: (EvalEnv m) => TreeCursor -> (Int, AST.Embedding) -> m TreeCursor
  evalElement x (i, e) =
    let
      listPath = appendSel (Path.IndexSelector i) path
     in
      evalExpr e listPath x

evalUnaryExpr :: (EvalEnv m) => UnaryExpr -> Path -> TreeCursor -> m TreeCursor
evalUnaryExpr (UnaryExprPrimaryExpr primExpr) = \path -> evalPrimExpr primExpr path
evalUnaryExpr (UnaryExprUnaryOp op e) = evalUnaryOp op e

builtinOpNameTable :: [(String, Bound)]
builtinOpNameTable = map (\b -> (show b, BdType b)) [minBound :: BdType .. maxBound :: BdType]

evalPrimExpr :: (EvalEnv m) => PrimaryExpr -> Path -> TreeCursor -> m TreeCursor
evalPrimExpr e@(PrimExprOperand op) path tc = case op of
  OpLiteral lit -> evalLiteral lit path tc
  OpExpression expr -> evalExpr expr path tc
  OperandName (Identifier ident) -> case lookup ident builtinOpNameTable of
    Nothing -> lookupVar e ident path tc
    Just b -> do
      let parSel = fromJust $ lastSel path
      pure tc >>= insertTCBound parSel b >>= propUpTCSel parSel
evalPrimExpr e@(PrimExprSelector primExpr sel) path tc =
  evalPrimExpr primExpr path tc
    >>= evalSelector e sel path
evalPrimExpr e@(PrimExprIndex primExpr index) path tc = undefined

{- | Looks up the variable denoted by the name in the current scope or the parent scopes.
If the variable is not atom, a new pending value is created and returned. The reason is that if the referenced var was
updated with a new value, the pending value should be updated with the value.
Parameters:
- var denotes the variable name.
- path is the path to the current expression that contains the selector.
For example, { a: b: x+y }
If the name is "y", and the path is "a.b".
-}
lookupVar :: (EvalEnv m) => PrimaryExpr -> String -> Path -> TreeCursor -> m TreeCursor
lookupVar e var path tc =
  let
    parSel = fromJust $ lastSel path
    notFound = Bottom $ printf "variable %s is not found, path: %s" var (show path)
   in
    do
      dump $ printf "lookupVar: path: %s, looks up var: %s" (show path) var
      res <- searchTCVar (Path.StringSelector var) tc
      case res of
        Nothing ->
          return
            (substTreeNode (TNAtom . TreeAtom $ notFound) (fst tc), snd tc)
        Just _ ->
          insertTCVarLink parSel var (UnaryExprPrimaryExpr e) tc
            >>= propUpTCSel parSel

{- | Evaluates the selector.
Parameters:
- pe is the primary expression.
- sel is the selector.
- path is the path to the current expression that contains the selector.
For example, { a: b: x.y }
If the field is "y", and the path is "a.b", expr is "x.y", the structPath is "x".
-}
evalSelector ::
  (EvalEnv m) => PrimaryExpr -> AST.Selector -> Path -> TreeCursor -> m TreeCursor
evalSelector pe astSel path tc =
  let parSel = fromJust $ lastSel path
      sel = case astSel of
        IDSelector ident -> ident
        AST.StringSelector str -> str
   in do
        insertTCDot parSel (Path.StringSelector sel) (UnaryExprPrimaryExpr pe) tc
        >>= propUpTCSel parSel

-- evalIndex ::
--   (EvalEnv m) => PrimaryExpr -> AST.Index -> Path -> TreeCursor -> m TreeCursor
-- evalIndex pe (AST.Index e) path tc =
--   let parSel = fromJust $ lastSel path
--    in do
--         -- evaluate the index expression.
--         u <- evalExpr e (appendSel (Path.UnaryOpSelector) path) tc
--         insertTCDot parSel (Path.StringSelector sel) (UnaryExprPrimaryExpr pe) tc
--           >>= propUpTCSel parSel

{- | Evaluates the unary operator.
unary operator should only be applied to atoms.
-}
evalUnaryOp :: (EvalEnv m) => UnaryOp -> UnaryExpr -> Path -> TreeCursor -> m TreeCursor
evalUnaryOp op e path tc =
  let parSel = fromJust $ lastSel path
      nextPath = appendSel UnaryOpSelector path
   in do
        pure tc >>= insertTCUnaryOp parSel op (dispUnaryFunc op)
        >>= evalUnaryExpr e nextPath
        >>= propUpTCSel parSel

dispUnaryFunc :: (EvalEnv m) => UnaryOp -> Tree -> TreeCursor -> m TreeCursor
dispUnaryFunc op t tc = do
  unode <- case treeNode t of
    TNAtom ta -> case (op, trAmAtom ta) of
      (Plus, Int i) -> ia i id
      (Plus, Float i) -> fa i id
      (Minus, Int i) -> ia i negate
      (Minus, Float i) -> fa i negate
      (Not, Bool b) -> return $ mkTreeAtom (Bool (not b)) Nothing
      (AST.UnaRelOp uop, _) -> case (uop, trAmAtom ta) of
        (AST.NE, a) -> mkb (BdNE a)
        (AST.LT, Int i) -> mkib BdLT i
        (AST.LT, Float f) -> mkfb BdLT f
        (AST.LE, Int i) -> mkib BdLE i
        (AST.LE, Float f) -> mkfb BdLE f
        (AST.GT, Int i) -> mkib BdGT i
        (AST.GT, Float f) -> mkfb BdGT f
        (AST.GE, Int i) -> mkib BdGE i
        (AST.GE, Float f) -> mkfb BdGE f
        (AST.ReMatch, String p) -> return $ mkTNBounds [BdStrMatch $ BdReMatch p] Nothing
        (AST.ReNotMatch, String p) -> return $ mkTNBounds [BdStrMatch $ BdReNotMatch p] Nothing
        _ -> returnConflict
      _ -> returnConflict
    TNUnaryOp _ -> return $ mkTree (TNUnaryOp $ mkTNUnaryOp op (dispUnaryFunc op) t) Nothing
    TNBinaryOp _ -> return $ mkTree (TNUnaryOp $ mkTNUnaryOp op (dispUnaryFunc op) t) Nothing
    _ -> returnConflict
  return (unode, snd tc)
 where
  conflict :: Atom
  conflict = Bottom $ printf "%s cannot be used for %s" (show t) (show op)

  returnConflict :: (EvalEnv m) => m Tree
  returnConflict = return $ mkTreeAtom conflict Nothing

  ia :: (EvalEnv m) => Integer -> (Integer -> Integer) -> m Tree
  ia a f = return $ mkTreeAtom (Int $ f a) Nothing

  fa :: (EvalEnv m) => Double -> (Double -> Double) -> m Tree
  fa a f = return $ mkTreeAtom (Float $ f a) Nothing

  mkb :: (EvalEnv m) => Bound -> m Tree
  mkb b = return $ mkTNBounds [b] Nothing

  mkib :: (EvalEnv m) => BdNumCmpOp -> Integer -> m Tree
  mkib uop i = return $ mkTNBounds [BdNumCmp $ BdNumCmpCons uop (NumInt i)] Nothing

  mkfb :: (EvalEnv m) => BdNumCmpOp -> Double -> m Tree
  mkfb uop f = return $ mkTNBounds [BdNumCmp $ BdNumCmpCons uop (NumFloat f)] Nothing

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (EvalEnv m) => BinaryOp -> Expression -> Expression -> Path -> TreeCursor -> m TreeCursor
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjunction e1 e2 path tc = evalDisj e1 e2 path tc
evalBinary op e1 e2 path tc =
  let parSel = fromJust $ lastSel path
   in pure tc
        >>= insertTCBinaryOp parSel op (dispBinFunc op)
        >>= (evalExpr e1 $ appendSel (BinOpSelector L) path)
        >>= (evalExpr e2 $ appendSel (BinOpSelector R) path)
        >>= propUpTCSel parSel

dispBinFunc :: (EvalEnv m) => BinaryOp -> Tree -> Tree -> TreeCursor -> m TreeCursor
dispBinFunc op = case op of
  AST.Unify -> unify
  _ -> regBin op

regBin :: (EvalEnv m) => BinaryOp -> Tree -> Tree -> TreeCursor -> m TreeCursor
regBin op t1 t2 tc = do
  node <- regBinDir op (L, t1) (R, t2) tc
  return (substTreeNode (treeNode node) (fst tc), snd tc)

regBinDir :: (EvalEnv m) => BinaryOp -> (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
regBinDir op dt1@(d1, t1) dt2@(d2, t2) tc = do
  dump $
    printf ("regBinDir: path: %s, %s: %s with %s: %s") (show $ pathFromTC tc) (show d1) (show t1) (show d2) (show t2)
  case (treeNode t1, treeNode t2) of
    (TNAtom l1, _) -> regBinLeftAtom op (d1, l1, t1) dt2 tc
    (_, TNAtom l2) -> regBinLeftAtom op (d2, l2, t2) dt1 tc
    (TNScope s1, _) -> regBinLeftScope op (d1, s1, t1) dt2 tc
    (_, TNScope s2) -> regBinLeftScope op (d2, s2, t2) dt1 tc
    (TNDisj dj1, _) -> regBinLeftDisj op (d1, dj1, t1) dt2 tc
    (_, TNDisj dj2) -> regBinLeftDisj op (d2, dj2, t2) dt1 tc
    _ -> regBinOther op dt1 dt2 tc

regBinLeftAtom :: (EvalEnv m) => BinaryOp -> (BinOpDirect, TNAtom, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
regBinLeftAtom op (d1, ta1, t1) (d2, t2) tc = do
  dump $ printf "regBinLeftAtom: %s %s %s" (show ta1) (show op) (show t2)
  if
    | isJust (lookup op cmpOps) -> case treeNode t2 of
        TNAtom ta2 ->
          let
            a2 = trAmAtom ta2
            f :: (Atom -> Atom -> Bool)
            f = fromJust (lookup op cmpOps)
            r = case (a1, a2) of
              (String _, String _) -> Bool $ dirApply f (d1, a1) a2
              (Int _, Int _) -> Bool $ dirApply f (d1, a1) a2
              (Int _, Float _) -> Bool $ dirApply f (d1, a1) a2
              (Float _, Int _) -> Bool $ dirApply f (d1, a1) a2
              (Float _, Float _) -> Bool $ dirApply f (d1, a1) a2
              (Bool _, Bool _) -> Bool $ dirApply f (d1, a1) a2
              (Bottom _, Bottom _) -> Bool $ dirApply f (d1, a1) a2
              (Null, _) -> Bool $ dirApply f (d1, a1) a2
              (_, Null) -> Bool $ dirApply f (d2, a2) a1
              _ -> uncmpAtoms a1 a2
           in
            return $ mkTreeAtom r Nothing
        TNScope _ -> return $ cmpNull a1 t2
        TNList _ -> return $ cmpNull a1 t2
        TNDisj _ -> return $ cmpNull a1 t2
        _ -> regBinOther op (d2, t2) (d1, t1) tc
    | op `elem` arithOps -> case treeNode t2 of
        TNAtom ta2 ->
          let
            r = case op of
              AST.Add -> case (a1, trAmAtom ta2) of
                (Int i1, Int i2) -> Int $ dirApply (+) (d1, i1) i2
                (Int i1, Float i2) -> Float $ dirApply (+) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Float $ dirApply (+) (d1, i1) (fromIntegral i2)
                _ -> mismatch a1 (trAmAtom ta2)
              AST.Sub -> case (a1, trAmAtom ta2) of
                (Int i1, Int i2) -> Int $ dirApply (-) (d1, i1) i2
                (Int i1, Float i2) -> Float $ dirApply (-) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Float $ dirApply (-) (d1, i1) (fromIntegral i2)
                _ -> mismatch a1 (trAmAtom ta2)
              AST.Mul -> case (a1, trAmAtom ta2) of
                (Int i1, Int i2) -> Int $ dirApply (*) (d1, i1) i2
                (Int i1, Float i2) -> Float $ dirApply (*) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Float $ dirApply (*) (d1, i1) (fromIntegral i2)
                _ -> mismatch a1 (trAmAtom ta2)
              AST.Div -> case (a1, trAmAtom ta2) of
                (Int i1, Int i2) -> Float $ dirApply (/) (d1, (fromIntegral i1)) (fromIntegral i2)
                (Int i1, Float i2) -> Float $ dirApply (/) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Float $ dirApply (/) (d1, i1) (fromIntegral i2)
                _ -> mismatch a1 (trAmAtom ta2)
              _ -> mismatch a1 (trAmAtom ta2)
           in
            return $ mkTreeAtom r Nothing
        TNScope _ -> return $ mismatchArith a1 t2
        TNList _ -> return $ mismatchArith a1 t2
        TNDisj _ -> return $ mismatchArith a1 t2
        _ -> regBinOther op (d2, t2) (d1, t1) tc
    | otherwise -> return $ mkTreeAtom (Bottom $ printf "operator %s is not supported" (show op)) Nothing
 where
  a1 = trAmAtom ta1
  cmpOps = [(AST.Equ, (==)), (AST.BinRelOp AST.NE, (/=))]
  arithOps = [AST.Add, AST.Sub, AST.Mul, AST.Div]

  uncmpAtoms :: Atom -> Atom -> Atom
  uncmpAtoms x y = Bottom $ printf "%s and %s are not comparable" (show x) (show y)

  cmpNull :: Atom -> Tree -> Tree
  cmpNull a t =
    if
      -- There is no way for a non-atom to be compared with a non-null atom.
      | a /= Null -> mkTreeAtom (mismatch a t) Nothing
      | op == AST.Equ -> mkTreeAtom (Bool False) Nothing
      | op == AST.BinRelOp AST.NE -> mkTreeAtom (Bool True) Nothing
      | otherwise -> mkTreeAtom (Bottom $ printf "operator %s is not supported" (show op)) Nothing

  mismatchArith :: (Show a, Show b) => a -> b -> Tree
  mismatchArith x y = mkTreeAtom (mismatch x y) Nothing

dirApply :: (a -> a -> b) -> (BinOpDirect, a) -> a -> b
dirApply f (di1, i1) i2 = if di1 == L then f i1 i2 else f i2 i1

mismatch :: (Show a, Show b) => a -> b -> Atom
mismatch x y = Bottom $ printf "%s can not be used with %s and %s" (show x) (show y)

regBinLeftScope ::
  (EvalEnv m) => BinaryOp -> (BinOpDirect, TNScope, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
regBinLeftScope op (d1, _, t1) (d2, t2) tc = case treeNode t2 of
  TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1) tc
  _ -> return (mkTreeAtom (mismatch t1 t2) Nothing)

regBinLeftDisj ::
  (EvalEnv m) => BinaryOp -> (BinOpDirect, TNDisj, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
regBinLeftDisj op (d1, dj1, t1) (d2, t2) tc = case dj1 of
  TreeDisj{trdDefault = Just d} -> regBinDir op (d1, d) (d2, t2) tc
  _ -> case treeNode t2 of
    TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1) tc
    _ -> return (mkTreeAtom (mismatch t1 t2) Nothing)

regBinOther :: (EvalEnv m) => BinaryOp -> (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
regBinOther op (d1, t1) (d2, t2) tc = case (treeNode t1, t2) of
  (TNUnaryOp _, _) -> evalOrDelay
  (TNBinaryOp _, _) -> evalOrDelay
  (TNLink _, _) -> evalOrDelay
  (TNRefCycleVar, _) -> evalOrDelay
  (TNConstraint c, _) -> do
    na <- regBinDir op (d1, mkTree (TNAtom $ trCnAtom c) Nothing) (d2, t2) tc
    case treeNode na of
      TNAtom atom -> return $ substTreeNode (TNConstraint $ updateTNConstraintAtom atom c) (fst tc)
      _ -> undefined
  _ -> return (mkTreeAtom (Bottom mismatchErr) Nothing)
 where
  -- evalOrDelay tries to evaluate the left side of the binary operation. If it is not possible to evaluate it, it
  -- returns a delayed evaluation.
  evalOrDelay :: (EvalEnv m) => m Tree
  evalOrDelay =
    let unevaledTC = mkSubTC (BinOpSelector d1) t1 tc
     in do
          dump $ printf "regBinOther: path: %s, evaluating:\n%s" (show $ pathFromTC unevaledTC) (show (fst unevaledTC))
          x <- evalTC unevaledTC
          dump $ printf "regBinOther: %s, is evaluated to:\n%s" (show t1) (show $ fst x)
          case treeNode (fst x) of
            TNAtom TreeAtom{trAmAtom = Top} -> delay
            TNAtom a1 -> regBinLeftAtom op (d1, a1, fst x) (d2, t2) tc
            TNDisj dj1 -> regBinLeftDisj op (d1, dj1, fst x) (d2, t2) tc
            TNScope s1 -> regBinLeftScope op (d1, s1, fst x) (d2, t2) tc
            TNList _ -> undefined
            TNConstraint _ -> regBinOther op (d1, fst x) (d2, t2) tc
            _ -> delay

  delay :: (EvalEnv m) => m Tree
  delay =
    let v = substTreeNode (TNBinaryOp $ mkTNBinaryOpDir op (regBin op) (d1, t1) (d2, t2)) (fst tc)
     in do
          dump $ printf "regBinOther: %s is incomplete, delaying to %s" (show t1) (show v)
          return v

  mismatchErr :: String
  mismatchErr = printf "values %s and %s cannot be used for %s" (show t1) (show t2) (show op)

data DisjItem = DisjDefault Tree | DisjRegular Tree

instance Show DisjItem where
  show (DisjDefault t) = show t
  show (DisjRegular t) = show t

evalDisj :: (EvalEnv m) => Expression -> Expression -> Path -> TreeCursor -> m TreeCursor
evalDisj e1 e2 path tc = do
  u <- insertTCDisj parSel evalDisjAdapt tc
  v <- case (e1, e2) of
    (ExprUnaryExpr (UnaryExprUnaryOp Star se1), ExprUnaryExpr (UnaryExprUnaryOp Star se2)) ->
      pure u
        >>= evalUnaryExpr se1 (appendSel (BinOpSelector L) path)
        >>= evalUnaryExpr se2 (appendSel (BinOpSelector R) path)
        >>= propUpTCSel parSel
    (ExprUnaryExpr (UnaryExprUnaryOp Star se1), _) ->
      pure u
        >>= evalUnaryExpr se1 (appendSel (BinOpSelector L) path)
        >>= evalExpr e2 (appendSel (BinOpSelector R) path)
        >>= propUpTCSel parSel
    (_, ExprUnaryExpr (UnaryExprUnaryOp Star se2)) ->
      pure u
        >>= evalExpr e1 (appendSel (BinOpSelector L) path)
        >>= evalUnaryExpr se2 (appendSel (BinOpSelector R) path)
        >>= propUpTCSel parSel
    (_, _) ->
      pure u
        >>= evalExpr e1 (appendSel (BinOpSelector L) path)
        >>= evalExpr e2 (appendSel (BinOpSelector R) path)
        >>= propUpTCSel parSel
  dump $ printf "evalDisj: tree:\n%s" (show $ fst v)
  return v
 where
  parSel = fromJust $ lastSel path

  evalDisjAdapt :: (EvalEnv m) => Tree -> Tree -> TreeCursor -> m TreeCursor
  evalDisjAdapt unt1 unt2 x = do
    t1 <- evalSub (BinOpSelector L) unt1 x
    t2 <- evalSub (BinOpSelector R) unt2 x
    if not (isValueNode (treeNode t1)) || not (isValueNode (treeNode t2))
      then do
        dump $ printf "evalDisjAdapt: %s, %s are not value nodes" (show t1) (show t2)
        return x
      else do
        unode <- case (e1, e2) of
          (ExprUnaryExpr (UnaryExprUnaryOp Star _), ExprUnaryExpr (UnaryExprUnaryOp Star _)) ->
            evalDisjPair (DisjDefault t1) (DisjDefault t2)
          (ExprUnaryExpr (UnaryExprUnaryOp Star _), _) ->
            evalDisjPair (DisjDefault t1) (DisjRegular t2)
          (_, ExprUnaryExpr (UnaryExprUnaryOp Star _)) ->
            evalDisjPair (DisjRegular t1) (DisjDefault t2)
          (_, _) -> evalDisjPair (DisjRegular t1) (DisjRegular t2)
        return (substTreeNode (treeNode unode) (fst x), snd x)

  evalSub :: (EvalEnv m) => Path.Selector -> Tree -> TreeCursor -> m Tree
  evalSub sel t x =
    let unevaledTC = mkSubTC sel t x
     in do
          dump $ printf "evalDisj: path: %s, evaluating:\n%s" (show $ pathFromTC unevaledTC) (show (fst unevaledTC))
          u <- evalTC unevaledTC
          dump $ printf "evalDisj: %s, is evaluated to:\n%s" (show t) (show $ fst u)
          return $ fst u

  -- evalDisjPair is used to evaluate a disjunction whose both sides are evaluated.
  evalDisjPair :: (EvalEnv m) => DisjItem -> DisjItem -> m Tree
  evalDisjPair i1 i2 = case (i1, i2) of
    (DisjDefault v1, _) -> do
      dump $ printf "evalDisjPair: *: %s, r: %s" (show v1) (show i2)
      t <- evalLeftDefault (\(df1, ds1, df2, ds2) -> newDisj df1 ds1 df2 ds2) v1 i2
      dump $ printf "evalDisjPair: *: %s, r: %s, resulting to:\n%s" (show v1) (show i2) (show t)
      return t
    -- reverse v2 r1 and also the order to the disjCons.
    (DisjRegular _, DisjDefault v2) -> do
      evalLeftDefault (\(df2, ds2, df1, ds1) -> newDisj df1 ds1 df2 ds2) v2 i1
    (DisjRegular v1, DisjRegular v2) -> do
      dump $ printf "evalDisjPair: both regulars v1: %s, v2: %s" (show v1) (show v2)
      r <- evalRegularDisj v1 v2
      dump $ printf "evalDisjPair: both regulars results: %s" (show r)
      return r

  -- evalLeftDefault is used to evaluate a disjunction whose left side is a default.
  -- the first argument is a function that takes the four lists of values and returns a disjunction.
  evalLeftDefault ::
    (MonadError String m) => ((Maybe Tree, [Tree], Maybe Tree, [Tree]) -> m Tree) -> Tree -> DisjItem -> m Tree
  -- Below is rule M2 and M3. We eliminate the defaults from the right side.
  evalLeftDefault disjCons (Tree{treeNode = TNDisj dj1}) (DisjRegular (Tree{treeNode = TNDisj dj2})) =
    disjCons ((trdDefault dj1), (trdDisjuncts dj1), Nothing, (trdDisjuncts dj2))
  -- Below is rule M1.
  evalLeftDefault disjCons v1 (DisjRegular (Tree{treeNode = TNDisj dj2})) =
    disjCons (Just v1, [v1], (trdDefault dj2), (trdDisjuncts dj2))
  evalLeftDefault disjCons v1 (DisjRegular v2) =
    disjCons (Just v1, [v1], Nothing, [v2])
  evalLeftDefault disjCons v1 (DisjDefault v2) =
    disjCons (Nothing, [v1], Nothing, [v2])

  -- evalFullDisj is used to evaluate a disjunction whose both sides are regular.
  -- Rule: D1, D2
  evalRegularDisj :: (EvalEnv m) => Tree -> Tree -> m Tree
  evalRegularDisj (Tree{treeNode = TNDisj dj1}) (Tree{treeNode = TNDisj dj2}) =
    newDisj (trdDefault dj1) (trdDisjuncts dj1) (trdDefault dj2) (trdDisjuncts dj2)
  evalRegularDisj (Tree{treeNode = TNDisj dj}) y = newDisj (trdDefault dj) (trdDisjuncts dj) Nothing [y]
  evalRegularDisj x (Tree{treeNode = TNDisj dj}) = newDisj Nothing [x] (trdDefault dj) (trdDisjuncts dj)
  -- Rule D0
  evalRegularDisj x y = newDisj Nothing [x] Nothing [y]

  -- dedupAppend appends unique elements in ys to the xs list, but only if they are not already in xs.
  -- xs and ys are guaranteed to be unique.
  dedupAppend :: [Tree] -> [Tree] -> [Tree]
  dedupAppend xs ys = xs ++ foldr (\y acc -> if y `elem` xs then acc else y : acc) [] ys

  newDisj :: (EvalEnv m) => Maybe Tree -> [Tree] -> Maybe Tree -> [Tree] -> m Tree
  newDisj df1 ds1 df2 ds2 =
    let
      subTree :: Maybe Tree
      subTree = case map fromJust (filter isJust [df1, df2]) of
        x : [] -> Just x
        x : y : [] -> Just $ mkTreeDisj Nothing [x, y] Nothing
        _ -> Nothing
     in
      return $ mkTreeDisj subTree (dedupAppend ds1 ds2) Nothing
