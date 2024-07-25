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
import qualified Data.Map.Strict as Map
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
  eval parsedE

-- (ExtendTCLabel Path.StartSelector defaultLabelAttr)

eval :: (MonadError String m, MonadLogger m) => Expression -> m TreeCursor
eval expr = do
  rootTC <-
    runReaderT
      ( do
          root <- evalExpr expr
          -- >>= propUpTCSel (exlSelector lb)
          dump $ printf "--- evaluated to rootTC: ---\n%s" (show root)
          let rootTC = (mkNewTree (TNRoot $ TreeRoot root), [])
          r2 <- setOrigNodesTC rootTC
          dump $ printf "--- start resolving links ---"
          res <- evalTC r2
          dump $ printf "--- resolved: ---\n%s" (showTreeCursor res)
          return res
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
  initTC = (mkNewTree (TNRoot $ TreeRoot mkStub), [])

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
  -- >>= propUpTCSel (exlSelector lb)

  v = case lit of
    StringLit (SimpleStringLit s) -> mkTreeAtom $ String s
    IntLit i -> mkTreeAtom $ Int i
    FloatLit a -> mkTreeAtom $ Float a
    BoolLit b -> mkTreeAtom $ Bool b
    NullLit -> mkTreeAtom $ Null
    TopLit -> mkTreeAtom $ Top
    BottomLit -> mkBottom ""

-- | The struct is guaranteed to have unique labels by transform.
evalStructLit :: (EvalEnv m) => [Declaration] -> m Tree
evalStructLit decls = do
  (scope, ts) <- foldM evalDecl (emptyTNScope, []) decls
  let v =
        if null ts
          then mkNewTree (TNScope scope)
          else
            foldl (\acc t -> mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify acc t)) (mkNewTree (TNScope scope)) ts
  return v
 where
  --  Evaluates a declaration in a struct.
  evalDecl :: (EvalEnv m) => (TNScope, [Tree]) -> Declaration -> m (TNScope, [Tree])
  evalDecl acc (Embedding e) =
    do
      v <- evalExpr e
      return (fst acc, v : snd acc)
  evalDecl (scope, ts) (FieldDecl fd) = case fd of
    Field ls e -> do
      (sel, attr, t) <- evalFdLabels ls e
      let
        extSubMaybe = Map.lookup sel (trsSubs scope)
        newSub =
          if isJust extSubMaybe
            then mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify (fromJust extSubMaybe) t)
            else t
        newAttr =
          if isJust extSubMaybe
            then mergeAttrs attr ((trsAttrs scope) Map.! sel)
            else attr
        newScope = insertScopeSub scope sel (Just newAttr) newSub
      return (newScope, ts)

  evalFdLabels :: (EvalEnv m) => [AST.Label] -> AST.Expression -> m (ScopeSelector, LabelAttr, Tree)
  evalFdLabels lbls e =
    case lbls of
      [] -> throwError "empty labels"
      l1 : [] ->
        let
          (lb1, attr1) = slFrom l1
          attr = LabelAttr{lbAttrType = attr1, lbAttrIsVar = isVar lb1}
         in
          do
            dump $ printf "evalFdLabels: lb1: %s" (show lb1)
            key <- sselFrom lb1
            dump $
              printf "evalFdLabels: key: %s, e: %s" (show key) (show e)
            sub <- evalExpr e
            return (key, attr, sub)
      l1 : l2 : rs ->
        do
          let
            (lb1, attr1) = slFrom l1
            attr = LabelAttr{lbAttrType = attr1, lbAttrIsVar = isVar lb1}
          key <- sselFrom lb1
          (key2, attr2, sub2) <- evalFdLabels (l2 : rs) e
          let sub = mkScope [key2] [(key2, attr2, sub2)]
          return (key, attr, sub)

  sselFrom :: (EvalEnv m) => LabelName -> m Path.ScopeSelector
  sselFrom (LabelID ident) = return $ Path.StringSelector ident
  sselFrom (LabelString ls) = return $ Path.StringSelector ls
  sselFrom (LabelNameExpr e) =
    do
      -- Use the current label as the label for the expression.
      t <- evalExpr e
      case treeNode t of
        TNAtom (TreeAtom (String s)) -> return $ Path.StringSelector s
        _ -> throwError $ printf "label name expression is not a string, %s" (show t)

  slFrom :: Label -> (LabelName, ScopeLabelType)
  slFrom l = case l of
    Label le -> case le of
      RegularLabel ln -> (ln, SLRegular)
      OptionalLabel ln -> (ln, SLOptional)
      RequiredLabel ln -> (ln, SLRequired)

  isVar :: LabelName -> Bool
  isVar (LabelID _) = True
  isVar _ = False

evalListLit :: (EvalEnv m) => AST.ElementList -> m Tree
evalListLit (AST.EmbeddingList es) = do
  xs <- mapM evalExpr es
  return $ mkList xs

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
    Nothing ->
      let
        tarSel = Path.ScopeSelector $ Path.StringSelector ident
        tarPath = Path [tarSel]
       in
        return $ mkNewTree (TNLink $ TreeLink{trlTarget = tarPath, trlExpr = AST.UnaryExprPrimaryExpr e})
    Just b -> return $ mkBounds [b]
evalPrimExpr e@(PrimExprSelector primExpr sel) = do
  p <- evalPrimExpr primExpr
  evalSelector e sel p
evalPrimExpr e@(PrimExprIndex primExpr index) = do
  p <- evalPrimExpr primExpr
  evalIndex e index p

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
evalSelector pe astSel t =
  indexBySel (Path.ScopeSelector $ Path.StringSelector sel) (UnaryExprPrimaryExpr pe) t
 where
  sel = case astSel of
    IDSelector ident -> ident
    AST.StringSelector str -> str

evalIndex ::
  (EvalEnv m) => PrimaryExpr -> AST.Index -> Tree -> m Tree
evalIndex pe (AST.Index e) t = do
  sel <- evalExpr e
  indexByTree sel (UnaryExprPrimaryExpr pe) t

{- | Evaluates the unary operator.
unary operator should only be applied to atoms.
-}
evalUnaryOp :: (EvalEnv m) => UnaryOp -> UnaryExpr -> m Tree
evalUnaryOp op e = do
  t <- evalUnaryExpr e
  return $ mkNewTree (TNFunc $ mkUnaryOp op (dispUnaryFunc op) t)

dispUnaryFunc :: (EvalEnv m) => UnaryOp -> Tree -> TreeCursor -> m TreeCursor
dispUnaryFunc op t tc = do
  unode <- case treeNode t of
    TNAtom ta -> case (op, trAmAtom ta) of
      (Plus, Int i) -> ia i id
      (Plus, Float i) -> fa i id
      (Minus, Int i) -> ia i negate
      (Minus, Float i) -> fa i negate
      (Not, Bool b) -> return $ mkTreeAtom (Bool (not b))
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
        (AST.ReMatch, String p) -> return $ mkBounds [BdStrMatch $ BdReMatch p]
        (AST.ReNotMatch, String p) -> return $ mkBounds [BdStrMatch $ BdReNotMatch p]
        _ -> returnConflict
      _ -> returnConflict
    -- The unary op is operating on a non-atom.
    TNFunc _ -> return $ mkNewTree (TNFunc $ mkUnaryOp op (dispUnaryFunc op) t)
    _ -> returnConflict
  return (unode, snd tc)
 where
  conflict :: Tree
  conflict = mkBottom $ printf "%s cannot be used for %s" (show t) (show op)

  returnConflict :: (EvalEnv m) => m Tree
  returnConflict = return conflict

  ia :: (EvalEnv m) => Integer -> (Integer -> Integer) -> m Tree
  ia a f = return $ mkTreeAtom (Int $ f a)

  fa :: (EvalEnv m) => Double -> (Double -> Double) -> m Tree
  fa a f = return $ mkTreeAtom (Float $ f a)

  mkb :: (EvalEnv m) => Bound -> m Tree
  mkb b = return $ mkBounds [b]

  mkib :: (EvalEnv m) => BdNumCmpOp -> Integer -> m Tree
  mkib uop i = return $ mkBounds [BdNumCmp $ BdNumCmpCons uop (NumInt i)]

  mkfb :: (EvalEnv m) => BdNumCmpOp -> Double -> m Tree
  mkfb uop f = return $ mkBounds [BdNumCmp $ BdNumCmpCons uop (NumFloat f)]

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (EvalEnv m) => BinaryOp -> Expression -> Expression -> m Tree
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjunction e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  return $ mkNewTree (TNFunc $ mkBinaryOp op (dispBinFunc op) lt rt)

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
    (TNBottom _, _) -> return t1
    (_, TNBottom _) -> return t2
    (TNAtom l1, _) -> regBinLeftAtom op (d1, l1, t1) dt2 tc
    (_, TNAtom l2) -> regBinLeftAtom op (d2, l2, t2) dt1 tc
    (TNScope s1, _) -> regBinLeftScope op (d1, s1, t1) dt2 tc
    (_, TNScope s2) -> regBinLeftScope op (d2, s2, t2) dt1 tc
    (TNDisj dj1, _) -> regBinLeftDisj op (d1, dj1, t1) dt2 tc
    (_, TNDisj dj2) -> regBinLeftDisj op (d2, dj2, t2) dt1 tc
    _ -> regBinOther op dt1 dt2 tc

regBinLeftAtom :: (EvalEnv m) => BinaryOp -> (BinOpDirect, TNAtom, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
regBinLeftAtom op (d1, ta1, t1) (d2, t2) tc = do
  dump $ printf "regBinLeftAtom: %s (%s: %s) (%s)" (show op) (show d1) (show ta1) (show t2)
  if
    | isJust (lookup op cmpOps) -> case treeNode t2 of
        TNAtom ta2 ->
          let
            a2 = trAmAtom ta2
            f :: (Atom -> Atom -> Bool)
            f = fromJust (lookup op cmpOps)
            r = case (a1, a2) of
              (String _, String _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Int _, Int _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Int _, Float _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Float _, Int _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Float _, Float _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Bool _, Bool _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Null, _) -> Right . Bool $ dirApply f (d1, a1) a2
              (_, Null) -> Right . Bool $ dirApply f (d2, a2) a1
              _ -> Left $ uncmpAtoms a1 a2
           in
            case r of
              Right b -> return $ mkTreeAtom b
              Left err -> return err
        TNScope _ -> return $ cmpNull a1 t2
        TNList _ -> return $ cmpNull a1 t2
        TNDisj _ -> return $ cmpNull a1 t2
        _ -> regBinOther op (d2, t2) (d1, t1) tc
    | op `elem` arithOps -> case treeNode t2 of
        TNAtom ta2 ->
          let
            r = case op of
              AST.Add -> case (a1, trAmAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (+) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (+) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (+) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch a1 (trAmAtom ta2)
              AST.Sub -> case (a1, trAmAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (-) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (-) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (-) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch a1 (trAmAtom ta2)
              AST.Mul -> case (a1, trAmAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (*) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (*) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (*) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch a1 (trAmAtom ta2)
              AST.Div -> case (a1, trAmAtom ta2) of
                (Int i1, Int i2) -> Right . Float $ dirApply (/) (d1, (fromIntegral i1)) (fromIntegral i2)
                (Int i1, Float i2) -> Right . Float $ dirApply (/) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (/) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch a1 (trAmAtom ta2)
              _ -> Left $ mismatch a1 (trAmAtom ta2)
           in
            case r of
              Right b -> return $ mkTreeAtom b
              Left err -> return err
        TNScope _ -> return $ mismatchArith a1 t2
        TNList _ -> return $ mismatchArith a1 t2
        TNDisj _ -> return $ mismatchArith a1 t2
        _ -> regBinOther op (d2, t2) (d1, t1) tc
    | otherwise -> return $ mkBottom $ printf "operator %s is not supported" (show op)
 where
  a1 = trAmAtom ta1
  cmpOps = [(AST.Equ, (==)), (AST.BinRelOp AST.NE, (/=))]
  arithOps = [AST.Add, AST.Sub, AST.Mul, AST.Div]

  uncmpAtoms :: Atom -> Atom -> Tree
  uncmpAtoms x y = mkBottom $ printf "%s and %s are not comparable" (show x) (show y)

  cmpNull :: Atom -> Tree -> Tree
  cmpNull a t =
    if
      -- There is no way for a non-atom to be compared with a non-null atom.
      | a /= Null -> mismatch a t
      | op == AST.Equ -> mkTreeAtom (Bool False)
      | op == AST.BinRelOp AST.NE -> mkTreeAtom (Bool True)
      | otherwise -> mkBottom $ printf "operator %s is not supported" (show op)

  mismatchArith :: (Show a, Show b) => a -> b -> Tree
  mismatchArith x y = mismatch x y

dirApply :: (a -> a -> b) -> (BinOpDirect, a) -> a -> b
dirApply f (di1, i1) i2 = if di1 == L then f i1 i2 else f i2 i1

mismatch :: (Show a, Show b) => a -> b -> Tree
mismatch x y = mkBottom $ printf "%s can not be used with %s and %s" (show x) (show y)

regBinLeftScope ::
  (EvalEnv m) => BinaryOp -> (BinOpDirect, TNScope, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
regBinLeftScope op (d1, _, t1) (d2, t2) tc = case treeNode t2 of
  TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1) tc
  _ -> return (mismatch t1 t2)

regBinLeftDisj ::
  (EvalEnv m) => BinaryOp -> (BinOpDirect, TNDisj, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
regBinLeftDisj op (d1, dj1, t1) (d2, t2) tc = case dj1 of
  TreeDisj{trdDefault = Just d} -> regBinDir op (d1, d) (d2, t2) tc
  _ -> case treeNode t2 of
    TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1) tc
    _ -> return (mismatch t1 t2)

regBinOther :: (EvalEnv m) => BinaryOp -> (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m Tree
regBinOther op (d1, t1) (d2, t2) tc = case (treeNode t1, t2) of
  (TNFunc _, _) -> evalOrDelay
  (TNLink _, _) -> evalOrDelay
  (TNRefCycleVar, _) -> evalOrDelay
  (TNConstraint c, _) -> do
    na <- regBinDir op (d1, mkNewTree (TNAtom $ trCnAtom c)) (d2, t2) tc
    case treeNode na of
      TNAtom atom -> return $ substTreeNode (TNConstraint $ updateTNConstraintAtom atom c) (fst tc)
      _ -> undefined
  _ -> return (mkBottom mismatchErr)
 where
  -- evalOrDelay tries to evaluate the left side of the binary operation. If it is not possible to evaluate it, it
  -- returns a delayed evaluation.
  evalOrDelay :: (EvalEnv m) => m Tree
  evalOrDelay =
    let unevaledTC = mkSubTC (toBinOpSelector d1) t1 tc
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
    let v = substTreeNode (TNFunc $ mkBinaryOpDir op (regBin op) (d1, t1) (d2, t2)) (fst tc)
     in do
          dump $ printf "regBinOther: %s is incomplete, delaying to %s" (show t1) (show v)
          return v

  mismatchErr :: String
  mismatchErr = printf "values %s and %s cannot be used for %s" (show t1) (show t2) (show op)

data DisjItem = DisjDefault Tree | DisjRegular Tree

instance Show DisjItem where
  show (DisjDefault t) = show t
  show (DisjRegular t) = show t

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
  evalDisjAdapt :: (EvalEnv m) => Tree -> Tree -> TreeCursor -> m TreeCursor
  evalDisjAdapt unt1 unt2 x = do
    t1 <- evalSub binOpLeftSelector unt1 x
    t2 <- evalSub binOpRightSelector unt2 x
    u <-
      if not (isValueNode (treeNode t1)) || not (isValueNode (treeNode t2))
        then do
          dump $ printf "evalDisjAdapt: %s, %s are not value nodes, return original disj" (show t1) (show t2)
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
    dump $ printf "evalDisjAdapt: evaluated to %s" (show $ fst u)
    return u

  evalSub :: (EvalEnv m) => Path.Selector -> Tree -> TreeCursor -> m Tree
  evalSub sel t x =
    let unevaledTC = mkSubTC sel t x
     in do
          dump $ printf "evalDisj: path: %s, evaluating:\n%s" (show $ pathFromTC unevaledTC) (show (fst unevaledTC))
          u <- evalTC unevaledTC
          dump $ printf "evalDisj: path: %s, %s, is evaluated to:\n%s" (show $ pathFromTC u) (show t) (show $ fst u)
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
        x : y : [] -> Just $ mkTreeDisj Nothing [x, y]
        _ -> Nothing
     in
      return $ mkTreeDisj subTree (dedupAppend ds1 ds2)
