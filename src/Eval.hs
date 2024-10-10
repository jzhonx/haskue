{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Eval (
  EvalConfig (..),
  runIO,
  runTreeIO,
  eval,
)
where

import AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (MonadLogger, runNoLoggingT, runStderrLoggingT)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (evalStateT, execStateT)
import Data.Maybe (fromJust, isJust)
import Parser (parseCUE)
import Path
import Text.Printf (printf)
import Tree
import Unify (unify)

data EvalConfig = EvalConfig
  { ecDebugLogging :: Bool
  , ecMermaidGraph :: Bool
  , ecFilePath :: String
  }

runIO :: (MonadIO m, MonadError String m) => String -> EvalConfig -> m AST.Expression
runIO s conf =
  if ecDebugLogging conf
    then runStderrLoggingT res
    else runNoLoggingT res
 where
  res :: (MonadError String m, MonadLogger m) => m AST.Expression
  res = runStr s (ecMermaidGraph conf)

runTreeIO :: (MonadIO m, MonadError String m) => String -> m Tree
runTreeIO s = runNoLoggingT $ runTreeStr s False

runStr :: (MonadError String m, MonadLogger m) => String -> Bool -> m AST.Expression
runStr s mermaid = do
  t <- runTreeStr s mermaid
  runReaderT (buildASTExpr False t) Config{}

runTreeStr :: (MonadError String m, MonadLogger m) => String -> Bool -> m Tree
runTreeStr s conf = parseCUE s >>= flip eval conf

eval :: (MonadError String m, MonadLogger m) => Expression -> Bool -> m Tree
eval expr mermaid = do
  rootTC <-
    runReaderT
      ( do
          root <- evalStateT (evalExpr expr) emptyContext
          dump $ printf "---- evaluated to rootTC: ----\n%s" (show root)
          let rootTC = ValCursor root [(RootSelector, mkNewTree TNTop)]
          r2 <- execStateT setOrigNodes (mkCVFromCur rootTC)
          dump $ printf "---- start resolving links ----"
          res <- execStateT evalTM r2
          dump $ printf "---- resolved: ----\n%s" (show . getCVCursor $ res)
          return res
      )
      Config{cfUnify = unify, cfCreateCnstr = True, cfMermaid = mermaid}

  finalized <-
    runReaderT
      (execStateT validateCnstrs rootTC)
      Config{cfUnify = unify, cfCreateCnstr = False, cfMermaid = mermaid}
  dump $ printf "---- constraints evaluated: ----\n%s" (show . getCVCursor $ finalized)
  return $ cvVal finalized

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
  evalDecl :: (EvalEnv m) => (Struct, [Tree]) -> Declaration -> m (Struct, [Tree])
  evalDecl (scp, ts) (Embedding e) = do
    v <- evalExpr e
    return (scp, v : ts)
  evalDecl (struct, ts) (FieldDecl fd) = case fd of
    Field ls e -> do
      sfa <- evalFdLabels ls e
      let newStruct = insertUnifyStruct sfa unify struct
      return (newStruct, ts)

  evalFdLabels :: (EvalEnv m) => [AST.Label] -> AST.Expression -> m StructElemAdder
  evalFdLabels lbls e =
    case lbls of
      [] -> throwError "empty labels"
      [l1] ->
        do
          dump $ printf "evalFdLabels: lb1: %s" (show l1)
          val <- evalExpr e
          adder <- mkAdder l1 val
          dump $ printf "evalFdLabels: adder: %s" (show adder)
          return adder
      l1 : l2 : rs ->
        do
          dump $ printf "evalFdLabels, nested: lb1: %s" (show l1)
          sf2 <- evalFdLabels (l2 : rs) e
          let val = mkStructTree [sf2]
          adder <- mkAdder l1 val
          dump $ printf "evalFdLabels, nested: adder: %s" (show adder)
          return adder

  mkAdder :: (EvalEnv m) => Label -> Tree -> m StructElemAdder
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
    Nothing -> return $ mkVarLinkTree ident (AST.UnaryExprPrimaryExpr e)
    Just b -> return $ mkBoundsTree [b]
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

dispUnaryFunc :: (TreeMonad s m) => UnaryOp -> Tree -> m ()
dispUnaryFunc op t = do
  case treeNode t of
    TNAtom ta -> case (op, amvAtom ta) of
      (Plus, Int i) -> ia i id
      (Plus, Float i) -> fa i id
      (Minus, Int i) -> ia i negate
      (Minus, Float i) -> fa i negate
      (Not, Bool b) -> putTMTree $ mkAtomTree (Bool (not b))
      (AST.UnaRelOp uop, _) -> case (uop, amvAtom ta) of
        (AST.NE, a) -> mkb (BdNE a)
        (AST.LT, Int i) -> mkib BdLT i
        (AST.LT, Float f) -> mkfb BdLT f
        (AST.LE, Int i) -> mkib BdLE i
        (AST.LE, Float f) -> mkfb BdLE f
        (AST.GT, Int i) -> mkib BdGT i
        (AST.GT, Float f) -> mkfb BdGT f
        (AST.GE, Int i) -> mkib BdGE i
        (AST.GE, Float f) -> mkfb BdGE f
        (AST.ReMatch, String p) -> putTMTree $ mkBoundsTree [BdStrMatch $ BdReMatch p]
        (AST.ReNotMatch, String p) -> putTMTree $ mkBoundsTree [BdStrMatch $ BdReNotMatch p]
        _ -> putConflict
      _ -> putConflict
    -- The unary op is operating on a non-atom.
    TNFunc _ -> putTMTree $ mkNewTree (TNFunc $ mkUnaryOp op (dispUnaryFunc op) t)
    _ -> putConflict
 where
  conflict :: Tree
  conflict = mkBottomTree $ printf "%s cannot be used for %s" (show t) (show op)

  putConflict :: (TreeMonad s m) => m ()
  putConflict = putTMTree conflict

  ia :: (TreeMonad s m) => Integer -> (Integer -> Integer) -> m ()
  ia a f = putTMTree $ mkAtomTree (Int $ f a)

  fa :: (TreeMonad s m) => Double -> (Double -> Double) -> m ()
  fa a f = putTMTree $ mkAtomTree (Float $ f a)

  mkb :: (TreeMonad s m) => Bound -> m ()
  mkb b = putTMTree $ mkBoundsTree [b]

  mkib :: (TreeMonad s m) => BdNumCmpOp -> Integer -> m ()
  mkib uop i = putTMTree $ mkBoundsTree [BdNumCmp $ BdNumCmpCons uop (NumInt i)]

  mkfb :: (TreeMonad s m) => BdNumCmpOp -> Double -> m ()
  mkfb uop f = putTMTree $ mkBoundsTree [BdNumCmp $ BdNumCmpCons uop (NumFloat f)]

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (EvalEnv m) => BinaryOp -> Expression -> Expression -> m Tree
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjunction e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  return $ mkNewTree (TNFunc $ mkBinaryOp op (dispBinFunc op) lt rt)

dispBinFunc :: (TreeMonad s m) => BinaryOp -> Tree -> Tree -> m ()
dispBinFunc op = case op of
  AST.Unify -> unify
  _ -> regBin op

regBin :: (TreeMonad s m) => BinaryOp -> Tree -> Tree -> m ()
regBin op t1 t2 = regBinDir op (L, t1) (R, t2)

regBinDir :: (TreeMonad s m) => BinaryOp -> (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> m ()
regBinDir op dt1@(d1, t1) dt2@(d2, t2) = do
  withDumpInfo $ \path _ ->
    dump $
      printf "regBinDir: path: %s, %s: %s with %s: %s" (show path) (show d1) (show t1) (show d2) (show t2)
  case (treeNode t1, treeNode t2) of
    (TNBottom _, _) -> putTMTree t1
    (_, TNBottom _) -> putTMTree t2
    (TNAtom l1, _) -> regBinLeftAtom op (d1, l1, t1) dt2
    (_, TNAtom l2) -> regBinLeftAtom op (d2, l2, t2) dt1
    (TNStruct s1, _) -> regBinLeftStruct op (d1, s1, t1) dt2
    (_, TNStruct s2) -> regBinLeftStruct op (d2, s2, t2) dt1
    (TNDisj dj1, _) -> regBinLeftDisj op (d1, dj1, t1) dt2
    (_, TNDisj dj2) -> regBinLeftDisj op (d2, dj2, t2) dt1
    _ -> regBinLeftOther op dt1 dt2

regBinLeftAtom :: (TreeMonad s m) => BinaryOp -> (BinOpDirect, AtomV, Tree) -> (BinOpDirect, Tree) -> m ()
regBinLeftAtom op (d1, ta1, t1) (d2, t2) = do
  dump $ printf "regBinLeftAtom: %s (%s: %s) (%s: %s)" (show op) (show d1) (show ta1) (show d2) (show t2)
  if
    -- comparison operators
    | isJust (lookup op cmpOps) -> case treeNode t2 of
        TNAtom ta2 ->
          let
            a2 = amvAtom ta2
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
              Right b -> putTMTree $ mkAtomTree b
              Left err -> putTMTree err
        TNStruct _ -> putTMTree $ cmpNull a1 t2
        TNList _ -> putTMTree $ cmpNull a1 t2
        TNDisj _ -> putTMTree $ cmpNull a1 t2
        _ -> regBinLeftOther op (d2, t2) (d1, t1)
    -- arithmetic operators
    | op `elem` arithOps -> case treeNode t2 of
        TNAtom ta2 ->
          let
            r = case op of
              AST.Add -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (+) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (+) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (+) (d1, i1) (fromIntegral i2)
                (String s1, String s2) -> Right . String $ dirApply (++) (d1, s1) s2
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              AST.Sub -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (-) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (-) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (-) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              AST.Mul -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (*) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (*) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (*) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              AST.Div -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Float $ dirApply (/) (d1, fromIntegral i1) (fromIntegral i2)
                (Int i1, Float i2) -> Right . Float $ dirApply (/) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (/) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              _ -> Left $ mismatch op a1 (amvAtom ta2)
           in
            case r of
              Right b -> putTMTree $ mkAtomTree b
              Left err -> putTMTree err
        TNStruct _ -> putTMTree $ mismatchArith a1 t2
        TNList _ -> putTMTree $ mismatchArith a1 t2
        TNDisj _ -> putTMTree $ mismatchArith a1 t2
        _ -> regBinLeftOther op (d2, t2) (d1, t1)
    | otherwise -> putTMTree $ mkBottomTree $ printf "operator %s is not supported" (show op)
 where
  a1 = amvAtom ta1
  cmpOps = [(AST.Equ, (==)), (AST.BinRelOp AST.NE, (/=))]
  arithOps = [AST.Add, AST.Sub, AST.Mul, AST.Div]

  uncmpAtoms :: Atom -> Atom -> Tree
  uncmpAtoms x y = mkBottomTree $ printf "%s and %s are not comparable" (show x) (show y)

  cmpNull :: Atom -> Tree -> Tree
  cmpNull a t =
    if
      -- There is no way for a non-atom to be compared with a non-null atom.
      | a /= Null -> mismatch op a t
      | op == AST.Equ -> mkAtomTree (Bool False)
      | op == AST.BinRelOp AST.NE -> mkAtomTree (Bool True)
      | otherwise -> mkBottomTree $ printf "operator %s is not supported" (show op)

  mismatchArith :: (Show a, Show b) => a -> b -> Tree
  mismatchArith = mismatch op

dirApply :: (a -> a -> b) -> (BinOpDirect, a) -> a -> b
dirApply f (di1, i1) i2 = if di1 == L then f i1 i2 else f i2 i1

mismatch :: (Show a, Show b) => BinaryOp -> a -> b -> Tree
mismatch op x y = mkBottomTree $ printf "%s can not be used for %s and %s" (show op) (show x) (show y)

regBinLeftStruct ::
  (TreeMonad s m) => BinaryOp -> (BinOpDirect, Struct, Tree) -> (BinOpDirect, Tree) -> m ()
regBinLeftStruct op (d1, _, t1) (d2, t2) = case treeNode t2 of
  TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1)
  _ -> putTMTree (mismatch op t1 t2)

regBinLeftDisj ::
  (TreeMonad s m) => BinaryOp -> (BinOpDirect, Disj, Tree) -> (BinOpDirect, Tree) -> m ()
regBinLeftDisj op (d1, dj1, t1) (d2, t2) = case dj1 of
  Disj{dsjDefault = Just d} -> regBinDir op (d1, d) (d2, t2)
  _ -> case treeNode t2 of
    TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1)
    _ -> putTMTree (mismatch op t1 t2)

regBinLeftOther :: (TreeMonad s m) => BinaryOp -> (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> m ()
regBinLeftOther op (d1, t1) (d2, t2) = do
  dump $ printf "regBinLeftOther: %s: %s, %s: %s" (show d1) (show t1) (show d2) (show t2)
  case (treeNode t1, t2) of
    (TNFunc fn, _)
      | isFuncRef fn -> do
          et1 <- evalFuncArg (toBinOpSelector d1) t1 exhaustTM
          regBinDir op (d1, et1) (d2, t2)
      | otherwise -> evalOrDelay
    (TNRefCycle _, _) -> evalOrDelay
    (TNConstraint c, _) -> do
      na <- regBinDir op (d1, mkNewTree (TNAtom $ cnsAtom c)) (d2, t2) >> getTMTree
      case treeNode na of
        TNAtom atom -> putTMTree $ mkNewTree (TNConstraint $ updateCnstrAtom atom c)
        _ -> undefined
    _ -> putTMTree (mkBottomTree mismatchErr)
 where
  -- evalOrDelay tries to evaluate the left side of the binary operation. If it is not possible to evaluate it, it
  -- returns a delayed evaluation.
  evalOrDelay :: (TreeMonad s m) => m ()
  evalOrDelay = do
    dump $ printf "evalOrDelay: %s: %s, %s: %s" (show d1) (show t1) (show d2) (show t2)
    et1 <- evalFuncArg (toBinOpSelector d1) t1 exhaustTM
    procLeftOtherRes et1

  procLeftOtherRes :: (TreeMonad s m) => Tree -> m ()
  procLeftOtherRes x = case treeNode x of
    TNAtom a1 -> regBinLeftAtom op (d1, a1, x) (d2, t2)
    TNDisj dj1 -> regBinLeftDisj op (d1, dj1, x) (d2, t2)
    TNStruct s1 -> regBinLeftStruct op (d1, s1, x) (d2, t2)
    TNList _ -> undefined
    TNConstraint _ -> regBinLeftOther op (d1, x) (d2, t2)
    _ -> do
      let v = mkNewTree (TNFunc $ mkBinaryOpDir op (regBin op) (d1, x) (d2, t2))
      withDumpInfo $ \path _ ->
        dump $ printf "regBinLeftOther: path: %s, %s is incomplete, delaying to %s" (show path) (show x) (show v)
      putTMTree v

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
  evalDisjAdapt :: (TreeMonad s m) => Tree -> Tree -> m ()
  evalDisjAdapt unt1 unt2 = do
    t1 <- evalFuncArg binOpLeftSelector unt1 exhaustTM
    t2 <- evalFuncArg binOpRightSelector unt2 exhaustTM
    u <-
      if not (isTreeValue t1) || not (isTreeValue t2)
        then do
          dump $ printf "evalDisjAdapt: %s, %s are not value nodes, return original disj" (show t1) (show t2)
          getTMTree
        else do
          case (e1, e2) of
            (ExprUnaryExpr (UnaryExprUnaryOp Star _), ExprUnaryExpr (UnaryExprUnaryOp Star _)) ->
              evalDisjPair (DisjDefault t1) (DisjDefault t2)
            (ExprUnaryExpr (UnaryExprUnaryOp Star _), _) ->
              evalDisjPair (DisjDefault t1) (DisjRegular t2)
            (_, ExprUnaryExpr (UnaryExprUnaryOp Star _)) ->
              evalDisjPair (DisjRegular t1) (DisjDefault t2)
            (_, _) -> evalDisjPair (DisjRegular t1) (DisjRegular t2)
    dump $ printf "evalDisjAdapt: evaluated to %s" (show u)
    putTMTree u

  -- evalDisjPair is used to evaluate a disjunction whose both sides are evaluated.
  evalDisjPair :: (TreeMonad s m) => DisjItem -> DisjItem -> m Tree
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
    disjCons (dsjDefault dj1, dsjDisjuncts dj1, Nothing, dsjDisjuncts dj2)
  -- Below is rule M1.
  evalLeftDefault disjCons v1 (DisjRegular (Tree{treeNode = TNDisj dj2})) =
    disjCons (Just v1, [v1], dsjDefault dj2, dsjDisjuncts dj2)
  evalLeftDefault disjCons v1 (DisjRegular v2) =
    disjCons (Just v1, [v1], Nothing, [v2])
  evalLeftDefault disjCons v1 (DisjDefault v2) =
    disjCons (Nothing, [v1], Nothing, [v2])

  -- evalFullDisj is used to evaluate a disjunction whose both sides are regular.
  -- Rule: D1, D2
  evalRegularDisj :: (TreeMonad s m) => Tree -> Tree -> m Tree
  evalRegularDisj (Tree{treeNode = TNDisj dj1}) (Tree{treeNode = TNDisj dj2}) =
    newDisj (dsjDefault dj1) (dsjDisjuncts dj1) (dsjDefault dj2) (dsjDisjuncts dj2)
  evalRegularDisj (Tree{treeNode = TNDisj dj}) y = newDisj (dsjDefault dj) (dsjDisjuncts dj) Nothing [y]
  evalRegularDisj x (Tree{treeNode = TNDisj dj}) = newDisj Nothing [x] (dsjDefault dj) (dsjDisjuncts dj)
  -- Rule D0
  evalRegularDisj x y = newDisj Nothing [x] Nothing [y]

  -- dedupAppend appends unique elements in ys to the xs list, but only if they are not already in xs.
  -- xs and ys are guaranteed to be unique.
  dedupAppend :: [Tree] -> [Tree] -> [Tree]
  dedupAppend xs ys = xs ++ foldr (\y acc -> if y `elem` xs then acc else y : acc) [] ys

  newDisj :: (TreeMonad s m) => Maybe Tree -> [Tree] -> Maybe Tree -> [Tree] -> m Tree
  newDisj df1 ds1 df2 ds2 =
    let
      subTree :: Maybe Tree
      subTree = case map fromJust (filter isJust [df1, df2]) of
        [x] -> Just x
        [x, y] -> Just $ mkDisjTree Nothing [x, y]
        _ -> Nothing
     in
      return $ mkDisjTree subTree (dedupAppend ds1 ds2)
