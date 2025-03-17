{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module EvalExpr where

import AST (
  BinaryOp (Disjunction, Unify),
  Declaration (..),
  ElementList (..),
  EllipsisDecl (Ellipsis),
  Embedding (..),
  Expression (..),
  FieldDecl (Field),
  Index (..),
  Label (..),
  LabelConstraint (..),
  LabelExpr (LabelName, LabelPattern),
  LabelName (..),
  LetClause (LetClause),
  Literal (..),
  Operand (OpExpression, OpLiteral, OperandName),
  OperandName (Identifier),
  PrimaryExpr (..),
  Selector (..),
  SourceFile (SourceFile),
  StringLit (SimpleStringLit),
  UnaryExpr (..),
  UnaryOp (Star),
 )
import Common (Config, Env, TreeOp (isTreeValue))
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State.Strict (MonadState, get, put)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Exception (throwErrSt)
import Path (
  StructTASeg (LetTASeg, StringTASeg),
  binOpLeftTASeg,
  binOpRightTASeg,
 )
import Reduce (
  DisjItem (DisjDefault, DisjRegular),
  builtinMutableTable,
  dispBinMutable,
  mkVarLinkTree,
  reduceDisjPair,
  reduceMutableArg,
  unify,
  unifyREmbedded,
 )
import qualified Reduce.RMonad as RM
import qualified Reduce.RegOps as RegOps
import Text.Printf (printf)
import Util (logDebugStr)
import Value.Mutable (getRefFromMutable)
import Value.Reference (Reference (refArg))
import Value.Tree (appendRefArg, stcLets)
import Value.Tree as VT (
  Atom (Bool, Float, Int, Null, String),
  BdType,
  Bound (BdType),
  DynamicField (DynamicField),
  Field (Field, ssfAttr, ssfCnstrs, ssfNoStatic, ssfPends, ssfValue),
  LabelAttr (LabelAttr, lbAttrCnstr, lbAttrIsVar),
  LetBinding (LetBinding),
  Mutable (Ref, SFunc),
  StatefulFunc (sfnArgs),
  Struct (stcCnstrs, stcFields, stcID, stcOrdLabels, stcPendSubs),
  StructCnstr (StructCnstr),
  StructElemAdder (..),
  StructFieldCnstr (..),
  StructVal (SField, SLet),
  Tree (treeNode),
  TreeNode (TNBottom, TNMutable, TNStruct, TNTop),
  appendSelToRefTree,
  emptyFieldMker,
  emptyStruct,
  getMutableFromTree,
  lookupStructVal,
  mergeAttrs,
  mkAtomTree,
  mkBinaryOp,
  mkBottomTree,
  mkBoundsTree,
  mkIndexRef,
  mkListTree,
  mkMutableTree,
  mkNewTree,
  mkStructFromAdders,
  mkStructTree,
  mkUnaryOp,
  setExpr,
  setTN,
 )

type EvalEnv r m = (Env r m, MonadState Int m)

evalSourceFile :: (EvalEnv r m) => SourceFile -> m Tree
evalSourceFile (SourceFile decls) = do
  logDebugStr $ printf "evalSourceFile: decls: %s" (show decls)
  evalDecls decls

{- | evalExpr and all expr* should return the same level tree cursor.
The label and the evaluated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every eval* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the addr of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
evalExpr :: (EvalEnv r m) => Expression -> m Tree
evalExpr e = do
  t <- case e of
    (ExprUnaryExpr ue) -> evalUnaryExpr ue
    (ExprBinaryOp op e1 e2) -> evalBinary op e1 e2
  return $ setExpr t (Just e)

evalLiteral :: (EvalEnv r m) => Literal -> m Tree
evalLiteral (StructLit s) = evalDecls s
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

evalDecls :: (EvalEnv r m) => [Declaration] -> m Tree
evalDecls decls = do
  sid <- allocOID
  (t, embeds) <- foldM evalDecl (mkStructTree (emptyStruct{stcID = sid}), []) decls
  return $
    if null embeds
      then t
      else
        foldl
          (\acc embed -> mkMutableTree $ mkBinaryOp AST.Unify unifyREmbedded acc embed)
          t
          embeds

allocOID :: (EvalEnv r m) => m Int
allocOID = do
  i <- get
  let j = i + 1
  put j
  return j

-- | Evaluates a declaration in a struct. It returns the updated struct tree and the list of embeddings to be unified.
evalDecl :: (EvalEnv r m) => (Tree, [Tree]) -> Declaration -> m (Tree, [Tree])
evalDecl (x, embeds) decl = case treeNode x of
  TNBottom _ -> return (x, embeds)
  TNStruct struct -> case decl of
    Embedding ed -> do
      v <- evalEmbedding ed
      return (mkStructTree struct, v : embeds)
    EllipsisDecl (Ellipsis cM) ->
      maybe
        (return (mkStructTree struct, embeds))
        (\_ -> throwError "default constraints are not implemented yet")
        cM
    FieldDecl (AST.Field ls e) -> do
      sfa <- evalFdLabels ls e
      let t = addNewStructElem sfa struct
      logDebugStr $ printf "evalDecl: sfa: %s, t: %s" (show sfa) (show t)
      return (t, embeds)
    DeclLet (LetClause ident binde) -> do
      val <- evalExpr binde
      let
        adder = LetSAdder ident val
        t = addNewStructElem adder struct
      logDebugStr $ printf "evalDecl: adder: %s, t: %s" (show adder) (show t)
      return (t, embeds)
  _ -> throwErrSt "invalid struct"

evalEmbedding :: (EvalEnv r m) => Embedding -> m Tree
evalEmbedding (Comprehension _) = throwErrSt "comprehension is not implemented yet"
evalEmbedding (AliasExpr e) = evalExpr e

evalFdLabels :: (EvalEnv r m) => [AST.Label] -> AST.Expression -> m (StructElemAdder Tree)
evalFdLabels lbls e =
  case lbls of
    [] -> throwErrSt "empty labels"
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
        sid <- allocOID
        let val = mkNewTree . TNStruct $ mkStructFromAdders sid [sf2]
        adder <- mkAdder l1 val
        logDebugStr $ printf "evalFdLabels, nested: adder: %s" (show adder)
        return adder
 where
  mkAdder :: (EvalEnv r m) => Label -> Tree -> m (StructElemAdder Tree)
  mkAdder (Label le) val = case le of
    AST.LabelName ln c ->
      let attr = LabelAttr{lbAttrCnstr = cnstrFrom c, lbAttrIsVar = isVar ln}
       in case ln of
            (sselFrom -> Just key) -> return $ StaticSAdder key (VT.emptyFieldMker val attr)
            (dselFrom -> Just se) -> do
              selTree <- evalExpr se
              oid <- allocOID
              return $ DynamicSAdder oid (DynamicField oid attr selTree se val)
            _ -> throwErrSt "invalid label"
    AST.LabelPattern pe -> do
      pat <- evalExpr pe
      oid <- allocOID
      return (CnstrSAdder oid pat val)

  -- Returns the label name and the whether the label is static.
  sselFrom :: LabelName -> Maybe String
  sselFrom (LabelID ident) = Just ident
  sselFrom (LabelString ls) = Just ls
  sselFrom _ = Nothing

  dselFrom :: LabelName -> Maybe AST.Expression
  dselFrom (LabelNameExpr lne) = Just lne
  dselFrom _ = Nothing

  cnstrFrom :: AST.LabelConstraint -> StructFieldCnstr
  cnstrFrom c = case c of
    RegularLabel -> SFCRegular
    OptionalLabel -> SFCOptional
    RequiredLabel -> SFCRequired

  isVar :: LabelName -> Bool
  isVar (LabelID _) = True
  -- Labels which are quoted or expressions are not variables.
  isVar _ = False

-- Insert a new element into the struct. If the field is already in the struct, then unify the field with the new field.
addNewStructElem :: StructElemAdder Tree -> Struct Tree -> Tree
addNewStructElem adder struct = case adder of
  (StaticSAdder name sf) ->
    fromMaybe
      ( case lookupStructVal name struct of
          [SField extSF] ->
            let
              unifySFOp =
                VT.Field
                  { ssfValue = mkNewTree (TNMutable $ mkBinaryOp AST.Unify unify (ssfValue extSF) (ssfValue sf))
                  , ssfAttr = mergeAttrs (ssfAttr extSF) (ssfAttr sf)
                  , ssfCnstrs = []
                  , ssfPends = []
                  , ssfNoStatic = False
                  }
             in
              mkStructTree $ struct{stcFields = Map.insert name unifySFOp (stcFields struct)}
          [SLet _] -> aliasErr name
          [] ->
            mkStructTree $
              struct
                { stcOrdLabels = stcOrdLabels struct ++ [name]
                , stcFields = Map.insert name sf (stcFields struct)
                }
          _ -> aliasErr name
      )
      (existCheck name False)
  (DynamicSAdder i dsf) ->
    mkStructTree $ struct{stcPendSubs = IntMap.insert i dsf (stcPendSubs struct)}
  (CnstrSAdder i pattern val) ->
    mkStructTree $ struct{stcCnstrs = IntMap.insert i (StructCnstr i pattern val) (stcCnstrs struct)}
  (LetSAdder name val) ->
    fromMaybe
      ( mkStructTree $
          struct{stcLets = Map.insert name (LetBinding False val) (stcLets struct)}
      )
      (existCheck name True)
 where
  aliasErr name = mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name
  lbRedeclErr name = mkBottomTree $ printf "%s redeclared in same scope" name

  -- Checks if name is already in the struct. If it is, then return an error message.
  existCheck :: String -> Bool -> Maybe Tree
  existCheck name isNameLet =
    case (lookupStructVal name struct, isNameLet) of
      ([SField f], True)
        | lbAttrIsVar (ssfAttr f) -> Just $ aliasErr name
      ([SLet _], True) -> Just $ lbRedeclErr name
      ([SLet _], False) -> Just $ aliasErr name
      ([_, _], _) -> Just $ aliasErr name
      _ -> Nothing

evalListLit :: (EvalEnv r m) => AST.ElementList -> m Tree
evalListLit (AST.EmbeddingList es) = do
  xs <- mapM evalEmbedding es
  return $ mkListTree xs

evalUnaryExpr :: (EvalEnv r m) => UnaryExpr -> m Tree
evalUnaryExpr (UnaryExprPrimaryExpr primExpr) = evalPrimExpr primExpr
evalUnaryExpr (UnaryExprUnaryOp op e) = evalUnaryOp op e

builtinOpNameTable :: [(String, Tree)]
builtinOpNameTable =
  -- bounds
  map (\b -> (show b, mkBoundsTree [BdType b])) [minBound :: BdType .. maxBound :: BdType]
    -- built-in function names
    -- We use the function to distinguish the identifier from the string literal.
    ++ builtinMutableTable

evalPrimExpr :: (EvalEnv r m) => PrimaryExpr -> m Tree
evalPrimExpr (PrimExprOperand op) = case op of
  OpLiteral lit -> evalLiteral lit
  OpExpression expr -> evalExpr expr
  OperandName (Identifier ident) -> case lookup ident builtinOpNameTable of
    Just v -> return v
    Nothing -> mkVarLinkTree ident
evalPrimExpr e@(PrimExprSelector primExpr sel) = do
  p <- evalPrimExpr primExpr
  evalSelector e sel p
evalPrimExpr e@(PrimExprIndex primExpr idx) = do
  p <- evalPrimExpr primExpr
  evalIndex e idx p
evalPrimExpr (PrimExprArguments primExpr aes) = do
  p <- evalPrimExpr primExpr
  args <- mapM evalExpr aes
  replaceFuncArgs p args

-- | mutApplier creates a new function tree for the original function with the arguments applied.
replaceFuncArgs :: (MonadError String m) => Tree -> [Tree] -> m Tree
replaceFuncArgs t args = case getMutableFromTree t of
  Just (SFunc fn) -> return . setTN t $ TNMutable . SFunc $ fn{sfnArgs = args}
  _ -> throwErrSt $ printf "%s is not a Mutable" (show t)

{- | Evaluates the selector.
Parameters:
- pe is the primary expression.
- sel is the segment.
- addr is the addr to the current expression that contains the segment.
For example, { a: b: x.y }
If the field is "y", and the addr is "a.b", expr is "x.y", the structTreeAddr is "x".
-}
evalSelector ::
  (EvalEnv r m) => PrimaryExpr -> AST.Selector -> Tree -> m Tree
evalSelector _ astSel oprnd =
  return $ appendSelToRefTree oprnd (mkAtomTree (String sel))
 where
  sel = case astSel of
    IDSelector ident -> ident
    AST.StringSelector str -> str

evalIndex ::
  (EvalEnv r m) => PrimaryExpr -> AST.Index -> Tree -> m Tree
evalIndex _ (AST.Index e) oprnd = do
  sel <- evalExpr e
  return $ appendSelToRefTree oprnd sel

{- | Evaluates the unary operator.
unary operator should only be applied to atoms.
-}
evalUnaryOp :: (EvalEnv r m) => UnaryOp -> UnaryExpr -> m Tree
evalUnaryOp op e = do
  t <- evalUnaryExpr e
  return $ mkNewTree (TNMutable $ mkUnaryOp op (RegOps.regUnaryOp op) t)

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (EvalEnv r m) => BinaryOp -> Expression -> Expression -> m Tree
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjunction e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  return $ mkNewTree (TNMutable $ mkBinaryOp op (dispBinMutable op) lt rt)

evalDisj :: (EvalEnv r m) => Expression -> Expression -> m Tree
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
  return $ mkNewTree (TNMutable $ mkBinaryOp AST.Disjunction reduceDisjAdapt lt rt)
 where
  reduceDisjAdapt :: (RM.ReduceMonad s r m) => Tree -> Tree -> m ()
  reduceDisjAdapt unt1 unt2 = do
    t1 <- reduceMutableArg binOpLeftTASeg unt1
    t2 <- reduceMutableArg binOpRightTASeg unt2
    if not (isTreeValue t1) || not (isTreeValue t2)
      then
        logDebugStr $ printf "reduceDisjAdapt: %s, %s are not value nodes, delay" (show t1) (show t2)
      else do
        u <- case (e1, e2) of
          (AST.ExprUnaryExpr (AST.UnaryExprUnaryOp AST.Star _), AST.ExprUnaryExpr (AST.UnaryExprUnaryOp AST.Star _)) ->
            reduceDisjPair (DisjDefault t1) (DisjDefault t2)
          (AST.ExprUnaryExpr (AST.UnaryExprUnaryOp AST.Star _), _) ->
            reduceDisjPair (DisjDefault t1) (DisjRegular t2)
          (_, AST.ExprUnaryExpr (AST.UnaryExprUnaryOp AST.Star _)) ->
            reduceDisjPair (DisjRegular t1) (DisjDefault t2)
          (_, _) -> reduceDisjPair (DisjRegular t1) (DisjRegular t2)
        logDebugStr $ printf "reduceDisjAdapt: evaluated to %s" (show u)
        RM.putRMTree u
