{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module EvalExpr where

import AST (
  BinaryOp (Disjunction, Unify),
  Clause (..),
  Clauses (..),
  Comprehension (..),
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
  StartClause (..),
  StringLit (SimpleStringLit),
  StructLit (..),
  UnaryExpr (..),
  UnaryOp (Star),
 )
import Common (Env, IDStore (..), TreeOp (isTreeValue))
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (gets, modify)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Set as Set
import Exception (throwErrSt)
import Path (
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
 )
import qualified Reduce.RMonad as RM
import qualified Reduce.RegOps as RegOps
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

type EvalEnv r s m = (Env r s m, IDStore s)

evalSourceFile :: (EvalEnv r s m) => SourceFile -> m VT.Tree
evalSourceFile (SourceFile decls) = do
  logDebugStr $ printf "evalSourceFile: decls: %s" (show decls)
  evalStructLit (StructLit decls)

{- | evalExpr and all expr* should return the same level tree cursor.
The label and the evaluated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every eval* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the addr of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
evalExpr :: (EvalEnv r s m) => Expression -> m VT.Tree
evalExpr e = do
  t <- case e of
    (ExprUnaryExpr ue) -> evalUnaryExpr ue
    (ExprBinaryOp op e1 e2) -> evalBinary op e1 e2
  return $ VT.setExpr t (Just e)

evalLiteral :: (EvalEnv r s m) => Literal -> m VT.Tree
evalLiteral (LitStructLit s) = evalStructLit s
evalLiteral (ListLit l) = evalListLit l
evalLiteral lit = return v
 where
  v = case lit of
    StringLit (SimpleStringLit s) -> VT.mkAtomTree $ VT.String s
    IntLit i -> VT.mkAtomTree $ VT.Int i
    FloatLit a -> VT.mkAtomTree $ VT.Float a
    BoolLit b -> VT.mkAtomTree $ VT.Bool b
    NullLit -> VT.mkAtomTree VT.Null
    TopLit -> VT.mkNewTree VT.TNTop
    BottomLit -> VT.mkBottomTree ""

evalStructLit :: (EvalEnv r s m) => StructLit -> m VT.Tree
evalStructLit (StructLit decls) = do
  sid <- allocOID
  foldM evalDecl (VT.mkStructTree (VT.emptyStruct{VT.stcID = sid})) decls

-- | Evaluates a declaration in a struct. It returns the updated struct tree.
evalDecl :: (EvalEnv r s m) => VT.Tree -> Declaration -> m VT.Tree
evalDecl x decl = case VT.treeNode x of
  VT.TNBottom _ -> return x
  VT.TNStruct struct -> case decl of
    Embedding ed -> do
      v <- evalEmbedding ed
      oid <- allocOID
      let adder = VT.EmbedSAdder oid v
      addNewStructElem adder struct
    EllipsisDecl (Ellipsis cM) ->
      maybe
        (return (VT.mkStructTree struct))
        (\_ -> throwError "default constraints are not implemented yet")
        cM
    FieldDecl (AST.Field ls e) -> do
      sfa <- evalFDeclLabels ls e
      addNewStructElem sfa struct
    DeclLet (LetClause ident binde) -> do
      val <- evalExpr binde
      let adder = VT.LetSAdder ident val
      addNewStructElem adder struct
  _ -> throwErrSt "invalid struct"

evalEmbedding :: (EvalEnv r s m) => Embedding -> m VT.Tree
evalEmbedding (AliasExpr e) = evalExpr e
evalEmbedding (EmbedComprehension (Comprehension (Clauses (GuardClause ge) cls) lit)) = do
  gev <- evalExpr ge
  clsv <- mapM evalClause cls
  sv <- evalStructLit lit
  return $ VT.mkMutableTree $ VT.Compreh $ VT.mkComprehension gev clsv sv

evalClause :: (EvalEnv r s m) => Clause -> m (VT.IterClause VT.Tree)
evalClause (ClauseStartClause (GuardClause e)) = do
  t <- evalExpr e
  return $ VT.IterClauseIf t
evalClause (ClauseLetClause (LetClause ident le)) = do
  lt <- evalExpr le
  return $ VT.IterClauseLet ident lt

-- evalStartClause :: (EvalEnv r s m) => StartClause -> m VT.Tree
-- evalStartClause (GuardClause e) = evalExpr e

evalFDeclLabels :: (EvalEnv r s m) => [AST.Label] -> AST.Expression -> m (VT.StructElemAdder VT.Tree)
evalFDeclLabels lbls e =
  case lbls of
    [] -> throwErrSt "empty labels"
    [l1] ->
      do
        logDebugStr $ printf "evalFDeclLabels: lb1: %s" (show l1)
        val <- evalExpr e
        adder <- mkAdder l1 val
        logDebugStr $ printf "evalFDeclLabels: adder: %s" (show adder)
        return adder
    l1 : l2 : rs ->
      do
        logDebugStr $ printf "evalFDeclLabels, nested: lb1: %s" (show l1)
        sf2 <- evalFDeclLabels (l2 : rs) e
        sid <- allocOID
        let val = VT.mkNewTree . VT.TNStruct $ VT.mkStructFromAdders sid [sf2]
        adder <- mkAdder l1 val
        logDebugStr $ printf "evalFDeclLabels, nested: adder: %s" (show adder)
        return adder
 where
  mkAdder :: (EvalEnv r s m) => Label -> VT.Tree -> m (VT.StructElemAdder VT.Tree)
  mkAdder (Label le) val = case le of
    AST.LabelName ln c ->
      let attr = VT.LabelAttr{VT.lbAttrCnstr = cnstrFrom c, VT.lbAttrIsIdent = isVar ln}
       in case ln of
            (sselFrom -> Just key) -> do
              logDebugStr $ printf "evalFDeclLabels: key: %s, mkAdder, val: %s" key (show val)
              return $ VT.StaticSAdder key (VT.staticFieldMker val attr)
            (dselFrom -> Just se) -> do
              selTree <- evalExpr se
              oid <- allocOID
              return $ VT.DynamicSAdder oid (VT.DynamicField oid attr selTree se val)
            _ -> throwErrSt "invalid label"
    AST.LabelPattern pe -> do
      pat <- evalExpr pe
      oid <- allocOID
      return (VT.CnstrSAdder oid pat val)

  -- Returns the label name and the whether the label is static.
  sselFrom :: LabelName -> Maybe String
  sselFrom (LabelID ident) = Just ident
  sselFrom (LabelString ls) = Just ls
  sselFrom _ = Nothing

  dselFrom :: LabelName -> Maybe AST.Expression
  dselFrom (LabelNameExpr lne) = Just lne
  dselFrom _ = Nothing

  cnstrFrom :: AST.LabelConstraint -> VT.StructFieldCnstr
  cnstrFrom c = case c of
    RegularLabel -> VT.SFCRegular
    OptionalLabel -> VT.SFCOptional
    RequiredLabel -> VT.SFCRequired

  isVar :: LabelName -> Bool
  isVar (LabelID _) = True
  -- Labels which are quoted or expressions are not variables.
  isVar _ = False

{- | Insert a new element into the struct. If the field is already in the struct, then unify the field with the new
field.
-}
addNewStructElem :: (Env r s m) => VT.StructElemAdder VT.Tree -> VT.Struct VT.Tree -> m VT.Tree
addNewStructElem adder struct = case adder of
  (VT.StaticSAdder name sf) ->
    maybe
      ( case VT.lookupStructVal name struct of
          [VT.SField extSF] ->
            let
              unifySFOp =
                VT.Field
                  { VT.ssfValue =
                      VT.mkNewTree
                        (VT.TNMutable $ VT.mkBinaryOp AST.Unify unify (VT.ssfValue extSF) (VT.ssfValue sf))
                  , VT.ssfBaseRaw =
                      Just $
                        VT.mkNewTree
                          ( VT.TNMutable $
                              VT.mkBinaryOp
                                AST.Unify
                                unify
                                (fromJust $ VT.ssfBaseRaw extSF)
                                (fromJust $ VT.ssfBaseRaw sf)
                          )
                  , VT.ssfAttr = VT.mergeAttrs (VT.ssfAttr extSF) (VT.ssfAttr sf)
                  , VT.ssfObjects = Set.empty
                  }
             in
              do
                logDebugStr $ printf "addNewStructElem: extSF: %s, sf: %s" (show extSF) (show sf)
                return $ VT.mkStructTree $ struct{VT.stcFields = Map.insert name unifySFOp (VT.stcFields struct)}
          [VT.SLet _] -> return $ aliasErr name
          -- The label is not seen before in the struct.
          [] ->
            return $
              VT.mkStructTree $
                struct
                  { VT.stcOrdLabels = VT.stcOrdLabels struct ++ [name]
                  , VT.stcBlockIdents = Set.insert name (VT.stcBlockIdents struct)
                  , VT.stcFields = Map.insert name sf (VT.stcFields struct)
                  }
          _ -> return $ aliasErr name
      )
      return
      (existCheck name False)
  (VT.DynamicSAdder i dsf) ->
    return $ VT.mkStructTree $ struct{VT.stcDynFields = IntMap.insert i dsf (VT.stcDynFields struct)}
  (VT.CnstrSAdder i pattern val) ->
    return $ VT.mkStructTree $ struct{VT.stcCnstrs = IntMap.insert i (VT.StructCnstr i pattern val) (VT.stcCnstrs struct)}
  (VT.LetSAdder name val) ->
    return $
      fromMaybe
        -- The name is not seen before in the struct.
        ( VT.mkStructTree $
            struct
              { VT.stcLets = Map.insert name (VT.LetBinding False val) (VT.stcLets struct)
              , VT.stcBlockIdents = Set.insert name (VT.stcBlockIdents struct)
              }
        )
        (existCheck name True)
  (VT.EmbedSAdder i val) -> do
    let embed = VT.mkEmbedding i val
    return $ VT.mkStructTree $ struct{VT.stcEmbeds = IntMap.insert i embed (VT.stcEmbeds struct)}
 where
  aliasErr name = VT.mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name
  lbRedeclErr name = VT.mkBottomTree $ printf "%s redeclared in same scope" name

  -- Checks if name is already in the struct. If it is, then return an error message.
  existCheck :: String -> Bool -> Maybe VT.Tree
  existCheck name isNameLet =
    case (VT.lookupStructVal name struct, isNameLet) of
      ([VT.SField f], True)
        | VT.lbAttrIsIdent (VT.ssfAttr f) -> Just $ aliasErr name
      ([VT.SLet _], True) -> Just $ lbRedeclErr name
      ([VT.SLet _], False) -> Just $ aliasErr name
      ([_, _], _) -> Just $ aliasErr name
      _ -> Nothing

evalListLit :: (EvalEnv r s m) => AST.ElementList -> m VT.Tree
evalListLit (AST.EmbeddingList es) = do
  xs <- mapM evalEmbedding es
  return $ VT.mkListTree xs

evalUnaryExpr :: (EvalEnv r s m) => UnaryExpr -> m VT.Tree
evalUnaryExpr (UnaryExprPrimaryExpr primExpr) = evalPrimExpr primExpr
evalUnaryExpr (UnaryExprUnaryOp op e) = evalUnaryOp op e

builtinOpNameTable :: [(String, VT.Tree)]
builtinOpNameTable =
  -- bounds
  map (\b -> (show b, VT.mkBoundsTree [VT.BdType b])) [minBound :: VT.BdType .. maxBound :: VT.BdType]
    -- built-in function names
    -- We use the function to distinguish the identifier from the string literal.
    ++ builtinMutableTable

evalPrimExpr :: (EvalEnv r s m) => PrimaryExpr -> m VT.Tree
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
replaceFuncArgs :: (MonadError String m) => VT.Tree -> [VT.Tree] -> m VT.Tree
replaceFuncArgs t args = case VT.getMutableFromTree t of
  Just (VT.SFunc fn) -> return . VT.setTN t $ VT.TNMutable . VT.SFunc $ fn{VT.sfnArgs = args}
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
  (EvalEnv r s m) => PrimaryExpr -> AST.Selector -> VT.Tree -> m VT.Tree
evalSelector _ astSel oprnd =
  return $ VT.appendSelToRefTree oprnd (VT.mkAtomTree (VT.String sel))
 where
  sel = case astSel of
    IDSelector ident -> ident
    AST.StringSelector str -> str

evalIndex ::
  (EvalEnv r s m) => PrimaryExpr -> AST.Index -> VT.Tree -> m VT.Tree
evalIndex _ (AST.Index e) oprnd = do
  sel <- evalExpr e
  return $ VT.appendSelToRefTree oprnd sel

{- | Evaluates the unary operator.

unary operator should only be applied to atoms.
-}
evalUnaryOp :: (EvalEnv r s m) => UnaryOp -> UnaryExpr -> m VT.Tree
evalUnaryOp op e = do
  t <- evalUnaryExpr e
  return $ VT.mkNewTree (VT.TNMutable $ VT.mkUnaryOp op (RegOps.regUnaryOp op) t)

{- | order of arguments is important for disjunctions.

left is always before right.
-}
evalBinary :: (EvalEnv r s m) => BinaryOp -> Expression -> Expression -> m VT.Tree
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjunction e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  return $ VT.mkNewTree (VT.TNMutable $ VT.mkBinaryOp op (dispBinMutable op) lt rt)

evalDisj :: (EvalEnv r s m) => Expression -> Expression -> m VT.Tree
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
  return $ VT.mkNewTree (VT.TNMutable $ VT.mkBinaryOp AST.Disjunction reduceDisjAdapt lt rt)
 where
  reduceDisjAdapt :: (RM.ReduceMonad s r m) => VT.Tree -> VT.Tree -> m ()
  reduceDisjAdapt unt1 unt2 = do
    t1 <- reduceMutableArg Path.binOpLeftTASeg unt1
    t2 <- reduceMutableArg Path.binOpRightTASeg unt2
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

allocOID :: (EvalEnv r s m) => m Int
allocOID = do
  i <- gets getID
  let j = i + 1
  modify (`setID` j)
  return j