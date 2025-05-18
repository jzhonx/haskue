{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module EvalExpr where

import AST (
  BinaryOp (Disjoin, Unify),
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
import Common (Env, IDStore (..))
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (gets, modify)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Set as Set
import Exception (throwErrSt)
import Reduce.Nodes (
  builtinMutableTable,
  mkVarLinkTree,
 )
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
  VT.TNBlock block -> case decl of
    Embedding ed -> do
      v <- evalEmbedding False ed
      oid <- allocOID
      let adder = VT.EmbedSAdder oid v
      addNewBlockElem adder block
    EllipsisDecl (Ellipsis cM) ->
      maybe
        (return (VT.mkBlockTree block))
        (\_ -> throwError "default constraints are not implemented yet")
        cM
    FieldDecl (AST.Field ls e) -> do
      sfa <- evalFDeclLabels ls e
      addNewBlockElem sfa block
    DeclLet (LetClause ident binde) -> do
      val <- evalExpr binde
      let adder = VT.LetSAdder ident val
      addNewBlockElem adder block
  _ -> throwErrSt "invalid struct"

evalEmbedding :: (EvalEnv r s m) => Bool -> Embedding -> m VT.Tree
evalEmbedding _ (AliasExpr e) = evalExpr e
evalEmbedding isListCompreh (EmbedComprehension (Comprehension (Clauses (GuardClause ge) cls) lit)) = do
  gev <- evalExpr ge
  clsv <- mapM evalClause cls
  sv <- evalStructLit lit
  return $ VT.mkMutableTree $ VT.Compreh $ VT.mkComprehension isListCompreh (VT.IterClauseIf gev : clsv) sv
evalEmbedding isListCompreh (EmbedComprehension (Comprehension (Clauses (ForClause i jM fe) cls) lit)) = do
  fev <- evalExpr fe
  clsv <- mapM evalClause cls
  sv <- evalStructLit lit
  return $ VT.mkMutableTree $ VT.Compreh $ VT.mkComprehension isListCompreh (VT.IterClauseFor i jM fev : clsv) sv

evalClause :: (EvalEnv r s m) => Clause -> m (VT.IterClause VT.Tree)
evalClause (ClauseStartClause (GuardClause e)) = do
  t <- evalExpr e
  return $ VT.IterClauseIf t
evalClause (ClauseStartClause (ForClause i jM e)) = do
  t <- evalExpr e
  return $ VT.IterClauseFor i jM t
evalClause (ClauseLetClause (LetClause ident le)) = do
  lt <- evalExpr le
  return $ VT.IterClauseLet ident lt

evalFDeclLabels :: (EvalEnv r s m) => [AST.Label] -> AST.Expression -> m (VT.BlockElemAdder VT.Tree)
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
        let val = VT.mkStructTree $ VT.mkStructFromAdders sid [sf2]
        adder <- mkAdder l1 val
        logDebugStr $ printf "evalFDeclLabels, nested: adder: %s" (show adder)
        return adder
 where
  mkAdder :: (EvalEnv r s m) => Label -> VT.Tree -> m (VT.BlockElemAdder VT.Tree)
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
addNewBlockElem :: (Env r s m) => VT.BlockElemAdder VT.Tree -> VT.Block VT.Tree -> m VT.Tree
addNewBlockElem adder block@(VT.Block{VT.blkStruct = struct}) = case adder of
  (VT.StaticSAdder name sf) ->
    maybe
      ( case VT.lookupStructStubVal name struct of
          [VT.SStubField extSF] ->
            let
              unifySFOp =
                VT.Field
                  { VT.ssfValue = VT.mkMutableTree (VT.mkUnifyOp [VT.ssfValue extSF, VT.ssfValue sf])
                  , VT.ssfBaseRaw =
                      Just $
                        VT.mkMutableTree
                          (VT.mkUnifyOp [fromJust $ VT.ssfBaseRaw extSF, fromJust $ VT.ssfBaseRaw sf])
                  , VT.ssfAttr = VT.mergeAttrs (VT.ssfAttr extSF) (VT.ssfAttr sf)
                  , VT.ssfObjects = Set.empty
                  }
             in
              do
                logDebugStr $ printf "addNewBlockElem: extSF: %s, sf: %s" (show extSF) (show sf)
                return $
                  VT.mkBlockTree $
                    VT.setBlockStruct (struct{VT.stcFields = Map.insert name unifySFOp (VT.stcFields struct)}) block
          [VT.SStubLet _] -> return $ aliasErr name
          -- The label is not seen before in the struct.
          [] ->
            return $
              VT.mkBlockTree $
                VT.setBlockStruct
                  ( struct
                      { VT.stcOrdLabels = VT.stcOrdLabels struct ++ [name]
                      , VT.stcBlockIdents = Set.insert name (VT.stcBlockIdents struct)
                      , VT.stcFields = Map.insert name sf (VT.stcFields struct)
                      }
                  )
                  block
          _ -> return $ aliasErr name
      )
      return
      (existCheck name False)
  (VT.DynamicSAdder i dsf) ->
    return . VT.mkBlockTree $
      VT.setBlockStruct (struct{VT.stcDynFields = IntMap.insert i dsf (VT.stcDynFields struct)}) block
  (VT.CnstrSAdder i pattern val) ->
    return . VT.mkBlockTree $
      VT.setBlockStruct
        (struct{VT.stcCnstrs = IntMap.insert i (VT.StructCnstr i pattern val) (VT.stcCnstrs struct)})
        block
  (VT.LetSAdder name val) ->
    return $
      fromMaybe
        -- The name is not seen before in the struct.
        ( VT.mkBlockTree $
            VT.setBlockStruct
              ( struct
                  { VT.stcLets = Map.insert name (VT.LetBinding False val) (VT.stcLets struct)
                  , VT.stcBlockIdents = Set.insert name (VT.stcBlockIdents struct)
                  }
              )
              block
        )
        (existCheck name True)
  (VT.EmbedSAdder i val) -> do
    let embed = VT.mkEmbedding i val
    return $ VT.mkBlockTree $ block{VT.blkEmbeds = IntMap.insert i embed (VT.blkEmbeds block)}
 where
  aliasErr name = VT.mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name
  lbRedeclErr name = VT.mkBottomTree $ printf "%s redeclared in same scope" name

  -- Checks if name is already in the struct. If it is, then return an error message.
  existCheck :: String -> Bool -> Maybe VT.Tree
  existCheck name isNameLet =
    case (VT.lookupStructStubVal name struct, isNameLet) of
      ([VT.SStubField f], True)
        | VT.lbAttrIsIdent (VT.ssfAttr f) -> Just $ aliasErr name
      ([VT.SStubLet _], True) -> Just $ lbRedeclErr name
      ([VT.SStubLet _], False) -> Just $ aliasErr name
      ([_, _], _) -> Just $ aliasErr name
      _ -> Nothing

evalListLit :: (EvalEnv r s m) => AST.ElementList -> m VT.Tree
evalListLit (AST.EmbeddingList es) = do
  xs <- mapM (evalEmbedding True) es
  return $ VT.mkListTree xs

evalUnaryExpr :: (EvalEnv r s m) => UnaryExpr -> m VT.Tree
evalUnaryExpr ue@(UnaryExprPrimaryExpr primExpr) = do
  t <- evalPrimExpr primExpr
  return $ VT.setExpr t (Just (AST.ExprUnaryExpr ue))
evalUnaryExpr ue@(UnaryExprUnaryOp op e) = do
  t <- evalUnaryOp op e
  return $ VT.setExpr t (Just (AST.ExprUnaryExpr ue))

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
  OperandName (Identifier ident) -> case lookup ident builtinOpNameTable of
    Just v -> return v
    Nothing -> mkVarLinkTree ident
  OpExpression expr -> do
    x <- evalExpr expr
    logDebugStr $ printf "evalPrimExpr: new root: %s" (show x)
    return $ x{VT.treeIsRootOfSubTree = True}
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
  Just (VT.RegOp fn) ->
    return . VT.setTN t $
      VT.TNMutable . VT.RegOp $
        fn
          { VT.ropArgs = args
          , VT.ropExpr = VT.buildArgsExpr (VT.ropName fn) args
          }
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
  let tWithE = VT.setExpr t (Just (AST.ExprUnaryExpr e))
  return $ VT.mkNewTree (VT.TNMutable $ VT.mkUnaryOp op tWithE)

{- | order of arguments is important for disjunctions.

left is always before right.
-}
evalBinary :: (EvalEnv r s m) => BinaryOp -> Expression -> Expression -> m VT.Tree
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary AST.Disjoin e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  case op of
    AST.Unify -> return $ flattenUnify lt rt
    _ -> return $ VT.mkNewTree (VT.TNMutable $ VT.mkBinaryOp op lt rt)

flattenUnify :: VT.Tree -> VT.Tree -> VT.Tree
flattenUnify l r = case getLeftAcc of
  Just acc -> VT.mkMutableTree $ VT.mkUnifyOp (acc ++ [r])
  Nothing -> VT.mkMutableTree $ VT.mkUnifyOp [l, r]
 where
  getLeftAcc = case VT.treeNode l of
    -- The left tree is an accumulator only if it is a unify op.
    VT.TNMutable (VT.UOp u) -> Just (VT.ufConjuncts u)
    _ -> Nothing

evalDisj :: (EvalEnv r s m) => Expression -> Expression -> m VT.Tree
evalDisj e1 e2 = do
  ((isLStar, lt), (isRStar, rt)) <- case (e1, e2) of
    (ExprUnaryExpr (UnaryExprUnaryOp Star se1), ExprUnaryExpr (UnaryExprUnaryOp Star se2)) -> do
      l <- evalUnaryExpr se1
      r <- evalUnaryExpr se2
      return ((,) True l, (,) True r)
    (ExprUnaryExpr (UnaryExprUnaryOp Star se1), _) -> do
      l <- evalUnaryExpr se1
      r <- evalExpr e2
      return ((,) True l, (,) False r)
    (_, ExprUnaryExpr (UnaryExprUnaryOp Star se2)) -> do
      l <- evalExpr e1
      r <- evalUnaryExpr se2
      return ((,) False l, (,) True r)
    (_, _) -> do
      l <- evalExpr e1
      r <- evalExpr e2
      return ((,) False l, (,) False r)
  let r = flattenDisj (VT.DisjTerm isLStar lt) (VT.DisjTerm isRStar rt)
  logDebugStr $ printf "evalDisj: l: %s, r: %s, result: %s" (show lt) (show rt) (show r)
  return r

{- | Flatten the disjoin op tree.

Since the leftmost term is in the deepest left and the next term is always on the right, either at this
level or the next level, we can append the right term to accumulating disjunction terms.

For example, a | b | c is parsed as
     |
   /   \
   |    c
 /   \
 a   b

We start with the a, where a is one of a root disj, a marked term or a regular non-disjunction value. Then append b to
it, and then append c to the accumulator.
We never need to go deeper into the right nodes.
-}
flattenDisj :: VT.DisjTerm VT.Tree -> VT.DisjTerm VT.Tree -> VT.Tree
flattenDisj l r = case getLeftAcc of
  Just acc -> VT.mkMutableTree $ VT.mkDisjoinOp (acc ++ [r])
  Nothing -> VT.mkMutableTree $ VT.mkDisjoinOp [l, r]
 where
  getLeftAcc = case VT.treeNode (VT.dstValue l) of
    VT.TNMutable (VT.DisjOp dj)
      -- The left term is an accumulator only if it is a disjoin op and not marked nor the root.
      -- If the left term is a marked term, it implies that it is a root.
      | not (VT.dstMarked l) && not (VT.treeIsRootOfSubTree (VT.dstValue l)) -> Just (VT.djoTerms dj)
    _ -> Nothing

allocOID :: (EvalEnv r s m) => m Int
allocOID = do
  i <- gets getID
  let j = i + 1
  modify (`setID` j)
  return j