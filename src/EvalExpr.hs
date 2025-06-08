{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module EvalExpr where

import AST
import qualified Common
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
 )
import Text.Printf (printf)
import qualified Value.Tree as VT

type EvalEnv r s m = (Common.Env r s m, Common.IDStore s)

evalSourceFile :: (EvalEnv r s m) => SourceFile -> m VT.Tree
evalSourceFile (SourceFile decls) = evalStructLit (pure $ StructLit decls)

{- | evalExpr and all expr* should return the same level tree cursor.
The label and the evaluated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every eval* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the addr of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
evalExpr :: (EvalEnv r s m) => Expression -> m VT.Tree
evalExpr e = do
  t <- case wpVal e of
    (ExprUnaryExpr ue) -> evalUnaryExpr ue
    (ExprBinaryOp op e1 e2) -> evalBinary op e1 e2
  return $ VT.setExpr t (Just e)

evalLiteral :: (EvalEnv r s m) => Literal -> m VT.Tree
evalLiteral (wpVal -> LitStructLit s) = evalStructLit s
evalLiteral (wpVal -> ListLit l) = evalListLit l
evalLiteral (wpVal -> StringLit (wpVal -> SimpleStringL s)) = do
  rE <- simpleStringLitToStr s
  return $ case rE of
    Left t -> t
    Right str -> VT.mkAtomTree $ VT.String str
evalLiteral lit = return v
 where
  v = case wpVal lit of
    IntLit i -> VT.mkAtomTree $ VT.Int i
    FloatLit a -> VT.mkAtomTree $ VT.Float a
    BoolLit b -> VT.mkAtomTree $ VT.Bool b
    NullLit -> VT.mkAtomTree VT.Null
    TopLit -> VT.mkNewTree VT.TNTop
    BottomLit -> VT.mkBottomTree ""
    _ -> error "evalLiteral: invalid literal"

evalStructLit :: (EvalEnv r s m) => StructLit -> m VT.Tree
evalStructLit (wpVal -> StructLit decls) = do
  sid <- allocOID
  foldM evalDecl (VT.mkStructTree (VT.emptyStruct{VT.stcID = sid})) decls

simpleStringLitToStr :: (EvalEnv r s m) => SimpleStringLit -> m (Either VT.Tree String)
simpleStringLitToStr (wpVal -> SimpleStringLit segs) = do
  (asM, aSegs, aExprs) <-
    foldM
      ( \(accCurStrM, accItpSegs, accItpExprs) seg -> case seg of
          UnicodeVal x -> return (maybe (Just [x]) (\y -> Just $ y ++ [x]) accCurStrM, accItpSegs, accItpExprs)
          InterpolationStr (wpVal -> Interpolation e) -> do
            t <- evalExpr e
            -- First append the current string segment to the accumulator if the current string segment exists, then
            -- append the interpolation segment. Finally reset the current string segment to Nothing.
            return
              ( Nothing
              , accItpSegs ++ (maybe [] (\y -> [VT.IplSegStr y]) accCurStrM ++ [VT.IplSegExpr $ length accItpExprs])
              , accItpExprs ++ [t]
              )
      )
      (Nothing, [], [])
      segs
  let rSegs = maybe aSegs (\x -> aSegs ++ [VT.IplSegStr x]) asM
  if
    | null rSegs -> return $ Right ""
    | not (null aExprs) ->
        return $ Left $ VT.mkMutableTree $ VT.mkItpMutable rSegs aExprs
    | length rSegs == 1, VT.IplSegStr s <- head rSegs -> return $ Right s
    | otherwise -> throwErrSt $ printf "invalid simple string literal: %s" (show segs)

-- | Evaluates a declaration in a struct. It returns the updated struct tree.
evalDecl :: (EvalEnv r s m) => VT.Tree -> Declaration -> m VT.Tree
evalDecl x decl = case VT.treeNode x of
  VT.TNBottom _ -> return x
  VT.TNBlock block -> case wpVal decl of
    Embedding ed -> do
      v <- evalEmbedding False ed
      oid <- allocOID
      let adder = VT.EmbedSAdder oid v
      addNewBlockElem adder block
    EllipsisDecl (wpVal -> Ellipsis cM) ->
      maybe
        (return (VT.mkBlockTree block))
        (\_ -> throwError "default constraints are not implemented yet")
        cM
    FieldDecl (wpVal -> AST.Field ls e) -> do
      sfa <- evalFDeclLabels ls e
      addNewBlockElem sfa block
    DeclLet (wpVal -> LetClause ident binde) -> do
      val <- evalExpr binde
      let adder = VT.LetSAdder (wpVal ident) val
      addNewBlockElem adder block
  _ -> throwErrSt "invalid struct"

evalEmbedding :: (EvalEnv r s m) => Bool -> Embedding -> m VT.Tree
evalEmbedding _ (wpVal -> AliasExpr e) = evalExpr e
evalEmbedding
  isListCompreh
  ( wpVal ->
      EmbedComprehension
        (wpVal -> Comprehension (wpVal -> Clauses (wpVal -> GuardClause ge) cls) lit)
    ) = do
    gev <- evalExpr ge
    clsv <- mapM evalClause cls
    sv <- evalStructLit lit
    return $ VT.mkMutableTree $ VT.Compreh $ VT.mkComprehension isListCompreh (VT.IterClauseIf gev : clsv) sv
evalEmbedding
  isListCompreh
  ( wpVal ->
      EmbedComprehension (wpVal -> Comprehension (wpVal -> Clauses (wpVal -> ForClause i jM fe) cls) lit)
    ) = do
    fev <- evalExpr fe
    clsv <- mapM evalClause cls
    sv <- evalStructLit lit
    return $
      VT.mkMutableTree $
        VT.Compreh $
          VT.mkComprehension isListCompreh (VT.IterClauseFor (wpVal i) (wpVal <$> jM) fev : clsv) sv
evalEmbedding _ _ = throwErrSt "invalid embedding"

evalClause :: (EvalEnv r s m) => Clause -> m (VT.IterClause VT.Tree)
evalClause c = case wpVal c of
  ClauseStartClause (wpVal -> GuardClause e) -> do
    t <- evalExpr e
    return $ VT.IterClauseIf t
  ClauseStartClause (wpVal -> ForClause (wpVal -> i) jM e) -> do
    t <- evalExpr e
    return $ VT.IterClauseFor i (wpVal <$> jM) t
  ClauseLetClause (wpVal -> LetClause (wpVal -> ident) le) -> do
    lt <- evalExpr le
    return $ VT.IterClauseLet ident lt
  _ -> throwErrSt $ printf "invalid clause: %s" (show c)

evalFDeclLabels :: (EvalEnv r s m) => [AST.Label] -> AST.Expression -> m (VT.BlockElemAdder VT.Tree)
evalFDeclLabels lbls e =
  case lbls of
    [] -> throwErrSt "empty labels"
    [l1] ->
      do
        val <- evalExpr e
        mkAdder l1 val
    l1 : l2 : rs ->
      do
        sf2 <- evalFDeclLabels (l2 : rs) e
        sid <- allocOID
        let val = VT.mkStructTree $ VT.mkStructFromAdders sid [sf2]
        mkAdder l1 val
 where
  mkAdder :: (EvalEnv r s m) => Label -> VT.Tree -> m (VT.BlockElemAdder VT.Tree)
  mkAdder (wpVal -> Label le) val = case wpVal le of
    AST.LabelName ln c ->
      let attr = VT.LabelAttr{VT.lbAttrCnstr = cnstrFrom c, VT.lbAttrIsIdent = isVar ln}
       in case ln of
            (toIDentLabel -> Just key) ->
              return $ VT.StaticSAdder key (VT.staticFieldMker val attr)
            (toDynLabel -> Just se) -> do
              selTree <- evalExpr se
              oid <- allocOID
              return $ VT.DynamicSAdder oid (VT.DynamicField oid attr selTree False val)
            (toSStrLabel -> Just ss) -> do
              rE <- simpleStringLitToStr ss
              case rE of
                Right str -> return $ VT.StaticSAdder str (VT.staticFieldMker val attr)
                Left t -> do
                  oid <- allocOID
                  return $ VT.DynamicSAdder oid (VT.DynamicField oid attr t True val)
            _ -> throwErrSt "invalid label"
    AST.LabelPattern pe -> do
      pat <- evalExpr pe
      oid <- allocOID
      return (VT.CnstrSAdder oid pat val)

  -- Returns the label name and the whether the label is static.
  toIDentLabel :: LabelName -> Maybe String
  toIDentLabel (wpVal -> LabelID (wpVal -> ident)) = Just ident
  toIDentLabel _ = Nothing

  toDynLabel :: LabelName -> Maybe AST.Expression
  toDynLabel (wpVal -> LabelNameExpr lne) = Just lne
  toDynLabel _ = Nothing

  toSStrLabel :: LabelName -> Maybe AST.SimpleStringLit
  toSStrLabel (wpVal -> LabelString ls) = Just ls
  toSStrLabel _ = Nothing

  cnstrFrom :: AST.LabelConstraint -> VT.StructFieldCnstr
  cnstrFrom c = case c of
    RegularLabel -> VT.SFCRegular
    OptionalLabel -> VT.SFCOptional
    RequiredLabel -> VT.SFCRequired

  isVar :: LabelName -> Bool
  isVar (wpVal -> LabelID _) = True
  -- Labels which are quoted or expressions are not variables.
  isVar _ = False

{- | Insert a new element into the struct. If the field is already in the struct, then unify the field with the new
field.
-}
addNewBlockElem :: (Common.Env r s m) => VT.BlockElemAdder VT.Tree -> VT.Block VT.Tree -> m VT.Tree
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
evalListLit (wpVal -> AST.EmbeddingList es) = do
  xs <- mapM (evalEmbedding True) es
  return $ VT.mkListTree xs

evalUnaryExpr :: (EvalEnv r s m) => UnaryExpr -> m VT.Tree
evalUnaryExpr ue = do
  t <- case wpVal ue of
    UnaryExprPrimaryExpr primExpr -> evalPrimExpr primExpr
    UnaryExprUnaryOp op e -> evalUnaryOp op e
  return $ VT.setExpr t (Just (AST.ExprUnaryExpr ue <$ ue))

builtinOpNameTable :: [(String, VT.Tree)]
builtinOpNameTable =
  -- bounds
  map (\b -> (show b, VT.mkBoundsTree [VT.BdType b])) [minBound :: VT.BdType .. maxBound :: VT.BdType]
    -- built-in function names
    -- We use the function to distinguish the identifier from the string literal.
    ++ builtinMutableTable

evalPrimExpr :: (EvalEnv r s m) => PrimaryExpr -> m VT.Tree
evalPrimExpr e = case wpVal e of
  (PrimExprOperand op) -> case wpVal op of
    OpLiteral lit -> evalLiteral lit
    OperandName (wpVal -> Identifier (wpVal -> ident)) -> case lookup ident builtinOpNameTable of
      Just v -> return v
      Nothing -> mkVarLinkTree ident
    OpExpression expr -> do
      x <- evalExpr expr
      return $ x{VT.treeIsRootOfSubTree = True}
  (PrimExprSelector primExpr sel) -> do
    p <- evalPrimExpr primExpr
    evalSelector e sel p
  (PrimExprIndex primExpr idx) -> do
    p <- evalPrimExpr primExpr
    evalIndex e idx p
  (PrimExprArguments primExpr aes) -> do
    p <- evalPrimExpr primExpr
    args <- mapM evalExpr aes
    replaceFuncArgs p args

-- | Create a new identifier reference.
mkVarLinkTree :: (MonadError String m) => String -> m VT.Tree
mkVarLinkTree var = do
  let mut = VT.mkRefMutable var []
  return $ VT.mkMutableTree mut

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
evalSelector _ astSel oprnd = do
  let f sel = VT.appendSelToRefTree oprnd (VT.mkAtomTree (VT.String sel))
  case wpVal astSel of
    IDSelector ident -> return $ f (wpVal ident)
    AST.StringSelector s -> do
      rE <- simpleStringLitToStr s
      case rE of
        Left _ -> return $ VT.mkBottomTree $ printf "selector should not have interpolation"
        Right str -> return $ f str

evalIndex ::
  (EvalEnv r s m) => PrimaryExpr -> AST.Index -> VT.Tree -> m VT.Tree
evalIndex _ (wpVal -> AST.Index e) oprnd = do
  sel <- evalExpr e
  return $ VT.appendSelToRefTree oprnd sel

{- | Evaluates the unary operator.

unary operator should only be applied to atoms.
-}
evalUnaryOp :: (EvalEnv r s m) => UnaryOp -> UnaryExpr -> m VT.Tree
evalUnaryOp op e = do
  t <- evalUnaryExpr e
  let tWithE = VT.setExpr t (Just (AST.ExprUnaryExpr e <$ e))
  return $ VT.mkNewTree (VT.TNMutable $ VT.mkUnaryOp op tWithE)

{- | order of arguments is important for disjunctions.

left is always before right.
-}
evalBinary :: (EvalEnv r s m) => BinaryOp -> Expression -> Expression -> m VT.Tree
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary (wpVal -> AST.Disjoin) e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  case op of
    (wpVal -> AST.Unify) -> return $ flattenUnify lt rt
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
  ((isLStar, lt), (isRStar, rt)) <- case (wpVal e1, wpVal e2) of
    ( ExprUnaryExpr (wpVal -> UnaryExprUnaryOp (wpVal -> Star) se1)
      , ExprUnaryExpr (wpVal -> UnaryExprUnaryOp (wpVal -> Star) se2)
      ) -> do
        l <- evalUnaryExpr se1
        r <- evalUnaryExpr se2
        return ((,) True l, (,) True r)
    (ExprUnaryExpr (wpVal -> UnaryExprUnaryOp (wpVal -> Star) se1), _) -> do
      l <- evalUnaryExpr se1
      r <- evalExpr e2
      return ((,) True l, (,) False r)
    (_, ExprUnaryExpr (wpVal -> UnaryExprUnaryOp (wpVal -> Star) se2)) -> do
      l <- evalExpr e1
      r <- evalUnaryExpr se2
      return ((,) False l, (,) True r)
    (_, _) -> do
      l <- evalExpr e1
      r <- evalExpr e2
      return ((,) False l, (,) False r)
  let r = flattenDisj (VT.DisjTerm isLStar lt) (VT.DisjTerm isRStar rt)
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
  i <- gets Common.getID
  let j = i + 1
  modify (`Common.setID` j)
  return j
