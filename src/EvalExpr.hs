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
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import Exception (throwErrSt)
import Text.Printf (printf)
import Value

type EvalEnv r s m = (Common.Env r s m, Common.IDStore s)

evalSourceFile :: (EvalEnv r s m) => SourceFile -> m Tree
evalSourceFile (SourceFile decls) = evalStructLit (pure $ StructLit decls)

{- | evalExpr and all expr* should return the same level tree cursor.
The label and the evaluated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every eval* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the addr of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
evalExpr :: (EvalEnv r s m) => Expression -> m Tree
evalExpr e = do
  t <- case anVal e of
    (ExprUnaryExpr ue) -> evalUnaryExpr ue
    (ExprBinaryOp op e1 e2) -> evalBinary op e1 e2
  return $ setExpr t (Just e)

evalLiteral :: (EvalEnv r s m) => Literal -> m Tree
evalLiteral (anVal -> LitStructLit s) = evalStructLit s
evalLiteral (anVal -> ListLit l) = evalListLit l
evalLiteral (anVal -> StringLit (anVal -> SimpleStringL s)) = do
  rE <- simpleStringLitToStr s
  return $ case rE of
    Left t -> t
    Right str -> mkAtomTree $ String str
evalLiteral lit = return v
 where
  v = case anVal lit of
    IntLit i -> mkAtomTree $ Int i
    FloatLit a -> mkAtomTree $ Float a
    BoolLit b -> mkAtomTree $ Bool b
    NullLit -> mkAtomTree Null
    TopLit -> mkNewTree TNTop
    BottomLit -> mkBottomTree ""
    _ -> error "evalLiteral: invalid literal"

evalStructLit :: (EvalEnv r s m) => StructLit -> m Tree
evalStructLit (anVal -> StructLit decls) = do
  sid <- allocOID
  foldM evalDecl (mkBlockTree (emptyBlock{blkID = sid})) decls

simpleStringLitToStr :: (EvalEnv r s m) => SimpleStringLit -> m (Either Tree T.Text)
simpleStringLitToStr (anVal -> SimpleStringLit segs) = do
  (asM, aSegs, aExprs) <-
    foldM
      ( \(accCurStrM, accItpSegs, accItpExprs) seg -> case seg of
          UnicodeVal x ->
            return
              -- TODO: efficiency
              ( maybe (Just (T.singleton x)) (\y -> Just $ T.snoc y x) accCurStrM
              , accItpSegs
              , accItpExprs
              )
          InterpolationStr (anVal -> AST.Interpolation e) -> do
            t <- evalExpr e
            -- First append the current string segment to the accumulator if the current string segment exists, then
            -- append the interpolation segment. Finally reset the current string segment to Nothing.
            return
              ( Nothing
              , accItpSegs ++ (maybe [] (\y -> [IplSegStr y]) accCurStrM ++ [IplSegExpr $ length accItpExprs])
              , accItpExprs ++ [t]
              )
      )
      (Nothing, [], [])
      segs
  let rSegs = maybe aSegs (\x -> aSegs ++ [IplSegStr x]) asM
  if
    | null rSegs -> return $ Right T.empty
    | not (null aExprs) ->
        return $ Left $ mkMutableTree $ mkItpMutable rSegs aExprs
    | length rSegs == 1, IplSegStr s <- head rSegs -> return $ Right s
    | otherwise -> throwErrSt $ printf "invalid simple string literal: %s" (show segs)

-- | Evaluates a declaration in a struct. It returns the updated struct tree.
evalDecl :: (EvalEnv r s m) => Tree -> Declaration -> m Tree
evalDecl x decl = case treeNode x of
  TNBottom _ -> return x
  TNBlock block -> case anVal decl of
    AST.Embedding ed -> do
      v <- evalEmbedding False ed
      oid <- allocOID
      let adder = EmbedSAdder oid v
      addNewBlockElem adder block
    EllipsisDecl (anVal -> Ellipsis cM) ->
      maybe
        (return (mkBlockTree block))
        (\_ -> throwError "default constraints are not implemented yet")
        cM
    FieldDecl (anVal -> AST.Field ls e) -> do
      sfa <- evalFDeclLabels ls e
      addNewBlockElem sfa block
    DeclLet (anVal -> LetClause ident binde) -> do
      val <- evalExpr binde
      let adder = LetSAdder (anVal ident) val
      addNewBlockElem adder block
  _ -> throwErrSt "invalid struct"

evalEmbedding :: (EvalEnv r s m) => Bool -> AST.Embedding -> m Tree
evalEmbedding _ (anVal -> AliasExpr e) = evalExpr e
evalEmbedding
  isListCompreh
  ( anVal ->
      EmbedComprehension
        (anVal -> AST.Comprehension (anVal -> Clauses (anVal -> GuardClause ge) cls) lit)
    ) = do
    gev <- evalExpr ge
    clsv <- mapM evalClause cls
    sv <- evalStructLit lit
    return $ mkMutableTree $ withEmptyMutFrame $ Compreh $ mkComprehension isListCompreh (ComprehClauseIf gev : clsv) sv
evalEmbedding
  isListCompreh
  ( anVal ->
      EmbedComprehension (anVal -> AST.Comprehension (anVal -> Clauses (anVal -> ForClause i jM fe) cls) lit)
    ) = do
    fev <- evalExpr fe
    clsv <- mapM evalClause cls
    sv <- evalStructLit lit
    return $
      mkMutableTree $
        withEmptyMutFrame $
          Compreh $
            mkComprehension isListCompreh (ComprehClauseFor (anVal i) (anVal <$> jM) fev : clsv) sv
evalEmbedding _ _ = throwErrSt "invalid embedding"

evalClause :: (EvalEnv r s m) => Clause -> m ComprehClause
evalClause c = case anVal c of
  ClauseStartClause (anVal -> GuardClause e) -> do
    t <- evalExpr e
    return $ ComprehClauseIf t
  ClauseStartClause (anVal -> ForClause (anVal -> i) jM e) -> do
    t <- evalExpr e
    return $ ComprehClauseFor i (anVal <$> jM) t
  ClauseLetClause (anVal -> LetClause (anVal -> ident) le) -> do
    lt <- evalExpr le
    return $ ComprehClauseLet ident lt
  _ -> throwErrSt $ printf "invalid clause: %s" (show c)

evalFDeclLabels :: (EvalEnv r s m) => [AST.Label] -> AST.Expression -> m BlockElemAdder
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
        let val = mkBlockTree $ mkBlockFromAdder sid sf2
        mkAdder l1 val
 where
  mkAdder :: (EvalEnv r s m) => Label -> Tree -> m BlockElemAdder
  mkAdder (anVal -> Label le) val = case anVal le of
    AST.LabelName ln c ->
      let attr = LabelAttr{lbAttrCnstr = cnstrFrom c, lbAttrIsIdent = isVar ln}
       in case ln of
            (toIDentLabel -> Just key) ->
              return $ StaticSAdder key (staticFieldMker val attr)
            (toDynLabel -> Just se) -> do
              selTree <- evalExpr se
              oid <- allocOID
              return $ DynamicSAdder oid (DynamicField oid attr selTree False val)
            (toSStrLabel -> Just ss) -> do
              rE <- simpleStringLitToStr ss
              case rE of
                Right str -> return $ StaticSAdder str (staticFieldMker val attr)
                Left t -> do
                  oid <- allocOID
                  return $ DynamicSAdder oid (DynamicField oid attr t True val)
            _ -> throwErrSt "invalid label"
    AST.LabelPattern pe -> do
      pat <- evalExpr pe
      oid <- allocOID
      return (CnstrSAdder oid pat val)

  -- Returns the label name and the whether the label is static.
  toIDentLabel :: LabelName -> Maybe T.Text
  toIDentLabel (anVal -> LabelID (anVal -> ident)) = Just ident
  toIDentLabel _ = Nothing

  toDynLabel :: LabelName -> Maybe AST.Expression
  toDynLabel (anVal -> LabelNameExpr lne) = Just lne
  toDynLabel _ = Nothing

  toSStrLabel :: LabelName -> Maybe AST.SimpleStringLit
  toSStrLabel (anVal -> LabelString ls) = Just ls
  toSStrLabel _ = Nothing

  cnstrFrom :: AST.LabelConstraint -> StructFieldCnstr
  cnstrFrom c = case c of
    RegularLabel -> SFCRegular
    OptionalLabel -> SFCOptional
    RequiredLabel -> SFCRequired

  isVar :: LabelName -> Bool
  isVar (anVal -> LabelID _) = True
  -- Labels which are quoted or expressions are not variables.
  isVar _ = False

{- | Insert a new element into the struct. If the field is already in the struct, then unify the field with the new
field.
-}
addNewBlockElem :: (Common.Env r s m) => BlockElemAdder -> Block -> m Tree
addNewBlockElem adder block@(IsBlockStruct struct) = case adder of
  (StaticSAdder name sf) ->
    maybe
      ( case lookupBlockStubVal name block of
          -- The label is already in the struct, so we need to unify the field.
          [BlkStubField extSF] ->
            let
              unifySFOp =
                Value.Field
                  { ssfValue = mkMutableTree (mkUnifyOp [ssfValue extSF, ssfValue sf])
                  , ssfAttr = mergeAttrs (ssfAttr extSF) (ssfAttr sf)
                  , ssfObjects = Set.empty
                  }
             in
              return $
                mkBlockTree $
                  setBlockStruct
                    (struct{stcFields = Map.insert name unifySFOp (stcFields struct)})
                    block
                      { blkStaticFields = Map.insert name unifySFOp (blkStaticFields block)
                      }
          [BlkStubLet _] -> return $ aliasErr name
          -- The label is not seen before in the struct.
          [] ->
            return $
              mkBlockTree
                ( setBlockStruct
                    ( struct
                        { stcFields = Map.insert name sf (stcFields struct)
                        }
                    )
                    block
                      { blkStaticFields = Map.insert name sf (blkStaticFields block)
                      , blkOrdLabels = blkOrdLabels block ++ [BlockFieldLabel name]
                      }
                )
          _ -> return $ aliasErr name
      )
      return
      (existCheck name False)
  (DynamicSAdder i dsf) ->
    return . mkBlockTree $
      block
        { blkOrdLabels = blkOrdLabels block ++ [BlockDynFieldOID i]
        , blkDynFields = IntMap.insert i dsf (blkDynFields block)
        }
  (CnstrSAdder i pattern val) ->
    return . mkBlockTree $
      block
        { blkCnstrs = IntMap.insert i (StructCnstr i pattern val) (blkCnstrs block)
        }
  (LetSAdder name val) ->
    return $
      fromMaybe
        -- The name is not seen before in the block.
        (mkBlockTree $ insertBlockLet name val block)
        (existCheck name True)
  (EmbedSAdder i val) -> do
    let embed = mkEmbedding i val
    return $ mkBlockTree $ block{blkEmbeds = IntMap.insert i embed (blkEmbeds block)}
 where
  aliasErr name = mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name
  lbRedeclErr name = mkBottomTree $ printf "%s redeclared in same scope" name

  -- Checks if name is already in the block. If it is, then return an error message.
  existCheck :: T.Text -> Bool -> Maybe Tree
  existCheck name isNameLet =
    case (lookupBlockStubVal name block, isNameLet) of
      ([BlkStubField f], True)
        | lbAttrIsIdent (ssfAttr f) -> Just $ aliasErr name
      ([BlkStubLet _], True) -> Just $ lbRedeclErr name
      ([BlkStubLet _], False) -> Just $ aliasErr name
      ([_, _], _) -> Just $ aliasErr name
      _ -> Nothing
addNewBlockElem _ _ = throwErrSt "addNewBlockElem: expected a Block with Struct"

evalListLit :: (EvalEnv r s m) => AST.ElementList -> m Tree
evalListLit (anVal -> AST.EmbeddingList es) = do
  xs <- mapM (evalEmbedding True) es
  return $ mkListTree xs

evalUnaryExpr :: (EvalEnv r s m) => UnaryExpr -> m Tree
evalUnaryExpr ue = do
  t <- case anVal ue of
    UnaryExprPrimaryExpr primExpr -> evalPrimExpr primExpr
    UnaryExprUnaryOp op e -> evalUnaryOp op e
  return $ setExpr t (Just (AST.ExprUnaryExpr ue <$ ue))

builtinOpNameTable :: [(String, Tree)]
builtinOpNameTable =
  -- bounds
  map (\b -> (show b, mkBoundsTreeFromList [BdType b])) [minBound :: BdType .. maxBound :: BdType]
    -- built-in function names
    -- We use the function to distinguish the identifier from the string literal.
    ++ builtinMutableTable

evalPrimExpr :: (EvalEnv r s m) => PrimaryExpr -> m Tree
evalPrimExpr e = case anVal e of
  (PrimExprOperand op) -> case anVal op of
    OpLiteral lit -> evalLiteral lit
    OperandName (anVal -> Identifier (anVal -> ident)) -> case lookup (T.unpack ident) builtinOpNameTable of
      Just v -> return v
      Nothing -> return $ mkMutableTree $ withEmptyMutFrame $ Ref $ emptyIdentRef ident
    OpExpression expr -> do
      x <- evalExpr expr
      return $ x{treeIsRootOfSubTree = True}
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

-- | Creates a new function tree for the original function with the arguments applied.
replaceFuncArgs :: (MonadError String m) => Tree -> [Tree] -> m Tree
replaceFuncArgs t args = case t of
  IsRegOp mut fn ->
    return . setTN t $
      TNMutable $
        setMutOp
          (RegOp $ fn{ropArgs = Seq.fromList args})
          mut
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
  (EvalEnv r s m) => PrimaryExpr -> AST.Selector -> Tree -> m Tree
evalSelector _ astSel oprnd = do
  let f sel = appendSelToRefTree oprnd (mkAtomTree (String sel))
  case anVal astSel of
    IDSelector ident -> return $ f (anVal ident)
    AST.StringSelector s -> do
      rE <- simpleStringLitToStr s
      case rE of
        Left _ -> return $ mkBottomTree $ printf "selector should not have interpolation"
        Right str -> return $ f str

evalIndex ::
  (EvalEnv r s m) => PrimaryExpr -> AST.Index -> Tree -> m Tree
evalIndex _ (anVal -> AST.Index e) oprnd = do
  sel <- evalExpr e
  return $ appendSelToRefTree oprnd sel

{- | Evaluates the unary operator.

unary operator should only be applied to atoms.
-}
evalUnaryOp :: (EvalEnv r s m) => UnaryOp -> UnaryExpr -> m Tree
evalUnaryOp op e = do
  t <- evalUnaryExpr e
  let tWithE = setExpr t (Just (AST.ExprUnaryExpr e <$ e))
  return $ mkNewTree (TNMutable $ mkUnaryOp op tWithE)

{- | order of arguments is important for disjunctions.

left is always before right.
-}
evalBinary :: (EvalEnv r s m) => BinaryOp -> Expression -> Expression -> m Tree
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary (anVal -> AST.Disjoin) e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  case op of
    (anVal -> AST.Unify) -> return $ flattenUnify lt rt
    _ -> return $ mkNewTree (TNMutable $ mkBinaryOp op lt rt)

flattenUnify :: Tree -> Tree -> Tree
flattenUnify l r = case getLeftAcc of
  Just acc -> mkMutableTree $ mkUnifyOp (toList acc ++ [r])
  Nothing -> mkMutableTree $ mkUnifyOp [l, r]
 where
  getLeftAcc = case treeNode l of
    -- The left tree is an accumulator only if it is a unify op.
    TNMutable (MutOp (UOp u)) -> Just (ufConjuncts u)
    _ -> Nothing

evalDisj :: (EvalEnv r s m) => Expression -> Expression -> m Tree
evalDisj e1 e2 = do
  ((isLStar, lt), (isRStar, rt)) <- case (anVal e1, anVal e2) of
    ( ExprUnaryExpr (anVal -> UnaryExprUnaryOp (anVal -> Star) se1)
      , ExprUnaryExpr (anVal -> UnaryExprUnaryOp (anVal -> Star) se2)
      ) -> do
        l <- evalUnaryExpr se1
        r <- evalUnaryExpr se2
        return ((,) True l, (,) True r)
    (ExprUnaryExpr (anVal -> UnaryExprUnaryOp (anVal -> Star) se1), _) -> do
      l <- evalUnaryExpr se1
      r <- evalExpr e2
      return ((,) True l, (,) False r)
    (_, ExprUnaryExpr (anVal -> UnaryExprUnaryOp (anVal -> Star) se2)) -> do
      l <- evalExpr e1
      r <- evalUnaryExpr se2
      return ((,) False l, (,) True r)
    (_, _) -> do
      l <- evalExpr e1
      r <- evalExpr e2
      return ((,) False l, (,) False r)
  let r = flattenDisj (DisjTerm isLStar lt) (DisjTerm isRStar rt)
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
flattenDisj :: DisjTerm -> DisjTerm -> Tree
flattenDisj l r = case getLeftAcc of
  Just acc -> mkMutableTree $ mkDisjoinOp (acc Seq.|> r)
  Nothing -> mkMutableTree $ mkDisjoinOp (Seq.fromList [l, r])
 where
  getLeftAcc = case treeNode (dstValue l) of
    TNMutable (MutOp (DisjOp dj))
      -- The left term is an accumulator only if it is a disjoin op and not marked nor the root.
      -- If the left term is a marked term, it implies that it is a root.
      | not (dstMarked l) && not (treeIsRootOfSubTree (dstValue l)) -> Just (djoTerms dj)
    _ -> Nothing

allocOID :: (EvalEnv r s m) => m Int
allocOID = do
  i <- gets Common.getID
  let j = i + 1
  modify (`Common.setID` j)
  return j
