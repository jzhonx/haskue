{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Util.BuildASTExpr (
  buildASTExpr,
  buildBoundASTExpr,
  bdRep,
  buildASTExprDebug,
)
where

import qualified AST
import Control.Monad (foldM)
import Control.Monad.Reader (MonadReader, ask, asks, runReaderT)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Env (ErrorEnv, HasConfig (..))
import Exception (throwErrSt)
import Feature (Feature, mkStringFeature)
import StringIndex (ShowWithTextIndexer (..), TextIndex, TextIndexerMonad, textToTextIndex)
import Text.Printf (printf)
import Value.Atom
import Value.Block
import Value.Bounds
import Value.Comprehension
import Value.Constraint
import Value.Disj
import Value.DisjoinOp
import Value.List
import Value.Mutable
import Value.Reference
import Value.Tree
import Value.UnifyOp
import Value.Util.TreeRep

buildASTExpr :: (ErrorEnv m, MonadReader r m, TextIndexerMonad s m) => Tree -> m AST.Expression
buildASTExpr t = do
  conf <- ask
  runReaderT (buildASTExprExt t) (BuildConfig False conf)

buildASTExprDebug :: (ErrorEnv m, TextIndexerMonad s m) => Tree -> m AST.Expression
buildASTExprDebug t = runReaderT (buildASTExprExt t) (BuildConfig True ())

class HasBuildConfig r where
  getIsDebug :: r -> Bool

type BEnv r s m = (ErrorEnv m, MonadReader r m, HasBuildConfig r, TextIndexerMonad s m)

data BuildConfig a = BuildConfig
  { bcIsDebug :: Bool
  , bcOther :: a
  }

instance HasBuildConfig (BuildConfig a) where
  getIsDebug = bcIsDebug

instance (HasConfig a) => HasConfig (BuildConfig a) where
  getConfig bc = getConfig (bcOther bc)
  setConfig bc c = bc{bcOther = setConfig (bcOther bc) c}

buildASTExprExt :: (BEnv r s m) => Tree -> m AST.Expression
buildASTExprExt t@Tree{isUnifiedWithRC = True} = buildUWCASTExpr t
buildASTExprExt t@Tree{isSCyclic = True} = buildSCyclicASTExpr t
buildASTExprExt t@(IsTGenOp mut) | IsNoVal <- t = buildMutableASTExpr mut t
buildASTExprExt t = case treeNode t of
  TNTop -> return $ AST.litCons (pure AST.TopLit)
  TNBottom _ -> return $ AST.litCons (pure AST.BottomLit)
  TNAtom a -> return $ (AST.litCons . aToLiteral) a
  TNBounds b -> return $ buildBoundsASTExpr b
  TNStruct struct -> buildStructASTExpr struct t
  TNList l -> do
    ls <-
      mapM
        ( \x -> do
            e <- buildASTExprExt x
            return $ pure $ AST.AliasExpr e
        )
        (toList l.final)
    return $ AST.litCons $ AST.ListLit AST.<^> pure (AST.EmbeddingList ls)
  TNDisj dj
    | null (rtrDisjDefVal dj) -> disjunctsToAST (dsjDisjuncts dj)
    | otherwise -> disjunctsToAST (defDisjunctsFromDisj dj)
  TNAtomCnstr ac -> buildAtomCnstrASTExpr ac t
  TNRefCycle -> buildRCASTExpr t
  TNRefSubCycle _ -> maybe (throwExprNotFound t) return (treeExpr t)
  TNNoVal -> throwExprNotFound t

throwExprNotFound :: (ErrorEnv m) => Tree -> m a
throwExprNotFound t = do
  let rep = buildRepTree t defaultTreeRepBuildOption
  throwErrSt $ printf "expression not found for %s, tree rep: %s" (showTreeSymbol t) (repToString 0 rep)

buildMutableASTExpr :: (BEnv r s m) => Mutable -> Tree -> m AST.Expression
buildMutableASTExpr mut t = do
  -- If in debug mode, we build the expression because arguments might have updated values even though the mutval is
  -- not ready.
  isDebug <- asks getIsDebug
  if isDebug
    then buildMutableASTExprForce mut t
    -- TODO: handle parenthese in treeExpr. Currently treeExpr does not have parenthese.
    else maybe (buildMutableASTExprForce mut t) return (treeExpr t)

buildAtomCnstrASTExpr :: (BEnv r s m) => AtomCnstr -> Tree -> m AST.Expression
buildAtomCnstrASTExpr ac t = do
  isDebug <- asks getIsDebug
  if isDebug
    then buildArgsExpr "atomCnstr" [mkAtomTree ac.value, cnsValidator ac]
    -- TODO: for non-core type, we should not build AST in non-debug mode.
    else maybe (buildASTExprExt $ cnsValidator ac) return (treeExpr t)

buildMutableASTExprForce :: (BEnv r s m) => Mutable -> Tree -> m AST.Expression
buildMutableASTExprForce (Mutable mop _) t = case mop of
  RegOp op -> buildRegOpASTExpr op
  Ref ref -> buildRefASTExpr ref
  Compreh cph -> do
    ce <- buildComprehASTExpr cph
    return $
      AST.litCons $
        AST.LitStructLit AST.<^> pure (AST.StructLit [AST.Embedding AST.<<^>> AST.EmbedComprehension AST.<^> ce])
  DisjOp dop -> buildDisjoinOpASTExpr dop t
  UOp u -> buildUnifyOpASTExpr u
  Itp _ -> throwExprNotFound t

buildRCASTExpr :: (BEnv r s m) => Tree -> m AST.Expression
buildRCASTExpr _ = do
  isDebug <- asks getIsDebug
  if isDebug
    then return (AST.idCons $ pure $ T.pack "RC")
    else throwErrSt "ref-cycle expression should not be built in non-debug mode"

buildUWCASTExpr :: (BEnv r s m) => Tree -> m AST.Expression
buildUWCASTExpr inner = do
  isDebug <- asks getIsDebug
  if isDebug
    then buildUnifyOpASTExpr (UnifyOp (Seq.fromList [mkNewTree TNRefCycle, inner]))
    else throwErrSt "unified-with-rc expression should not be built in non-debug mode"

buildSCyclicASTExpr :: (BEnv r s m) => Tree -> m AST.Expression
buildSCyclicASTExpr inner = do
  isDebug <- asks getIsDebug
  if isDebug
    then buildArgsExpr "SC" [inner{isSCyclic = False}]
    else throwErrSt "structural cycle expression should not be built in non-debug mode"

buildStaticFieldExpr :: (BEnv r s m) => (TextIndex, Field) -> m AST.Declaration
buildStaticFieldExpr (sIdx, sf) = do
  sel <- tshow sIdx
  e <- buildASTExprExt (ssfValue sf)
  let decl =
        AST.FieldDecl
          AST.<^> pure
            ( AST.Field
                [ labelCons (ssfAttr sf) $
                    if lbAttrIsIdent (ssfAttr sf)
                      then AST.LabelID AST.<^> pure sel
                      else AST.LabelString AST.<^> AST.strToSimpleStrLit sel
                ]
                e
            )
  return decl

buildDynFieldExpr :: (BEnv r s m) => DynamicField -> m AST.Declaration
buildDynFieldExpr sf = do
  le <- buildASTExprExt (dsfLabel sf)
  ve <- buildASTExprExt (dsfValue sf)
  let decl =
        AST.FieldDecl
          AST.<^> pure
            ( AST.Field
                [ labelCons
                    (dsfAttr sf)
                    ( if dsfLabelIsInterp sf
                        then pure $ AST.LabelNameExpr le
                        else pure $ AST.LabelNameExpr le
                    )
                ]
                ve
            )
  return decl

buildPatternExpr :: (BEnv r s m) => StructCnstr -> m AST.Declaration
buildPatternExpr pat = do
  pte <- buildASTExprExt (scsPattern pat)
  ve <- buildASTExprExt (scsValue pat)
  return $
    AST.FieldDecl
      AST.<^> pure (AST.Field [labelPatternCons pte] ve)

buildLetExpr :: (BEnv r s m) => (TextIndex, Binding) -> m AST.Declaration
buildLetExpr (ident, binding) = do
  s <- tshow ident
  ve <- buildASTExprExt binding.value
  let
    letClause :: AST.LetClause
    letClause = pure (AST.LetClause (pure s) ve)
  return (pure $ AST.DeclLet letClause)

-- buildEmbedExpr :: (BEnv r s m) => Embedding -> m AST.Declaration
-- buildEmbedExpr embed = case embValue embed of
--   IsTGenOp (MutOp (Compreh c)) -> do
--     ce <- buildComprehASTExpr c
--     return $ AST.Embedding AST.<<^>> AST.EmbedComprehension AST.<^> ce
--   _ -> do
--     e <- buildASTExprExt (embValue embed)
--     return $ AST.Embedding AST.<<^>> AST.AliasExpr AST.<^> e

labelCons :: LabelAttr -> AST.LabelName -> AST.Label
labelCons a ln =
  AST.Label
    AST.<^> pure
      ( AST.LabelName
          ln
          ( case lbAttrCnstr a of
              SFCRegular -> AST.RegularLabel
              SFCRequired -> AST.RequiredLabel
              SFCOptional -> AST.OptionalLabel
          )
      )
labelPatternCons :: AST.Expression -> AST.Label
labelPatternCons le = AST.Label AST.<^> pure (AST.LabelPattern le)

buildStructASTExpr :: (BEnv r s m) => Struct -> Tree -> m AST.Expression
buildStructASTExpr struct t = do
  isDebug <- asks getIsDebug
  if isDebug
    then buildStructASTExprDebug struct t
    else buildStructASTExprNormal struct t

buildStructASTExprDebug :: (BEnv r s m) => Struct -> Tree -> m AST.Expression
buildStructASTExprDebug s _ = do
  statics <- mapM buildStaticFieldExpr (Map.toList $ stcFields s)
  dynamics <- mapM buildDynFieldExpr (IntMap.elems $ stcDynFields s)
  patterns <- mapM buildPatternExpr (IntMap.elems $ stcCnstrs s)
  lets <- mapM buildLetExpr (Map.toList $ stcBindings s)
  -- embedValM <- maybe (return Nothing) buildASTExprExt s.stcEmbedVal
  let
    decls = statics ++ dynamics ++ patterns ++ lets
    e = AST.litCons $ AST.LitStructLit AST.<^> pure (AST.StructLit decls)
  return e

buildStructASTExprNormal :: (BEnv r s m) => Struct -> Tree -> m AST.Expression
buildStructASTExprNormal _ (IsEmbedVal v) = buildASTExprExt v
buildStructASTExprNormal s t = do
  r <- buildStructOrdLabels rtrString s
  case r of
    Just labels -> do
      fields <-
        mapM
          ( \l -> do
              li <- textToTextIndex l
              pair <-
                maybe
                  (throwErrSt $ "struct field not found: " ++ show l)
                  (\f -> return (li, f))
                  (lookupStructField li s)
              buildStaticFieldExpr pair
          )
          labels

      let decls = fields
          e = AST.litCons $ AST.LitStructLit AST.<^> pure (AST.StructLit decls)
      return e
    -- If not all dynamic fields can be resolved to string labels, we can not build the struct expression.
    Nothing ->
      maybe
        (throwErrSt "struct expression not found")
        return
        (treeExpr t)

buildComprehASTExpr :: (BEnv r s m) => Comprehension -> m AST.Comprehension
buildComprehASTExpr cph = do
  let argList = toList cph.args
      clauses = init argList
      structTmpl = last argList
  start <- buildStartClause (head clauses)
  rest <- mapM buildIterClause (tail clauses)

  e <- buildASTExprExt (getValFromIterClause structTmpl)
  sl <- case AST.anVal e of
    AST.ExprUnaryExpr
      ( AST.anVal ->
          AST.UnaryExprPrimaryExpr
            ( AST.anVal ->
                AST.PrimExprOperand
                  ( AST.anVal ->
                      AST.OpLiteral
                        (AST.anVal -> AST.LitStructLit l)
                    )
              )
        ) -> return l
    _ -> throwErrSt "struct lit is not found"
  return $
    pure $
      AST.Comprehension (pure $ AST.Clauses (pure start) (map pure rest)) sl
 where
  buildStartClause clause = case clause of
    ComprehArgIf val -> do
      ve <- buildASTExprExt val
      return (AST.GuardClause ve)
    ComprehArgFor varNameIdx secVarIdxM val -> do
      varName <- tshow varNameIdx
      secVarM <- case secVarIdxM of
        Just sIdx -> Just <$> tshow sIdx
        Nothing -> return Nothing
      ve <- buildASTExprExt val
      return (AST.ForClause (pure varName) (pure <$> secVarM) ve)
    _ -> throwErrSt "start clause should not be let clause"

  buildIterClause clause = case clause of
    ComprehArgLet varNameIdx val -> do
      varName <- tshow varNameIdx
      ve <- buildASTExprExt val
      return $ AST.ClauseLetClause (pure $ AST.LetClause (pure varName) ve)
    _ -> do
      start <- buildStartClause clause
      return $ AST.ClauseStartClause (pure start)

buildBoundsASTExpr :: Bounds -> AST.Expression
buildBoundsASTExpr bds = foldl1 (\acc x -> pure $ AST.ExprBinaryOp (pure AST.Unify) acc x) es
 where
  es = map buildBoundASTExpr (bdsList bds)

buildBoundASTExpr :: Bound -> AST.Expression
buildBoundASTExpr b = case b of
  BdNE a -> litOp AST.NE (AST.anVal $ aToLiteral a)
  BdNumCmp (BdNumCmpCons o n) -> case o of
    BdLT -> numOp AST.LT n
    BdLE -> numOp AST.LE n
    BdGT -> numOp AST.GT n
    BdGE -> numOp AST.GE n
  BdStrMatch m -> case m of
    BdReMatch s -> litOp AST.ReMatch (AST.anVal $ AST.strToLit s)
    BdReNotMatch s -> litOp AST.ReNotMatch (AST.anVal $ AST.strToLit s)
  BdType t -> AST.idCons (pure $ T.pack (show t))
  BdIsAtom a -> AST.litCons (aToLiteral a)
 where
  litOp :: AST.RelOpNode -> AST.LiteralNode -> AST.Expression
  litOp op l =
    let uop = pure $ AST.UnaRelOp op
        ue = AST.PrimExprOperand AST.<<^>> AST.OpLiteral AST.<^> pure l
     in AST.ExprUnaryExpr
          AST.<<^>> AST.UnaryExprUnaryOp uop
          AST.<<^>> AST.UnaryExprPrimaryExpr
          AST.<^> ue

  numOp :: AST.RelOpNode -> Number -> AST.Expression
  numOp op n =
    AST.ExprUnaryExpr
      AST.<<^>> AST.UnaryExprUnaryOp (pure $ AST.UnaRelOp op)
      AST.<<^>> AST.UnaryExprPrimaryExpr
      AST.<<^>> AST.PrimExprOperand
      AST.<<^>> AST.OpLiteral
      AST.<^> case n of
        NumInt i -> pure $ AST.IntLit i
        NumFloat f -> pure $ AST.FloatLit f

bdRep :: Bound -> String
bdRep b = case b of
  BdNE _ -> show AST.NE
  BdNumCmp (BdNumCmpCons o _) -> show o
  BdStrMatch m -> case m of
    BdReMatch _ -> show AST.ReMatch
    BdReNotMatch _ -> show AST.ReNotMatch
  BdType t -> show t
  BdIsAtom _ -> "="

disjunctsToAST :: (BEnv r s m) => [Tree] -> m AST.Expression
disjunctsToAST ds = do
  xs <- mapM buildASTExprExt ds
  isDebug <- asks getIsDebug
  -- We might print unresolved disjunctions in debug mode with only one disjunct.
  if isDebug && length xs < 2
    then case xs of
      [] -> return $ AST.litCons (pure AST.BottomLit)
      [x] -> return x
      _ -> throwErrSt "unreachable"
    else
      return $
        foldr1
          (\x acc -> pure $ AST.ExprBinaryOp (pure AST.Disjoin) x acc)
          xs

buildUnifyOpASTExpr :: (BEnv r s m) => UnifyOp -> m AST.Expression
buildUnifyOpASTExpr op
  | fstConj Seq.:<| rest <- ufConjuncts op
  , -- The rest should be a non-empty sequence.
    _ Seq.:|> _ <- rest = do
      leftMost <- buildASTExprExt fstConj
      foldM
        ( \acc x -> do
            right <- buildASTExprExt x
            return $ pure $ AST.ExprBinaryOp (pure AST.Unify) acc right
        )
        leftMost
        rest
  | otherwise = throwErrSt "UnifyOp should have at least two conjuncts"

buildDisjoinOpASTExpr :: (BEnv r s m) => DisjoinOp -> Tree -> m AST.Expression
buildDisjoinOpASTExpr op t = do
  isDebug <- asks getIsDebug
  if isDebug
    then go
    else throwExprNotFound t
 where
  go
    | fstDisj Seq.:<| rest <- djoTerms op
    , -- The rest should be a non-empty sequence.
      _ Seq.:|> _ <- rest = do
        leftMost <- buildASTExprExt (dstValue fstDisj)
        foldM
          ( \acc x -> do
              right <- buildASTExprExt (dstValue x)
              return $ pure $ AST.ExprBinaryOp (pure AST.DisjoinDebugOp) acc right
          )
          leftMost
          rest
    | otherwise = throwErrSt "UnifyOp should have at least two conjuncts"

buildRefASTExpr :: (BEnv r s m) => Reference -> m AST.Expression
buildRefASTExpr ref = case refArg ref of
  RefPath var xs -> do
    varS <- tshow var
    let varE =
          AST.PrimExprOperand
            AST.<<^>> AST.OperandName
            AST.<<^>> AST.Identifier
            AST.<^> pure varS
    r <-
      foldM
        ( \acc x -> do
            xe <- buildASTExprExt x
            return $ pure $ AST.PrimExprIndex acc (pure $ AST.Index xe)
        )
        varE
        xs
    return $ AST.ExprUnaryExpr AST.<^> pure (AST.UnaryExprPrimaryExpr r)
  RefIndex xs -> do
    case xs of
      (x Seq.:<| rest) -> do
        xe <- buildASTExprExt x
        v <- case AST.anVal xe of
          AST.ExprUnaryExpr
            (AST.anVal -> AST.UnaryExprPrimaryExpr v) -> return v
          _ -> throwErrSt "the first element of RefIndex should be a primary expression"
        r <-
          foldM
            ( \acc y -> do
                ye <- buildASTExprExt y
                return $ pure $ AST.PrimExprIndex acc (pure $ AST.Index ye)
            )
            v
            rest
        return $ AST.ExprUnaryExpr AST.<^> pure (AST.UnaryExprPrimaryExpr r)
      _ -> throwErrSt "RefIndex should have at least one element"

buildRegOpASTExpr :: (BEnv r s m) => RegularOp -> m AST.Expression
buildRegOpASTExpr op = case ropOpType op of
  UnaryOpType uop
    | x Seq.:<| _ <- ropArgs op -> buildUnaryExpr uop x
  BinOpType bop
    | x Seq.:<| y Seq.:<| _ <- ropArgs op -> buildBinaryExpr bop x y
  CloseFunc -> return $ AST.litCons (AST.strToLit (T.pack "close func"))
  _ -> throwErrSt $ "Unsupported operation type: " ++ show (ropOpType op)

buildUnaryExpr :: (BEnv r s m) => AST.UnaryOp -> Tree -> m AST.Expression
buildUnaryExpr op t = do
  te <- buildASTExprExt t
  case AST.anVal te of
    (AST.ExprUnaryExpr ue) -> return $ AST.ExprUnaryExpr AST.<<^>> AST.UnaryExprUnaryOp op AST.<^> ue
    _ ->
      return $
        AST.ExprUnaryExpr
          AST.<<^>> AST.UnaryExprUnaryOp op
          AST.<<^>> AST.UnaryExprPrimaryExpr
          AST.<<^>> AST.PrimExprOperand
          AST.<<^>> AST.OpExpression
          AST.<^> te

buildBinaryExpr :: (BEnv r s m) => AST.BinaryOp -> Tree -> Tree -> m AST.Expression
buildBinaryExpr op l r = do
  xe <- buildASTExprExt l
  ye <- buildASTExprExt r
  return $ pure $ AST.ExprBinaryOp op xe ye

buildArgsExpr :: (BEnv r s m) => String -> [Tree] -> m AST.Expression
buildArgsExpr func ts = do
  ets <- mapM buildASTExprExt ts
  return $
    AST.ExprUnaryExpr
      AST.<<^>> AST.UnaryExprPrimaryExpr
      AST.<^> pure
        (AST.PrimExprArguments (AST.idToPrimExpr (pure $ T.pack func)) ets)