{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
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
import Common (ErrorEnv, HasConfig (..))
import Control.Monad (foldM)
import Control.Monad.Reader (MonadReader, ask, asks, runReaderT)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (isJust)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Exception (throwErrSt)
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

buildASTExpr :: (ErrorEnv m, MonadReader r m) => Tree -> m AST.Expression
buildASTExpr t = do
  conf <- ask
  runReaderT (buildASTExprExt t) (BuildConfig False conf)

buildASTExprDebug :: (ErrorEnv m) => Tree -> m AST.Expression
buildASTExprDebug t = runReaderT (buildASTExprExt t) (BuildConfig True ())

class HasBuildConfig r where
  getIsDebug :: r -> Bool

type BEnv r s m = (ErrorEnv m, MonadReader r m, HasBuildConfig r)

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
buildASTExprExt t = case treeNode t of
  TNTop -> return $ AST.litCons (pure AST.TopLit)
  TNBottom _ -> return $ AST.litCons (pure AST.BottomLit)
  TNAtom a -> return $ (AST.litCons . aToLiteral) a
  TNBounds b -> return $ buildBoundsASTExpr b
  TNBlock block
    | IsBlockEmbed ev <- block -> buildASTExprExt ev
    | let dynsReady = all (isJust . rtrNonMut . dsfLabel) (IntMap.elems $ blkDynFields block)
    , let embedsReady = all (isJust . rtrNonMut . embValue) (IntMap.elems $ blkEmbeds block)
    , dynsReady && embedsReady ->
        buildStructASTExpr block
    -- If dynamic fields or embedded values are not ready, then we need to use the original expression.
    | otherwise -> maybe (buildStructASTExpr block) return (treeExpr t)
  TNList l -> do
    ls <-
      mapM
        ( \x -> do
            e <- buildASTExprExt x
            return $ pure $ AST.AliasExpr e
        )
        (lstSubs l)
    return $ AST.litCons $ AST.ListLit AST.<^> pure (AST.EmbeddingList ls)
  TNDisj dj ->
    if null (dsjDefault dj)
      then
        disjunctsToAST (dsjDisjuncts dj)
      else
        disjunctsToAST (defDisjunctsFromDisj dj)
  TNMutable mut -> buildMutableASTExpr mut t
  TNAtomCnstr c -> maybe (buildASTExprExt $ cnsValidator c) return (treeExpr t)
  TNRefCycle -> buildRCASTExpr t
  TNRefSubCycle _ -> maybe (throwExprNotFound t) return (treeExpr t)
  TNNoValRef -> maybe (throwExprNotFound t) return (treeExpr t)

throwExprNotFound :: (ErrorEnv m) => Tree -> m a
throwExprNotFound t = do
  let rep = buildRepTree t defaultTreeRepBuildOption
  throwErrSt $ printf "expression not found for %s, tree rep: %s" (showTreeSymbol t) (repToString 0 rep)

buildMutableASTExpr :: (BEnv r s m) => Mutable -> Tree -> m AST.Expression
buildMutableASTExpr mut t
  | Just v <- getMutVal mut = buildASTExprExt v
  | otherwise = do
      -- If in debug mode, we build the expression because arguments might have updated values even though the mutval is
      -- not ready.
      isDebug <- asks getIsDebug
      if isDebug
        then buildMutableASTExprForce mut t
        else maybe (buildMutableASTExprForce mut t) return (treeExpr t)

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
buildRCASTExpr t =
  maybe
    ( do
        isDebug <- asks getIsDebug
        if isDebug
          then return (AST.idCons $ pure $ T.pack "RC")
          else throwExprNotFound t
    )
    return
    (treeExpr t)

buildStructASTExpr :: (BEnv r s m) => Block -> m AST.Expression
buildStructASTExpr block@(IsBlockStruct s) = do
  fields <-
    mapM
      ( \case
          BlockFieldLabel fl -> do
            pair <-
              maybe
                (throwErrSt $ "struct field not found: " ++ show fl)
                (\f -> return (fl, f))
                (lookupStructField fl s)
            processSField pair
          BlockDynFieldOID oid -> do
            dsf <-
              maybe
                (throwErrSt $ "dynamic field not found: " ++ show oid)
                return
                (IntMap.lookup oid (blkDynFields block))
            maybe
              (processDynField dsf)
              ( \al ->
                  maybe
                    -- The dynamic field might not be in the fields if the dynamic field is in the form of ("str")
                    (processDynField dsf)
                    (\f -> processSField (al, f))
                    (lookupStructField al s)
              )
              (rtrString $ dsfLabel dsf)
      )
      (dedupBlockLabels rtrString (blkDynFields block) (blkOrdLabels block))
  patterns <- mapM processPattern (IntMap.elems $ blkCnstrs block)
  embeds <- mapM processEmbed (IntMap.elems $ blkEmbeds block)

  isDebug <- asks getIsDebug
  let decls = fields ++ embeds ++ (if isDebug then patterns else [])
      e = AST.litCons $ AST.LitStructLit AST.<^> pure (AST.StructLit decls)
  return e
 where
  processSField :: (BEnv r s m) => (T.Text, Field) -> m AST.Declaration
  processSField (sel, sf) = do
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

  processDynField :: (BEnv r s m) => DynamicField -> m AST.Declaration
  processDynField sf = do
    le <- buildASTExprExt (dsfLabel sf)
    ve <- buildASTExprExt (dsfValue sf)
    let decl =
          AST.FieldDecl
            AST.<^> pure
              ( AST.Field
                  [ labelCons
                      (dsfAttr sf)
                      ( if dsfLabelIsInterp sf
                          then undefined
                          else pure $ AST.LabelNameExpr le
                      )
                  ]
                  ve
              )
    return decl

  processPattern :: (BEnv r s m) => StructCnstr -> m AST.Declaration
  processPattern pat = do
    pte <- buildASTExprExt (scsPattern pat)
    ve <- buildASTExprExt (scsValue pat)
    return $
      AST.FieldDecl
        AST.<^> pure (AST.Field [labelPatternCons pte] ve)

  processEmbed :: (BEnv r s m) => Embedding -> m AST.Declaration
  processEmbed embed = case treeNode (embValue embed) of
    TNMutable (MutOp (Compreh c)) -> do
      ce <- buildComprehASTExpr c
      return $ AST.Embedding AST.<<^>> AST.EmbedComprehension AST.<^> ce
    _ -> do
      e <- buildASTExprExt (embValue embed)
      return $ AST.Embedding AST.<<^>> AST.AliasExpr AST.<^> e

  labelCons :: LabelAttr -> AST.LabelName -> AST.Label
  labelCons attr ln =
    AST.Label
      AST.<^> pure
        ( AST.LabelName
            ln
            ( case lbAttrCnstr attr of
                SFCRegular -> AST.RegularLabel
                SFCRequired -> AST.RequiredLabel
                SFCOptional -> AST.OptionalLabel
            )
        )
  labelPatternCons :: AST.Expression -> AST.Label
  labelPatternCons le =
    AST.Label
      AST.<^> pure (AST.LabelPattern le)
buildStructASTExpr _ = throwErrSt "buildStructASTExpr: expected a Block with Struct"

buildComprehASTExpr :: (BEnv r s m) => Comprehension -> m AST.Comprehension
buildComprehASTExpr cph = do
  start <- buildStartClause (head (toList $ cphClauses cph))
  rest <- mapM buildIterClause (tail (toList $ cphClauses cph))

  e <- buildASTExprExt (cphBlock cph)
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
    ComprehClauseIf val -> do
      ve <- buildASTExprExt val
      return (AST.GuardClause ve)
    ComprehClauseFor varName secVarM val -> do
      ve <- buildASTExprExt val
      return (AST.ForClause (pure varName) (pure <$> secVarM) ve)
    _ -> throwErrSt "start clause should not be let clause"

  buildIterClause clause = case clause of
    ComprehClauseLet varName val -> do
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
    let varE =
          AST.PrimExprOperand
            AST.<<^>> AST.OperandName
            AST.<<^>> AST.Identifier
            AST.<^> pure var
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
        ( AST.PrimExprArguments
            ( AST.PrimExprOperand
                AST.<<^>> AST.OpLiteral
                AST.<^> AST.strToLit (T.pack func)
            )
            ets
        )