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
import Common (Env, HasConfig (..))
import Control.Monad (foldM)
import Control.Monad.Reader (ask, asks, runReaderT)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (isJust)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Exception (throwErrSt)
import Text.Printf (printf)
import Value.Atom
import Value.Bounds
import Value.Comprehension
import Value.Constraint
import Value.Disj
import Value.List
import Value.Mutable
import Value.Struct
import Value.Tree
import Value.UnifyOp

buildASTExpr :: (Env r s m) => Tree -> m AST.Expression
buildASTExpr t = do
  conf <- ask
  runReaderT (buildASTExprExt t) (BuildConfig False conf)

buildASTExprDebug :: (Env r s m) => Tree -> m AST.Expression
buildASTExprDebug t = do
  conf <- ask
  runReaderT (buildASTExprExt t) (BuildConfig True conf)

class HasBuildConfig r where
  getIsDebug :: r -> Bool

type BEnv r s m = (Env r s m, HasBuildConfig r)

data BuildConfig a = BuildConfig Bool a

instance HasBuildConfig (BuildConfig a) where
  getIsDebug (BuildConfig e _) = e

instance (HasConfig a) => HasConfig (BuildConfig a) where
  getConfig (BuildConfig _ r) = getConfig r
  setConfig (BuildConfig e r) c = BuildConfig e (setConfig r c)

buildASTExprExt :: (BEnv r s m) => Tree -> m AST.Expression
buildASTExprExt t = case treeNode t of
  TNTop -> return $ AST.litCons (pure AST.TopLit)
  TNBottom _ -> return $ AST.litCons (pure AST.BottomLit)
  TNAtom a -> return $ (AST.litCons . aToLiteral) a
  TNBounds b -> return $ buildBoundsASTExpr b
  TNBlock block@(Block{blkStruct = s})
    | Just ev <- blkNonStructValue block -> buildASTExprExt ev
    | let dynsReady = all (isJust . rtrNonMut . dsfLabel) (IntMap.elems $ stcDynFields s)
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
  TNMutable mut@(Mutable mop _) -> case mop of
    RegOp op -> buildRegOpASTExpr mut op
    Ref _ -> maybe (throwErrSt $ printf "expression not found for reference: %s" (show t)) return (treeExpr t)
    Compreh cph -> do
      ce <- buildComprehASTExpr cph
      return $
        AST.litCons $
          AST.LitStructLit AST.<^> pure (AST.StructLit [AST.Embedding AST.<<^>> AST.EmbedComprehension AST.<^> ce])
    DisjOp _ -> maybe (throwErrSt "expression not found for disjunction") return (treeExpr t)
    UOp u -> maybe (buildUnifyOpASTExpr u) return (treeExpr t)
    Itp _ -> maybe (throwErrSt "expression not found for interpolation") return (treeExpr t)
  TNAtomCnstr c -> maybe (return $ cnsValidator c) return (treeExpr t)
  TNRefCycle _ -> return $ AST.litCons (pure AST.TopLit)

-- | Patterns are not included in the AST.
buildStructASTExpr :: (BEnv r s m) => Block -> m AST.Expression
buildStructASTExpr block@(Block{blkStruct = s}) = do
  stcs <-
    mapM
      ( \l -> do
          pair <-
            maybe
              (throwErrSt $ "struct field not found: " ++ show l)
              (\f -> return (l, f))
              (lookupStructField l s)
          processSField pair
      )
      (stcOrdLabels s)
  dyns <-
    foldM
      ( \acc dsf ->
          -- If the label can be evaluated to an atom, then the dynamic field should be already in the static
          -- fields.
          maybe
            ( do
                decl <- processDynField dsf
                return (decl : acc)
            )
            (const $ return acc)
            (rtrAtom $ dsfLabel dsf)
      )
      []
      (IntMap.elems $ stcDynFields s)
  patterns <- mapM processPattern (IntMap.elems $ stcCnstrs s)
  embeds <- mapM processEmbed (IntMap.elems $ blkEmbeds block)

  isDebug <- asks getIsDebug
  let fields = stcs ++ dyns ++ embeds ++ (if isDebug then patterns else [])
      e = AST.litCons $ AST.LitStructLit AST.<^> pure (AST.StructLit fields)
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

buildComprehASTExpr :: (BEnv r s m) => Comprehension -> m AST.Comprehension
buildComprehASTExpr cph = do
  start <- buildStartClause (head (cphIterClauses cph))
  rest <- mapM buildIterClause (tail (cphIterClauses cph))

  e <- buildASTExprExt (cphStruct cph)
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
    IterClauseIf val -> do
      ve <- buildASTExprExt val
      return (AST.GuardClause ve)
    IterClauseFor varName secVarM val -> do
      ve <- buildASTExprExt val
      return (AST.ForClause (pure varName) (pure <$> secVarM) ve)
    _ -> throwErrSt "start clause should not be let clause"

  buildIterClause clause = case clause of
    IterClauseLet varName val -> do
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

buildRegOpASTExpr :: (BEnv r s m) => Mutable -> RegularOp -> m AST.Expression
buildRegOpASTExpr mut op = do
  if requireMutableConcrete op
    -- If the expression must be concrete, but due to incomplete evaluation, we need to use original expression.
    then build
    else maybe build buildASTExprExt (getMutVal mut)
 where
  build = case ropOpType op of
    UnaryOpType uop
      | x Seq.:<| _ <- ropArgs op -> buildUnaryExpr uop x
    BinOpType bop
      | x Seq.:<| y Seq.:<| _ <- ropArgs op -> buildBinaryExpr bop x y
    CloseFunc -> return $ AST.litCons (AST.strToLit (T.pack "close func"))
    _ -> throwErrSt $ "Unsupported operation type: " ++ show (ropOpType op)

buildUnaryExpr :: (BEnv r s m) => AST.UnaryOp -> Tree -> m AST.Expression
buildUnaryExpr op t = do
  -- let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
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
  -- let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
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