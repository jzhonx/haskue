{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Util.BuildASTExpr where

import qualified AST
import Common (Env)
import Control.Monad (foldM)
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

buildASTExpr :: (Env r s m) => Bool -> Tree -> m AST.Expression
buildASTExpr cr t = case treeNode t of
  TNTop -> return $ AST.litCons (pure AST.TopLit)
  TNBottom _ -> return $ AST.litCons (pure AST.BottomLit)
  TNAtom a -> return $ (AST.litCons . aToLiteral) a
  TNBounds b -> return $ buildBoundsASTExpr b
  TNBlock block@(Block{blkStruct = s})
    | Just ev <- blkNonStructValue block -> buildASTExpr cr ev
    | let dynsReady = all (isJust . rtrNonMut . dsfLabel) (IntMap.elems $ stcDynFields s)
    , let embedsReady = all (isJust . rtrNonMut . embValue) (IntMap.elems $ blkEmbeds block)
    , dynsReady && embedsReady ->
        buildStructASTExpr cr block
    -- If dynamic fields or embedded values are not ready, then we need to use the original expression.
    | otherwise -> maybe (buildStructASTExpr cr block) return (treeExpr t)
  TNList l -> do
    ls <-
      mapM
        ( \x -> do
            e <- buildASTExpr cr x
            return $ pure $ AST.AliasExpr e
        )
        (lstSubs l)
    return $ AST.litCons $ AST.ListLit AST.<^> pure (AST.EmbeddingList ls)
  TNDisj dj ->
    if null (dsjDefault dj)
      then
        disjunctsToAST cr (dsjDisjuncts dj)
      else
        disjunctsToAST cr (defDisjunctsFromDisj dj)
  TNMutable mut -> case mut of
    RegOp op -> buildRegOpASTExpr cr op
    Ref _ -> maybe (throwErrSt $ printf "expression not found for reference: %s" (show t)) return (treeExpr t)
    Compreh cph -> do
      ce <- buildComprehASTExpr cr cph
      return $
        AST.litCons $
          AST.LitStructLit AST.<^> pure (AST.StructLit [AST.Embedding AST.<<^>> AST.EmbedComprehension AST.<^> ce])
    DisjOp _ -> maybe (throwErrSt "expression not found for disjunction") return (treeExpr t)
    UOp u -> maybe (buildUnifyOpASTExpr cr u) return (treeExpr t)
    Itp _ -> maybe (throwErrSt "expression not found for interpolation") return (treeExpr t)
  TNAtomCnstr c -> maybe (return $ cnsValidator c) return (treeExpr t)
  TNRefCycle _ -> return $ AST.litCons (pure AST.TopLit)
  TNCnstredVal c -> maybe (throwErrSt "expression not found for cnstred value") return (cnsedOrigExpr c)

-- | Patterns are not included in the AST.
buildStructASTExpr :: (Env r s m) => Bool -> Block -> m AST.Expression
buildStructASTExpr concrete block@(Block{blkStruct = s}) =
  let
    processSField :: (Env r s m) => (T.Text, Field) -> m AST.Declaration
    processSField (sel, sf) = do
      e <- buildASTExpr concrete (ssfValue sf)
      return $
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

    processDynField :: (Env r s m) => DynamicField -> m AST.Declaration
    processDynField sf = do
      le <- buildASTExpr concrete (dsfLabel sf)
      ve <- buildASTExpr concrete (dsfValue sf)
      return $
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

    processEmbed :: (Env r s m) => Embedding -> m AST.Declaration
    processEmbed embed = case treeNode (embValue embed) of
      TNMutable (Compreh c) -> do
        ce <- buildComprehASTExpr concrete c
        return $ AST.Embedding AST.<<^>> AST.EmbedComprehension AST.<^> ce
      _ -> do
        e <- buildASTExpr concrete (embValue embed)
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
   in
    do
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
      embeds <- mapM processEmbed (IntMap.elems $ blkEmbeds block)

      return $ AST.litCons $ AST.LitStructLit AST.<^> pure (AST.StructLit (stcs ++ dyns ++ embeds))

buildComprehASTExpr :: (Env r s m) => Bool -> Comprehension -> m AST.Comprehension
buildComprehASTExpr c cph = do
  start <- buildStartClause (head (cphIterClauses cph))
  rest <- mapM buildIterClause (tail (cphIterClauses cph))

  e <- buildASTExpr c (cphStruct cph)
  sl <- case AST.wpVal e of
    AST.ExprUnaryExpr
      ( AST.wpVal ->
          AST.UnaryExprPrimaryExpr
            ( AST.wpVal ->
                AST.PrimExprOperand
                  ( AST.wpVal ->
                      AST.OpLiteral
                        (AST.wpVal -> AST.LitStructLit l)
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
      ve <- buildASTExpr c val
      return (AST.GuardClause ve)
    IterClauseFor varName secVarM val -> do
      ve <- buildASTExpr c val
      return (AST.ForClause (pure varName) (pure <$> secVarM) ve)
    _ -> throwErrSt "start clause should not be let clause"

  buildIterClause clause = case clause of
    IterClauseLet varName val -> do
      ve <- buildASTExpr c val
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
  BdNE a -> litOp AST.NE (AST.wpVal $ aToLiteral a)
  BdNumCmp (BdNumCmpCons o n) -> case o of
    BdLT -> numOp AST.LT n
    BdLE -> numOp AST.LE n
    BdGT -> numOp AST.GT n
    BdGE -> numOp AST.GE n
  BdStrMatch m -> case m of
    BdReMatch s -> litOp AST.ReMatch (AST.wpVal $ AST.strToLit s)
    BdReNotMatch s -> litOp AST.ReNotMatch (AST.wpVal $ AST.strToLit s)
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

disjunctsToAST :: (Env r s m) => Bool -> [Tree] -> m AST.Expression
disjunctsToAST c ds = do
  xs <- mapM (buildASTExpr c) ds
  return $
    foldr1
      (\x acc -> pure $ AST.ExprBinaryOp (pure AST.Disjoin) x acc)
      xs

buildUnifyOpASTExpr :: (Env r s m) => Bool -> UnifyOp -> m AST.Expression
buildUnifyOpASTExpr c op
  | fstConj Seq.:<| rest <- ufConjuncts op
  , -- The rest should be a non-empty sequence.
    _ Seq.:|> _ <- rest = do
      leftMost <- buildASTExpr c fstConj
      foldM
        ( \acc x -> do
            right <- buildASTExpr c x
            return $ pure $ AST.ExprBinaryOp (pure AST.Unify) acc right
        )
        leftMost
        rest
  | otherwise = throwErrSt "UnifyOp should have at least two conjuncts"

buildRegOpASTExpr :: (Env r s m) => Bool -> RegularOp -> m AST.Expression
buildRegOpASTExpr c op = do
  if c || requireMutableConcrete op
    -- If the expression must be concrete, but due to incomplete evaluation, we need to use original expression.
    then build
    else maybe build (buildASTExpr c) (ropValue op)
 where
  build = case ropOpType op of
    UnaryOpType uop
      | x Seq.:<| _ <- ropArgs op -> buildUnaryExpr uop x
    BinOpType bop
      | x Seq.:<| y Seq.:<| _ <- ropArgs op -> buildBinaryExpr bop x y
    _ -> throwErrSt $ "Unsupported operation type: " ++ show (ropOpType op)

buildUnaryExpr :: (Env r s m) => AST.UnaryOp -> Tree -> m AST.Expression
buildUnaryExpr op t = do
  let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
  te <- buildASTExpr c t
  case AST.wpVal te of
    (AST.ExprUnaryExpr ue) -> return $ AST.ExprUnaryExpr AST.<<^>> AST.UnaryExprUnaryOp op AST.<^> ue
    _ ->
      return $
        AST.ExprUnaryExpr
          AST.<<^>> AST.UnaryExprUnaryOp op
          AST.<<^>> AST.UnaryExprPrimaryExpr
          AST.<<^>> AST.PrimExprOperand
          AST.<<^>> AST.OpExpression
          AST.<^> te

buildBinaryExpr :: (Env r s m) => AST.BinaryOp -> Tree -> Tree -> m AST.Expression
buildBinaryExpr op l r = do
  let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
  xe <- buildASTExpr c l
  ye <- buildASTExpr c r
  return $ pure $ AST.ExprBinaryOp op xe ye

buildArgsExpr :: (Env r s m) => String -> [Tree] -> m AST.Expression
buildArgsExpr func ts = do
  ets <- mapM (buildASTExpr False) ts
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