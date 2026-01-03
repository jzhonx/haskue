{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Export.AST (
  buildExpr,
  buildBoundASTExpr,
  bdRep,
  buildExprDebug,
)
where

import qualified AST
import Control.Monad (foldM)
import Control.Monad.Except (Except, MonadError (..))
import Control.Monad.RWS.Strict (RWST, runRWST)
import Control.Monad.Reader (asks)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Exception (throwErrSt)
import StringIndex (ShowWTIndexer (..), TextIndex, TextIndexer, textToTextIndex)
import Text.Printf (printf)
import Value.Atom
import Value.Bounds
import Value.Comprehension
import Value.Constraint
import Value.Disj
import Value.DisjoinOp
import Value.Export.Debug
import Value.Fix
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.UnifyOp
import Value.Val

type EM = RWST BuildConfig () TextIndexer (Except String)

buildExpr :: Val -> TextIndexer -> Except String (AST.Expression, TextIndexer)
buildExpr t tier = do
  (a, s, _) <- runRWST (buildExprExt t) (BuildConfig False) tier
  return (a, s)

buildExprDebug :: Val -> TextIndexer -> Except String (AST.Expression, TextIndexer)
buildExprDebug t tier = do
  (a, s, _) <- runRWST (buildExprExt t) (BuildConfig True) tier
  return (a, s)

newtype BuildConfig = BuildConfig {isDebug :: Bool}

buildExprExt :: Val -> EM AST.Expression
buildExprExt t@Val{isSCyclic = True} = buildSCyclicASTExpr t
buildExprExt t@(IsValMutable mut) | IsNoVal <- t = buildMutableASTExpr mut t
buildExprExt t = case valNode t of
  VNTop -> return $ AST.litCons (pure AST.TopLit)
  VNBottom _ -> return $ AST.litCons (pure AST.BottomLit)
  VNAtom a -> return $ (AST.litCons . aToLiteral) a
  VNBounds b -> return $ buildBoundsASTExpr b
  VNStruct struct -> buildStructASTExpr struct t
  VNList l -> do
    ls <-
      mapM
        ( \x -> do
            e <- buildExprExt x
            return $ pure $ AST.AliasExpr e
        )
        (toList l.final)
    return $ AST.litCons $ AST.ListLit AST.<^> pure (AST.EmbeddingList ls)
  VNDisj dj
    | null (rtrDisjDefVal dj) -> disjunctsToAST (dsjDisjuncts dj)
    | otherwise -> disjunctsToAST (defDisjunctsFromDisj dj)
  VNAtomCnstr ac -> buildAtomCnstrASTExpr ac t
  VNFix r -> buildFixASTExpr r t
  VNNoVal -> do
    isDebug <- asks isDebug
    if isDebug
      then return (AST.idCons $ pure $ T.pack "NoVal")
      else throwExprNotFound t

throwExprNotFound :: Val -> EM a
throwExprNotFound t = do
  rep <- treeToRepString t
  throwError $ printf "expression not found for %s, tree rep: %s" (showValSymbol t) rep

buildMutableASTExpr :: SOp -> Val -> EM AST.Expression
buildMutableASTExpr mut t = do
  -- If in debug mode, we build the expression because arguments might have updated values even though the mutval is
  -- not ready.
  isDebug <- asks isDebug
  if isDebug
    then buildMutableASTExprForce mut t
    -- TODO: handle parenthese in origExpr. Currently origExpr does not have parenthese.
    else maybe (buildMutableASTExprForce mut t) return (origExpr t)

buildAtomCnstrASTExpr :: AtomCnstr -> Val -> EM AST.Expression
buildAtomCnstrASTExpr ac t = do
  isDebug <- asks isDebug
  if isDebug
    then buildArgsExpr "atomCnstr" [mkAtomVal ac.value, cnsValidator ac]
    -- TODO: for non-core type, we should not build AST in non-debug mode.
    else maybe (buildExprExt $ cnsValidator ac) return (origExpr t)

buildMutableASTExprForce :: SOp -> Val -> EM AST.Expression
buildMutableASTExprForce (SOp mop _) t = case mop of
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

buildFixASTExpr :: Fix -> Val -> EM AST.Expression
buildFixASTExpr r t = do
  isDebug <- asks isDebug
  if isDebug
    then return (AST.idCons $ pure $ T.pack "Fix")
    else do
      if r.unknownExists
        then maybe (throwExprNotFound t) return (origExpr t)
        else buildExprExt (mkNewVal r.val)

buildSCyclicASTExpr :: Val -> EM AST.Expression
buildSCyclicASTExpr inner = do
  isDebug <- asks isDebug
  if isDebug
    then buildArgsExpr "SC" [inner{isSCyclic = False}]
    else throwErrSt "structural cycle expression should not be built in non-debug mode"

buildStaticFieldExpr :: (TextIndex, Field) -> EM AST.Declaration
buildStaticFieldExpr (sIdx, sf) = do
  sel <- tshow sIdx
  e <- buildExprExt (ssfValue sf)
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

buildDynFieldExpr :: DynamicField -> EM AST.Declaration
buildDynFieldExpr sf = do
  le <- buildExprExt (dsfLabel sf)
  ve <- buildExprExt (dsfValue sf)
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

buildPatternExpr :: StructCnstr -> EM AST.Declaration
buildPatternExpr pat = do
  pte <- buildExprExt (scsPattern pat)
  ve <- buildExprExt (scsValue pat)
  return $
    AST.FieldDecl
      AST.<^> pure (AST.Field [labelPatternCons pte] ve)

buildLetExpr :: (TextIndex, Binding) -> EM AST.Declaration
buildLetExpr (ident, binding) = do
  s <- tshow ident
  ve <- buildExprExt binding.value
  let
    letClause :: AST.LetClause
    letClause = pure (AST.LetClause (pure s) ve)
  return (pure $ AST.DeclLet letClause)

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

buildStructASTExpr :: Struct -> Val -> EM AST.Expression
buildStructASTExpr struct t = do
  isDebug <- asks isDebug
  if isDebug
    then buildStructASTExprDebug struct t
    else buildStructASTExprNormal struct t

buildStructASTExprDebug :: Struct -> Val -> EM AST.Expression
buildStructASTExprDebug s _ = do
  statics <- mapM buildStaticFieldExpr (Map.toList $ stcFields s)
  dynamics <- mapM buildDynFieldExpr (IntMap.elems $ stcDynFields s)
  patterns <- mapM buildPatternExpr (IntMap.elems $ stcCnstrs s)
  lets <- mapM buildLetExpr (Map.toList $ stcBindings s)
  let
    decls = statics ++ dynamics ++ patterns ++ lets
    e = AST.litCons $ AST.LitStructLit AST.<^> pure (AST.StructLit decls)
  return e

buildStructASTExprNormal :: Struct -> Val -> EM AST.Expression
buildStructASTExprNormal _ (IsEmbedVal v) = buildExprExt v
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
        (origExpr t)

buildComprehASTExpr :: Comprehension -> EM AST.Comprehension
buildComprehASTExpr cph = do
  let argList = toList cph.args
      clauses = init argList
      structTmpl = last argList
  start <- buildStartClause (head clauses)
  rest <- mapM buildIterClause (tail clauses)

  e <- buildExprExt (getValFromIterClause structTmpl)
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
      ve <- buildExprExt val
      return (AST.GuardClause ve)
    ComprehArgFor varNameIdx secVarIdxM val -> do
      varName <- tshow varNameIdx
      secVarM <- case secVarIdxM of
        Just sIdx -> Just <$> tshow sIdx
        Nothing -> return Nothing
      ve <- buildExprExt val
      return (AST.ForClause (pure varName) (pure <$> secVarM) ve)
    _ -> throwErrSt "start clause should not be let clause"

  buildIterClause clause = case clause of
    ComprehArgLet varNameIdx val -> do
      varName <- tshow varNameIdx
      ve <- buildExprExt val
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

disjunctsToAST :: [Val] -> EM AST.Expression
disjunctsToAST ds = do
  xs <- mapM buildExprExt ds
  isDebug <- asks isDebug
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

buildUnifyOpASTExpr :: UnifyOp -> EM AST.Expression
buildUnifyOpASTExpr op
  | fstConj Seq.:<| rest <- op.conjs
  , -- The rest should be a non-empty sequence.
    _ Seq.:|> _ <- rest = do
      leftMost <- buildExprExt fstConj
      foldM
        ( \acc x -> do
            right <- buildExprExt x
            return $ pure $ AST.ExprBinaryOp (pure AST.Unify) acc right
        )
        leftMost
        rest
  | otherwise = throwErrSt "UnifyOp should have at least two conjuncts"

buildDisjoinOpASTExpr :: DisjoinOp -> Val -> EM AST.Expression
buildDisjoinOpASTExpr op t = do
  isDebug <- asks isDebug
  if isDebug
    then go
    else throwExprNotFound t
 where
  go
    | fstDisj Seq.:<| rest <- djoTerms op
    , -- The rest should be a non-empty sequence.
      _ Seq.:|> _ <- rest = do
        leftMost <- buildExprExt (dstValue fstDisj)
        foldM
          ( \acc x -> do
              right <- buildExprExt (dstValue x)
              return $ pure $ AST.ExprBinaryOp (pure AST.DisjoinDebugOp) acc right
          )
          leftMost
          rest
    | otherwise = throwErrSt "UnifyOp should have at least two conjuncts"

buildRefASTExpr :: Reference -> EM AST.Expression
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
            xe <- buildExprExt x
            return $ pure $ AST.PrimExprIndex acc (pure $ AST.Index xe)
        )
        varE
        xs
    return $ AST.ExprUnaryExpr AST.<^> pure (AST.UnaryExprPrimaryExpr r)
  RefIndex xs -> do
    case xs of
      (x Seq.:<| rest) -> do
        xe <- buildExprExt x
        v <- case AST.anVal xe of
          AST.ExprUnaryExpr
            (AST.anVal -> AST.UnaryExprPrimaryExpr v) -> return v
          _ -> throwErrSt "the first element of RefIndex should be a primary expression"
        r <-
          foldM
            ( \acc y -> do
                ye <- buildExprExt y
                return $ pure $ AST.PrimExprIndex acc (pure $ AST.Index ye)
            )
            v
            rest
        return $ AST.ExprUnaryExpr AST.<^> pure (AST.UnaryExprPrimaryExpr r)
      _ -> throwErrSt "RefIndex should have at least one element"

buildRegOpASTExpr :: RegularOp -> EM AST.Expression
buildRegOpASTExpr op = case ropOpType op of
  UnaryOpType uop
    | x Seq.:<| _ <- ropArgs op -> buildUnaryExpr uop x
  BinOpType bop
    | x Seq.:<| y Seq.:<| _ <- ropArgs op -> buildBinaryExpr bop x y
  CloseFunc -> return $ AST.litCons (AST.strToLit (T.pack "close func"))
  _ -> throwErrSt $ "Unsupported operation type: " ++ show (ropOpType op)

buildUnaryExpr :: AST.UnaryOp -> Val -> EM AST.Expression
buildUnaryExpr op t = do
  te <- buildExprExt t
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

buildBinaryExpr :: AST.BinaryOp -> Val -> Val -> EM AST.Expression
buildBinaryExpr op l r = do
  xe <- buildExprExt l
  ye <- buildExprExt r
  return $ pure $ AST.ExprBinaryOp op xe ye

buildArgsExpr :: String -> [Val] -> EM AST.Expression
buildArgsExpr func ts = do
  ets <- mapM buildExprExt ts
  return $
    AST.ExprUnaryExpr
      AST.<<^>> AST.UnaryExprPrimaryExpr
      AST.<^> pure
        (AST.PrimExprArguments (AST.idToPrimExpr (pure $ T.pack func)) ets)