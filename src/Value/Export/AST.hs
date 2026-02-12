{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Export.AST (
  buildExpr,
  buildBoundASTExpr,
  bdRep,
  buildExprDebug,
)
where

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
import qualified Syntax.AST as AST
import Syntax.Token as Token
import Text.Printf (printf)
import Value.Atom as Atom
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
buildExprExt t@(IsValMutable mut) | IsNoVal <- t = buildMutableASTExpr mut t
buildExprExt t = case valNode t of
  VNTop -> return $ AST.idCons "_"
  VNBottom _ -> buildBottom
  VNAtom a -> return $ (AST.litCons . aToLiteral) a
  VNBounds b -> return $ buildBoundsASTExpr b
  VNStruct struct -> buildStructASTExpr struct t
  VNList l -> do
    ls <-
      mapM
        ( \x -> do
            e <- buildExprExt x
            return $ AST.EmbeddingAlias $ AST.AliasExpr Nothing e
        )
        (toList l.final)
    return $ AST.litCons $ AST.LitList $ AST.ListLit emptyLoc (AST.EmbeddingList ls Nothing) emptyLoc
  VNDisj dj
    | null (rtrDisjDefVal dj) -> disjunctsToAST (toList $ dsjDisjuncts dj)
    | otherwise -> disjunctsToAST (defDisjunctsFromDisj dj)
  VNAtomCnstr ac -> buildAtomCnstrASTExpr ac t
  VNFix r -> buildFixASTExpr r t
  VNNoVal -> do
    isDebug <- asks isDebug
    if isDebug
      then return $ AST.idCons "NoVal"
      else throwExprNotFound t

buildBottom :: EM AST.Expression
buildBottom = return $ AST.litCons (AST.LitBasic $ AST.BottomLit $ mkTypeToken Token.Bottom)

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
  Index idx -> buildIndexASTExpr idx
  Compreh cph -> do
    ce <- buildComprehASTExpr cph
    return $
      AST.litCons $
        AST.LitStruct (AST.StructLit emptyLoc [AST.Embedding (AST.EmbedComprehension ce)] emptyLoc)
  DisjOp dop -> buildDisjoinOpASTExpr dop t
  UOp u -> buildUnifyOpASTExpr u
  Itp _ -> throwExprNotFound t

buildFixASTExpr :: Fix -> Val -> EM AST.Expression
buildFixASTExpr r t = do
  isDebug <- asks isDebug
  if isDebug
    then return (AST.idCons "Fix")
    else do
      if r.unknownExists
        then maybe (throwExprNotFound t) return (origExpr t)
        else buildExprExt (mkNewVal r.val)

buildStaticFieldExpr :: (TextIndex, Field) -> EM AST.Declaration
buildStaticFieldExpr (sIdx, sf) = do
  sel <- tshow sIdx
  e <- buildExprExt (ssfValue sf)
  let decl =
        AST.FieldDecl
          ( AST.Field
              [ labelCons (ssfAttr sf) $
                  if lbAttrIsIdent (ssfAttr sf)
                    then AST.LabelID (textIdentToken sel)
                    else AST.LabelString $ AST.textToSimpleStrLit sel
              ]
              (AST.AliasExpr Nothing e)
          )
  return decl

buildDynFieldExpr :: DynamicField -> EM AST.Declaration
buildDynFieldExpr sf = do
  le <- buildExprExt (dsfLabel sf)
  ve <- buildExprExt (dsfValue sf)
  let decl =
        AST.FieldDecl
          ( AST.Field
              [ labelCons
                  (dsfAttr sf)
                  (AST.LabelNameExpr emptyLoc (AST.AliasExpr Nothing le) emptyLoc)
              ]
              (AST.AliasExpr Nothing ve)
          )
  return decl

buildPatternExpr :: StructCnstr -> EM AST.Declaration
buildPatternExpr pat = do
  pte <- buildExprExt (scsPattern pat)
  ve <- buildExprExt (scsValue pat)
  return $ AST.FieldDecl (AST.Field [labelPatternCons pte] (AST.AliasExpr Nothing ve))

buildLetExpr :: (TextIndex, Val) -> EM AST.Declaration
buildLetExpr (ident, v) = do
  s <- tshow ident
  ve <- buildExprExt v
  let
    letClause :: AST.LetClause
    letClause = AST.LetClause emptyLoc (textIdentToken s) ve
  return (AST.DeclLet letClause)

labelCons :: LabelAttr -> AST.LabelName -> AST.Label
labelCons a ln =
  AST.Label
    ( AST.LabelName
        ln
        ( case lbAttrCnstr a of
            SFCRegular -> Nothing
            SFCRequired -> Just Exclamation
            SFCOptional -> Just QuestionMark
        )
    )
labelPatternCons :: AST.Expression -> AST.Label
labelPatternCons le = AST.Label (AST.LabelExpr emptyLoc (AST.AliasExpr Nothing le) emptyLoc)

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
    e = AST.litCons $ AST.LitStruct (AST.StructLit emptyLoc decls emptyLoc)
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
          e = AST.litCons $ AST.LitStruct (AST.StructLit emptyLoc decls emptyLoc)
      return e
    -- If not all dynamic fields can be resolved to string labels, we can not build the struct expression.
    Nothing ->
      maybe
        (throwErrSt "not all dynamic fields can be resolved to string labels")
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
  sl <- case e of
    AST.Unary (AST.Primary (AST.PrimExprOperand (AST.OpLiteral (AST.LitStruct l)))) -> return l
    _ -> throwErrSt "struct lit is not found"
  return $
    AST.Comprehension (AST.Clauses start rest) sl
 where
  buildStartClause clause = case clause of
    ComprehArgIf val -> do
      ve <- buildExprExt val
      return (AST.GuardClause emptyLoc ve)
    ComprehArgFor varNameIdx secVarIdxM val -> do
      varName <- tshow varNameIdx
      secVarM <- case secVarIdxM of
        Just sIdx -> Just <$> tshow sIdx
        Nothing -> return Nothing
      ve <- buildExprExt val
      return (AST.ForClause emptyLoc (textIdentToken varName) (textIdentToken <$> secVarM) ve)
    _ -> throwErrSt "start clause should not be let clause"

  buildIterClause clause = case clause of
    ComprehArgLet varNameIdx val -> do
      varName <- tshow varNameIdx
      ve <- buildExprExt val
      return $ AST.ClauseLet (AST.LetClause emptyLoc (textIdentToken varName) ve)
    _ -> do
      start <- buildStartClause clause
      return $ AST.ClauseStart start

buildBoundsASTExpr :: Bounds -> AST.Expression
buildBoundsASTExpr bds = foldl1 (AST.Binary (mkTypeToken Token.Unify)) es
 where
  es = map buildBoundASTExpr (bdsList bds)

buildBoundASTExpr :: Bound -> AST.Expression
buildBoundASTExpr b = case b of
  BdNE a -> litOp NotEqual (aToLiteral a)
  BdNumCmp (BdNumCmpCons o n) -> case o of
    BdLT -> numOp Less n
    BdLE -> numOp LessEqual n
    BdGT -> numOp Greater n
    BdGE -> numOp GreaterEqual n
  BdStrMatch m -> case m of
    BdReMatch s -> litOp Match (AST.textToSimpleStrLiteral s)
    BdReNotMatch s -> litOp NotMatch (AST.textToSimpleStrLiteral s)
  BdType t -> AST.idCons (T.pack (show t))
  BdIsAtom a -> AST.litCons (aToLiteral a)
 where
  litOp :: TokenType -> AST.Literal -> AST.Expression
  litOp op l =
    let
      ue = AST.PrimExprOperand $ AST.OpLiteral l
     in
      AST.Unary $ AST.UnaryOp (mkTypeToken op) $ AST.Primary ue

  numOp :: TokenType -> Number -> AST.Expression
  numOp op n =
    AST.Unary $
      AST.UnaryOp (mkTypeToken op) $
        AST.Primary $
          AST.PrimExprOperand $
            AST.OpLiteral $
              case n of
                NumInt i -> aToLiteral (Atom.Int i)
                NumFloat f -> aToLiteral (Atom.Float f)

bdRep :: Bound -> String
bdRep b = case b of
  BdNE _ -> show NotEqual
  BdNumCmp (BdNumCmpCons o _) -> show o
  BdStrMatch m -> case m of
    BdReMatch _ -> show Match
    BdReNotMatch _ -> show NotMatch
  BdType t -> show t
  BdIsAtom _ -> show Assign

disjunctsToAST :: [Val] -> EM AST.Expression
disjunctsToAST ds = do
  xs <- mapM buildExprExt ds
  isDebug <- asks isDebug
  -- We might print unresolved disjunctions in debug mode with only one disjunct.
  if isDebug && length xs < 2
    then case xs of
      [] -> buildBottom
      [x] -> return x
      _ -> throwErrSt "unreachable"
    else
      return $ foldr1 (AST.Binary (mkTypeToken Disjoin)) xs

buildUnifyOpASTExpr :: UnifyOp -> EM AST.Expression
buildUnifyOpASTExpr op
  | fstConj Seq.:<| rest <- op.conjs
  , -- The rest should be a non-empty sequence.
    _ Seq.:|> _ <- rest = do
      leftMost <- buildExprExt fstConj
      foldM
        ( \acc x -> do
            right <- buildExprExt x
            return $ AST.Binary (mkTypeToken Unify) acc right
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
              return $ AST.Binary (mkTypeToken Disjoin) acc right
          )
          leftMost
          rest
    | otherwise = throwErrSt "UnifyOp should have at least two conjuncts"

buildRefASTExpr :: Reference -> EM AST.Expression
buildRefASTExpr ref = do
  varS <- tshow ref.ident
  let varE = AST.PrimExprOperand $ AST.OpName $ AST.OperandName (textIdentToken varS)
  r <-
    foldM
      ( \acc x -> do
          xe <- buildExprExt x
          return $ AST.PrimExprIndex acc emptyLoc xe emptyLoc
      )
      varE
      ref.selectors
  return $ AST.Unary (AST.Primary r)

buildIndexASTExpr :: InplaceIndex -> EM AST.Expression
buildIndexASTExpr (InplaceIndex xs) = do
  case xs of
    (x Seq.:<| rest) -> do
      xe <- buildExprExt x
      v <- case xe of
        AST.Unary (AST.Primary v) -> return v
        _ -> throwErrSt "the first element of InplaceIndex should be a primary expression"
      r <-
        foldM
          ( \acc y -> do
              ye <- buildExprExt y
              return $ AST.PrimExprIndex acc emptyLoc ye emptyLoc
          )
          v
          rest
      return $ AST.Unary (AST.Primary r)
    _ -> throwErrSt "InplaceIndex should have at least one element"

buildRegOpASTExpr :: RegularOp -> EM AST.Expression
buildRegOpASTExpr op = case ropOpType op of
  UnaryOpType uop
    | x Seq.:<| _ <- ropArgs op -> buildUnaryExpr uop x
  BinOpType bop
    | x Seq.:<| y Seq.:<| _ <- ropArgs op -> buildBinaryExpr bop x y
  CloseFunc -> return $ AST.litCons (AST.textToSimpleStrLiteral (T.pack "close func"))
  _ -> throwErrSt $ "Unsupported operation type: " ++ show (ropOpType op)

buildUnaryExpr :: TokenType -> Val -> EM AST.Expression
buildUnaryExpr op t = do
  te <- buildExprExt t
  case te of
    (AST.Unary ue) -> return $ AST.Unary $ AST.UnaryOp (mkTypeToken op) ue
    _ ->
      return $
        AST.Unary $
          AST.UnaryOp (mkTypeToken op) $
            AST.Primary $
              AST.PrimExprOperand $
                AST.OpExpression emptyLoc te emptyLoc

buildBinaryExpr :: TokenType -> Val -> Val -> EM AST.Expression
buildBinaryExpr op l r = do
  xe <- buildExprExt l
  ye <- buildExprExt r
  return $ AST.Binary (mkTypeToken op) xe ye

buildArgsExpr :: String -> [Val] -> EM AST.Expression
buildArgsExpr func ts = do
  ets <- mapM buildExprExt ts
  return $
    AST.Unary $
      AST.Primary
        (AST.PrimExprArguments (AST.idToPrimExpr (T.pack func)) emptyLoc ets emptyLoc)