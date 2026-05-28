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

import Control.Monad (foldM)
import Control.Monad.Except (Except, MonadError (..))
import Control.Monad.RWS.Strict (RWST, runRWST)
import Control.Monad.Reader (asks)
import qualified Data.ByteString.Char8 as BC
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Exception (throwErrSt)
import StringIndex (TextIndex, TextIndexer, textIndexToBS, textToTextIndex)
import qualified Syntax.AST as AST
import Syntax.Token as Token
import Text.Printf (printf)
import Value.Atom as Atom
import Value.Bounds
import Value.Comprehension
import Value.Disj
import Value.DisjoinOp
import Value.Export.Debug
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.Val

type EM = RWST BuildConfig () TextIndexer (Except String)

buildExpr :: VNode -> TextIndexer -> Except String (AST.Expression, TextIndexer)
buildExpr t tier = do
  (a, s, _) <- runRWST (buildExprExt t) (BuildConfig False) tier
  return (a, s)

buildExprDebug :: VNode -> TextIndexer -> Except String (AST.Expression, TextIndexer)
buildExprDebug t tier = do
  (a, s, _) <- runRWST (buildExprExt t) (BuildConfig True) tier
  return (a, s)

newtype BuildConfig = BuildConfig {isDebug :: Bool}

buildExprExt :: VNode -> EM AST.Expression
buildExprExt t = case t of
  IsUnknown -> do
    isDebug <- asks isDebug
    if isDebug
      then
        if not (null (static $ constraints t))
          then buildStaticConstraintsExpr (static $ constraints t)
          else return $ AST.idCons "Unknown"
      else case origExpr t of
        Just e -> return e
        _
          | not (null (static $ constraints t)) ->
              buildStaticConstraintsExpr (static $ constraints t)
          | otherwise -> throwErrSt "cannot build expression for Unknown value without original expression"
  IsStruct s -> buildStructASTExpr s t
  _ -> buildValExprExt (value t)

buildValExprExt :: Val -> EM AST.Expression
buildValExprExt t = case t of
  VTop -> return $ AST.idCons "_"
  VBottom _ -> buildBottom
  VAtom a -> return $ (AST.litCons . aToLiteral) a
  VBounds b -> return $ buildBoundsASTExpr b
  VStruct struct -> buildStructASTExpr struct (mkValVN t)
  VList l -> do
    ls <-
      mapM
        ( \x -> do
            e <- buildExprExt x
            return $ AST.EmbeddingAlias $ AST.AliasExpr Nothing e
        )
        (toList l.final)
    return $ AST.litCons $ AST.LitList $ AST.ListLit emptyLoc (AST.EmbeddingList ls Nothing) emptyLoc
  VDisj dj
    | null (rtrDisjDefVal dj) -> disjunctsToAST (toList $ dsjDisjuncts dj)
    | otherwise -> disjunctsToAST (defDisjunctsFromDisj dj)
  VUnknown -> do
    isDebug <- asks isDebug
    if isDebug
      then return $ AST.idCons "Unknown"
      else throwErrSt "cannot build expression for Unknown value without original expression"
  VFuncAddr addr -> do
    isDebug <- asks isDebug
    if isDebug
      then return $ AST.idCons "fnAddr"
      else throwErrSt "cannot build expression for function address value without original expression"

buildStaticConstraintsExpr :: Seq.Seq Constraint -> EM AST.Expression
buildStaticConstraintsExpr cs = do
  cs' <- mapM buildConstraintExpr (toList cs)
  return $ foldr1 (AST.Binary (mkTypeToken Token.Unify)) cs'

buildConstraintExpr :: Constraint -> EM AST.Expression
buildConstraintExpr c = case c of
  ValCnstr vn -> buildExprExt (mkValVN vn)
  StructEmbedCnstr xs -> buildStaticConstraintsExpr xs
  OpCnstr op -> buildOpASTExpr op (mkValVN VUnknown)

buildBottom :: EM AST.Expression
buildBottom = return $ AST.litCons (AST.LitBasic $ AST.BottomLit $ mkTypeToken Token.Bottom)

throwExprNotFound :: VNode -> EM a
throwExprNotFound t = do
  rep <- vnToStringTermsRep t
  throwError $ printf "expression not found for %s, tree rep: %s" (showValType $ value t) rep

buildOpASTExpr :: Op -> VNode -> EM AST.Expression
buildOpASTExpr mut t = do
  -- If in debug mode, we build the expression because arguments might have updated values even though the mutval is
  -- not ready.
  isDebug <- asks isDebug
  if isDebug
    then buildOpASTExprForce mut t
    -- TODO: handle parenthese in origExpr. Currently origExpr does not have parenthese.
    else maybe (buildOpASTExprForce mut t) return (origExpr t)

buildOpASTExprForce :: Op -> VNode -> EM AST.Expression
buildOpASTExprForce op t = case op of
  RegOp r -> buildRegOpASTExpr r
  Ref ref -> buildRefASTExpr ref
  VSelect idx -> buildIndexASTExpr idx
  Compreh cph -> do
    ce <- buildComprehASTExpr cph
    return $
      AST.litCons $
        AST.LitStruct (AST.StructLit emptyLoc [AST.Embedding (AST.EmbedComprehension ce)] emptyLoc)
  DisjOp dop -> buildDisjoinOpASTExpr dop t
  Itp _ -> throwExprNotFound t
  FCall _ -> throwExprNotFound t

buildStaticFieldExpr :: (TextIndex, Field) -> EM AST.Declaration
buildStaticFieldExpr (sIdx, sf) = do
  sel <- textIndexToBS sIdx
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
  ve <- buildStaticConstraintsExpr (dsfValue sf)
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
  ve <- buildStaticConstraintsExpr (scsValue pat)
  return $ AST.FieldDecl (AST.Field [labelPatternCons pte] (AST.AliasExpr Nothing ve))

buildLetExpr :: (TextIndex, VNode) -> EM AST.Declaration
buildLetExpr (ident, v) = do
  s <- textIndexToBS ident
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

buildStructASTExpr :: Struct -> VNode -> EM AST.Expression
buildStructASTExpr struct t = do
  isDebug <- asks isDebug
  if isDebug
    then buildStructASTExprDebug struct t
    else buildStructASTExprNormal struct t

buildStructASTExprDebug :: Struct -> VNode -> EM AST.Expression
buildStructASTExprDebug (stcEmbedVal -> Just ev) _ = do
  evE <- buildExprExt (mkValVN ev)
  return $
    AST.litCons $
      AST.LitStruct (AST.StructLit emptyLoc [AST.Embedding (AST.EmbeddingAlias (AST.AliasExpr Nothing evE))] emptyLoc)
buildStructASTExprDebug s _ = do
  statics <- mapM buildStaticFieldExpr (Map.toList $ stcFields s)
  dynamics <- mapM buildDynFieldExpr (IntMap.elems $ stcDynFields s)
  patterns <- mapM buildPatternExpr (IntMap.elems $ stcCnstrs s)
  lets <- mapM buildLetExpr (Map.toList $ stcBindings s)
  let
    decls = statics ++ dynamics ++ patterns ++ lets
    e = AST.litCons $ AST.LitStruct (AST.StructLit emptyLoc decls emptyLoc)
  return e

buildStructASTExprNormal :: Struct -> VNode -> EM AST.Expression
buildStructASTExprNormal _ (VNVal (IsEmbedVal v)) = buildExprExt (mkValVN v)
buildStructASTExprNormal s t = do
  r <- buildStructOrdLabels (rtrString . value) s
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
      varName <- textIndexToBS varNameIdx
      secVarM <- case secVarIdxM of
        Just sIdx -> Just <$> textIndexToBS sIdx
        Nothing -> return Nothing
      ve <- buildExprExt val
      return (AST.ForClause emptyLoc (textIdentToken varName) (textIdentToken <$> secVarM) ve)
    _ -> throwErrSt "start clause should not be let clause"

  buildIterClause clause = case clause of
    ComprehArgLet varNameIdx val -> do
      varName <- textIndexToBS varNameIdx
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
  xs <- mapM buildValExprExt ds
  isDebug <- asks isDebug
  -- We might print unresolved disjunctions in debug mode with only one disjunct.
  if isDebug && length xs < 2
    then case xs of
      [] -> buildBottom
      [x] -> return x
      _ -> throwErrSt "unreachable"
    else
      return $ foldr1 (AST.Binary (mkTypeToken Disjoin)) xs

-- buildUnifyOpASTExpr :: UnifyOp -> EM AST.Expression
-- buildUnifyOpASTExpr op
--   | fstConj Seq.:<| rest <- op.conjs
--   , -- The rest should be a non-empty sequence.
--     _ Seq.:|> _ <- rest = do
--       leftMost <- buildExprExt fstConj
--       foldM
--         ( \acc x -> do
--             right <- buildExprExt x
--             return $ AST.Binary (mkTypeToken Unify) acc right
--         )
--         leftMost
--         rest
--   | otherwise = throwErrSt "UnifyOp should have at least two conjuncts"

buildDisjoinOpASTExpr :: DisjoinOp -> VNode -> EM AST.Expression
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
  varS <- textIndexToBS ref.ident
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

buildIndexASTExpr :: ValueSelect -> EM AST.Expression
buildIndexASTExpr (ValueSelect _ b xs) = do
  be <- buildExprExt b
  v <- case be of
    AST.Unary (AST.Primary v) -> return v
    _ -> throwErrSt "the index value of ValueSelect should be a primary expression"
  r <-
    foldM
      ( \acc y -> do
          ye <- buildExprExt y
          return $ AST.PrimExprIndex acc emptyLoc ye emptyLoc
      )
      v
      xs
  return $ AST.Unary (AST.Primary r)

buildRegOpASTExpr :: RegularOp -> EM AST.Expression
buildRegOpASTExpr op = case ropOpType op of
  UnaryOpType uop
    | x Seq.:<| _ <- ropArgs op -> buildUnaryExpr uop x
  BinOpType bop
    | x Seq.:<| y Seq.:<| _ <- ropArgs op -> buildBinaryExpr bop x y
  -- CloseFunc -> return $ AST.litCons (AST.textToSimpleStrLiteral (BC.pack "close func"))
  _ -> throwErrSt $ "Unsupported operation type: " ++ show (ropOpType op)

buildUnaryExpr :: TokenType -> VNode -> EM AST.Expression
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

buildBinaryExpr :: TokenType -> VNode -> VNode -> EM AST.Expression
buildBinaryExpr op l r = do
  xe <- buildExprExt l
  ye <- buildExprExt r
  return $ AST.Binary (mkTypeToken op) xe ye

buildArgsExpr :: String -> [VNode] -> EM AST.Expression
buildArgsExpr func ts = do
  ets <- mapM buildExprExt ts
  return $
    AST.Unary $
      AST.Primary
        (AST.PrimExprArguments (AST.idToPrimExpr (T.pack func)) emptyLoc ets emptyLoc)