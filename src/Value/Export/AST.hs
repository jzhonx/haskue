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
import Control.Monad.Except (Except)
import Control.Monad.RWS.Strict (RWST, local, runRWST)
import Control.Monad.Reader (asks)
import qualified Data.ByteString.Char8 as BC
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import Debug.Trace (trace)
import Exception (throwErrSt)
import Feature (removeTISuffix)
import StringIndex (TextIndex, TextIndexer, textIndexToBS, textToTextIndex)
import qualified Syntax.AST as AST
import Syntax.Scanner (isByteStringIdentifier)
import Syntax.Token as Token
import Text.Printf (printf)
import Value.Atom as Atom
import Value.Bounds
import Value.Comprehension
import Value.Disj
import Value.DisjoinOp
import Value.Func (FuncCall (..))
import Value.Interpolation (Interpolation, IplSeg (..), itpExprs, itpIsBytes, itpSegs)
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.Val

type EM = RWST BuildConfig () TextIndexer (Except String)

buildExpr :: VNode -> TextIndexer -> Except String (AST.Expression, TextIndexer)
buildExpr t tier = do
  (a, s, _) <- runRWST (buildExprExt t) (BuildConfig False False) tier
  return (a, s)

buildExprDebug :: VNode -> TextIndexer -> Except String (AST.Expression, TextIndexer)
buildExprDebug t tier = do
  (a, s, _) <- runRWST (buildExprExt t) (BuildConfig True False) tier
  return (a, s)

data BuildConfig = BuildConfig
  { isDebug :: Bool
  , forceBuildFromCnstrs :: Bool
  }

buildExprExt :: VNode -> EM AST.Expression
buildExprExt t = do
  forceBuild <- asks forceBuildFromCnstrs
  case t of
    IsUnknown -> do
      if not (null (static $ constraints t))
        then
          -- All the sub nodes of an Unknown value should be built from constraints.
          local (\cfg -> cfg{forceBuildFromCnstrs = True}) $ buildConstraintSeqExpr (static $ constraints t)
        else do
          isDebug <- asks isDebug
          if isDebug
            then return $ AST.idCons "Unknown"
            else throwErrSt "no constraints found for Unknown value, cannot build expression for it"
    IsStruct s
      | isStructAllLabelsConcrete s -> buildStructASTExpr s
      | otherwise ->
          local (\cfg -> cfg{forceBuildFromCnstrs = True}) $
            buildConstraintSeqExpr (static $ constraints t)
    _
      | forceBuild -> buildConstraintSeqExpr (static $ constraints t)
      | otherwise -> buildValExprExt (value t)

buildValExprExt :: Val -> EM AST.Expression
buildValExprExt t = case t of
  VTop -> return $ AST.idCons "_"
  VBottom _ -> buildBottom
  VAtom a -> return $ (AST.litCons . aToLiteral) a
  VBounds b -> return $ buildBoundsASTExpr b
  VStruct struct -> buildStructASTExpr struct
  VList l -> do
    ls <-
      if l.isFinalReady
        then
          mapM
            ( \x -> do
                e <- buildValExprExt x
                return $ AST.EmbeddingAlias $ AST.AliasExpr Nothing e
            )
            (toList l.final)
        else
          mapM
            ( \x -> do
                e <- buildExprExt x
                return $ AST.EmbeddingAlias $ AST.AliasExpr Nothing e
            )
            (toList l.store)
    return $ AST.litCons $ AST.LitList $ AST.ListLit emptyLoc (AST.EmbeddingList ls Nothing) emptyLoc
  VDisj dj
    | null (rtrDisjDefVal dj) -> disjunctsToAST (toList $ dsjDisjuncts dj)
    | otherwise -> disjunctsToAST (defDisjunctsFromDisj dj)
  VUnknown -> do
    isDebug <- asks isDebug
    if isDebug
      then return $ AST.idCons "Unknown"
      else throwErrSt "cannot build expression for Unknown value without original expression"
  VFuncAddr _ -> do
    isDebug <- asks isDebug
    if isDebug
      then return $ AST.idCons "fnAddr"
      else throwErrSt "cannot build expression for function address value without original expression"

buildConstraintSeqExpr :: Seq.Seq Constraint -> EM AST.Expression
buildConstraintSeqExpr cs = do
  es' <- mapM buildConstraintExpr (toList cs)
  case es' of
    [] -> throwErrSt "no constraints found, cannot build expression for it"
    [e] -> return e
    _ -> return $ foldl1 (AST.Binary (mkTypeToken Token.Unify)) es'

buildConstraintExpr :: Constraint -> EM AST.Expression
buildConstraintExpr c = case c of
  ValCnstr vc -> buildValExprExt (vcVal vc)
  OpCnstr oc -> buildOpASTExpr (ocOp oc)
  StructEmbedCnstr xs -> buildConstraintSeqExpr xs

buildBottom :: EM AST.Expression
buildBottom = return $ AST.litCons (AST.LitBasic $ AST.BottomLit $ mkTypeToken Token.Bottom)

buildOpASTExpr :: Op -> EM AST.Expression
buildOpASTExpr op = case op of
  RegOp r -> buildRegOpASTExpr r
  Ref ref -> buildRefASTExpr ref
  VSelect idx -> buildIndexASTExpr idx
  Compreh cph -> do
    ce <- buildComprehASTExpr cph
    return $
      AST.litCons $
        AST.LitStruct (AST.StructLit emptyLoc [AST.Embedding (AST.EmbedComprehension ce)] emptyLoc)
  DisjOp dop -> buildDisjoinOpASTExpr dop
  Itp itp -> buildInterpolationASTExpr itp
  FCall fc -> buildFCallASTExpr fc

buildInterpolationASTExpr :: Interpolation -> EM AST.Expression
buildInterpolationASTExpr itp = do
  exprs <- mapM buildExprExt (toList $ itpExprs itp)
  let xs =
        map
          ( \seg ->
              ( case seg of
                  IplSegStr s -> AST.UnicodeChars s
                  IplSegExpr i -> AST.InterpolationExpr emptyLoc (exprs !! i)
              )
          )
          (itpSegs itp)
      lit = if itpIsBytes itp
        then AST.StringLit $ AST.SimpleBytesL (AST.SimpleBytesLit emptyLoc xs)
        else AST.StringLit $ AST.SimpleStringL (AST.SimpleStringLit emptyLoc xs)
  return $ AST.litCons $ AST.LitBasic $ lit

buildFCallASTExpr :: FuncCall -> EM AST.Expression
buildFCallASTExpr FuncCall{fnFrame}
  | faddr Seq.:<| args <- fnFrame = do
      fe <- local (\cfg -> cfg{forceBuildFromCnstrs = True}) $ buildExprExt faddr
      argEs <- mapM (local (\cfg -> cfg{forceBuildFromCnstrs = True}) . buildExprExt) args
      case fe of
        AST.Unary (AST.Primary pe) ->
          return $
            AST.Unary $
              AST.Primary $
                AST.PrimExprArguments pe emptyLoc (toList argEs) emptyLoc
        _ -> throwErrSt "the function address of a function call should be a primary expression"
  | otherwise = throwErrSt "function call should have at least one element in the frame"

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
  ve <- buildConstraintSeqExpr (dsfValue sf)
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
  ve <- buildConstraintSeqExpr (scsValue pat)
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

buildStructASTExpr :: Struct -> EM AST.Expression
buildStructASTExpr struct = do
  isDebug <- asks isDebug
  if isDebug
    then buildStructASTExprDebug struct
    else buildStructASTExprNormal struct

buildStructASTExprDebug :: Struct -> EM AST.Expression
buildStructASTExprDebug (stcEmbedVal -> Just ev) = do
  evE <- buildValExprExt ev
  return $
    AST.litCons $
      AST.LitStruct (AST.StructLit emptyLoc [AST.Embedding (AST.EmbeddingAlias (AST.AliasExpr Nothing evE))] emptyLoc)
buildStructASTExprDebug s = buildNonConcreteStructASTExpr s

buildStructASTExprNormal :: Struct -> EM AST.Expression
buildStructASTExprNormal Struct{stcEmbedVal = Just v} = buildValExprExt v
buildStructASTExprNormal s = do
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
    Nothing -> buildNonConcreteStructASTExpr s

buildNonConcreteStructASTExpr :: Struct -> EM AST.Expression
buildNonConcreteStructASTExpr s = do
  statics <- mapM buildStaticFieldExpr (Map.toList $ stcFields s)
  dynamics <- mapM buildDynFieldExpr (IntMap.elems $ stcDynFields s)
  patterns <- mapM buildPatternExpr (IntMap.elems $ stcCnstrs s)
  lets <- mapM buildLetExpr (Map.toList $ stcBindings s)
  let
    decls = statics ++ dynamics ++ patterns ++ lets
    e = AST.litCons $ AST.LitStruct (AST.StructLit emptyLoc decls emptyLoc)
  return e

isStructAllLabelsConcrete :: Struct -> Bool
isStructAllLabelsConcrete s = all (isJust . rtrString . value . dsfLabel) (IntMap.elems $ stcDynFields s)

{- | Build the ordered list of labels in the struct.

If not all dynamic field labels can be resolved to strings, return Nothing.
-}
buildStructOrdLabels :: (VNode -> Maybe BC.ByteString) -> Struct -> EM (Maybe [BC.ByteString])
buildStructOrdLabels rtrBC struct = do
  r <-
    foldM
      ( \acc blkLabel -> case acc of
          Nothing -> return Nothing
          Just (revAcc, seen) -> do
            newLabelM <- case blkLabel of
              StructStaticFieldLabel n -> Just <$> textIndexToBS n
              StructDynFieldOID i -> return $ do
                dsf <- lookupStructDynField i struct
                rtrBC (dsfLabel dsf)
            case newLabelM of
              Nothing -> return Nothing
              Just newLabel ->
                return $
                  Just
                    if Set.member newLabel seen
                      then (revAcc, seen)
                      else (newLabel : revAcc, Set.insert newLabel seen)
      )
      (Just ([], Set.empty))
      (stcOrdLabels struct)
  return $ reverse . fst <$> r

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

buildDisjoinOpASTExpr :: DisjoinOp -> EM AST.Expression
buildDisjoinOpASTExpr op
  | length (djoTerms op) < 2 = throwErrSt "DisjoinOp should have at least two conjuncts"
  | fstDisj Seq.:<| rest <- djoTerms op = do
      leftMost <- build fstDisj
      foldM
        ( \acc x -> do
            right <- build x
            return $ AST.Binary (mkTypeToken Disjoin) acc right
        )
        leftMost
        rest
  | otherwise = throwErrSt "unreachable"
 where
  build term = do
    e <- buildExprExt (dstValue term)
    if dstMarked term
      then case e of
        AST.Unary ue -> return $ AST.Unary $ AST.UnaryOp (mkTypeToken Token.Multiply) ue
        _ ->
          return
            $ AST.Unary
            $ AST.UnaryOp
              (mkTypeToken Token.Multiply)
            $ AST.Primary
            $ AST.PrimExprOperand
            $ AST.OpExpression emptyLoc e emptyLoc
      else return e

buildRefASTExpr :: Reference -> EM AST.Expression
buildRefASTExpr ref = do
  varS <-
    if ref.resolvedIdentType == ITLetBinding
      then removeTISuffix ref.ident >>= textIndexToBS
      else textIndexToBS ref.ident
  let varE = AST.PrimExprOperand $ AST.OpName $ AST.OperandName (textIdentToken varS)
  r <-
    foldM
      ( \acc (x, isIndex) -> do
          xe <- buildExprExt x
          if isIndex
            then return $ AST.PrimExprIndex acc emptyLoc xe emptyLoc
            else do
              sel <- exprToSelector xe
              return $ AST.PrimExprSelector acc emptyLoc sel
      )
      varE
      (Seq.zip ref.selectors ref.selectorTypes)
  return $ AST.Unary (AST.Primary r)

exprToSelector :: AST.Expression -> EM AST.Selector
exprToSelector e = case e of
  AST.Unary
    ( AST.Primary
        ( AST.PrimExprOperand
            ( AST.OpLiteral
                ( AST.LitBasic
                    (AST.StringLit (AST.SimpleStringL s@(AST.SimpleStringLit _ [AST.UnicodeChars t])))
                  )
              )
          )
      ) ->
      if isByteStringIdentifier t
        then return (AST.IDSelector (mkToken Identifier t))
        else return (AST.StringSelector s)
  _ -> throwErrSt "selector should be a string literal"

buildIndexASTExpr :: ValueSelect -> EM AST.Expression
buildIndexASTExpr vs = do
  be <- buildExprExt vs.base
  v <- case be of
    AST.Unary (AST.Primary v) -> return v
    _ -> throwErrSt "the index value of ValueSelect should be a primary expression"
  r <-
    foldM
      ( \acc (y, isIndex) -> do
          ye <- buildExprExt y
          if isIndex
            then return $ AST.PrimExprIndex acc emptyLoc ye emptyLoc
            else do
              sel <- exprToSelector ye
              return $ AST.PrimExprSelector acc emptyLoc sel
      )
      v
      (Seq.zip vs.iSelectors vs.iSelectorTypes)
  return $ AST.Unary (AST.Primary r)

buildRegOpASTExpr :: RegularOp -> EM AST.Expression
buildRegOpASTExpr op = case ropOpType op of
  UnaryOpType uop
    | x Seq.:<| _ <- ropArgs op -> buildUnaryExpr uop x
  BinOpType bop
    | x Seq.:<| y Seq.:<| _ <- ropArgs op -> buildBinaryExpr bop x y
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
