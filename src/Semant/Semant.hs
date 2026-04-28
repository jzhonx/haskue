{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Semant.Semant where

import Control.Monad (foldM, when)
import Control.Monad.Except (ExceptT (..), throwError)
import Control.Monad.RWS.Strict (RWST)
import Control.Monad.State.Strict (gets, modify')
import qualified Data.ByteString.Char8 as BC
import qualified Data.DList as DList
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Vector as V
import Debug.Trace (trace)
import Feature
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import StringIndex (
  HasTextIndexer (..),
  ShowWTIndexer (..),
  TextIndex,
  TextIndexer,
  textToTextIndex,
 )
import Syntax.AST
import qualified Syntax.AST as AST
import Syntax.Token (
  Location,
  Token,
  TokenType (Disjoin, Exclamation, QuestionMark, Unify),
  emptyLoc,
  tkLiteral,
  tkType,
 )
import qualified Syntax.Token as Token
import Text.Printf (printf)
import Value

transSourceFile :: SourceFile -> ValAddr -> TM VNode
transSourceFile (SourceFile decls) addr = trDataEToVNode <$> transStructLit (StructLit emptyLoc decls emptyLoc) addr

transExprToVal :: Expression -> ValAddr -> TM VNode
transExprToVal e addr = trDataEToVNode <$> transExpr e addr

data TrDataE = TrDataE
  { trData :: TrData
  , trExpr :: Maybe Expression
  }
  deriving (Show)

data TrData
  = TrValue Val
  | TrOp Op
  | TrStructEmbed ConstraintSeq
  | TrCnstrs ConstraintSeq
  deriving (Show)

mkEmptyExprTrDataE :: TrData -> TrDataE
mkEmptyExprTrDataE d = TrDataE{trData = d, trExpr = Nothing}

trDataEToVNode :: TrDataE -> VNode
trDataEToVNode d =
  let v = case trData d of
        TrValue x -> mkValCnstrVN x
        TrOp op -> mkOpVN op
        TrCnstrs cs -> emptyVNode{constraints = emptyConstraintsSet{static = cs}}
        TrStructEmbed cs -> emptyVNode{constraints = emptyConstraintsSet{static = Seq.singleton (StructEmbedCnstr cs)}}
   in v{origExpr = trExpr d}

trDataEToCnstrsSeq :: TrDataE -> ConstraintSeq
trDataEToCnstrsSeq d = case trDataEToCnstr d of
  Just cnstr -> Seq.singleton cnstr
  Nothing -> case trData d of
    TrCnstrs cs -> cs
    _ -> error "trDataEToCnstrsSeq: expected constraint data"

trDataEToCnstr :: TrDataE -> Maybe Constraint
trDataEToCnstr d = case trData d of
  TrValue n -> Just $ ValCnstr n
  TrOp o -> Just $ OpCnstr o
  TrStructEmbed cs -> Just (StructEmbedCnstr cs)
  TrCnstrs _ -> Nothing

{- | transExpr and all trans* should return the same level tree cursor.

The label and the translated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every trans* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the addr of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
transExpr :: Expression -> ValAddr -> TM TrDataE
transExpr e addr = do
  r <- case e of
    (Unary ue) -> transUnaryExpr ue addr
    (Binary op e1 e2) -> transBinary op.tkType e1 e2 addr
  return r{trExpr = Just e}

transLiteral :: Literal -> ValAddr -> TM TrDataE
transLiteral (LitStruct s) addr = transStructLit s addr
transLiteral (LitList (ListLit _ l _)) addr = transListLit l addr
transLiteral (LitBasic a) addr
  | (StringLit (SimpleStringL (SimpleStringLit _ segs))) <- a = segsToStrAtom segs
  | (StringLit (MultiLineStringL (MultiLineStringLit _ segs))) <- a = segsToStrAtom segs
 where
  segsToStrAtom segs = do
    rE <- strLitSegsToStr segs addr
    return $ case rE of
      Left op -> mkEmptyExprTrDataE (TrOp op)
      Right str -> mkAtomTrDataE $ String str
transLiteral (LitBasic a) _ = case a of
  IntLit i -> do
    let v = read (BC.unpack (tkLiteral i)) :: Integer
    return $ mkAtomTrDataE $ Int v
  FloatLit f -> do
    let v = read (BC.unpack (tkLiteral f)) :: Double
    return $ mkAtomTrDataE $ Float v
  BoolLit b -> do
    v <- case BC.unpack (tkLiteral b) of
      "true" -> return True
      "false" -> return False
      _ -> throwFatal $ printf "invalid boolean literal: %s" (show b)
    return $ mkAtomTrDataE $ Bool v
  NullLit _ -> return $ mkAtomTrDataE Null
  BottomLit _ -> return $ mkEmptyExprTrDataE (TrValue $ VBottom $ Bottom "")

mkAtomTrDataE :: Atom -> TrDataE
mkAtomTrDataE a = mkEmptyExprTrDataE (TrValue $ VAtom a)

data DeclWithEmbedIndex
  = RegDecl Declaration
  | -- | The index should start from 1 because the first is reserved for the struct literal itself.
    EmbedDecl Int Embedding

transStructLit :: StructLit -> ValAddr -> TM TrDataE
transStructLit (StructLit _ decls _) addr = inStructScope decls addr $ do
  sid <- getEnvID
  let (revRes, embedCnt) =
        foldl
          ( \(acc, accEmbedCnt) decl -> case decl of
              Embedding emb -> (EmbedDecl (accEmbedCnt + 1) emb : acc, accEmbedCnt + 1)
              _ -> (RegDecl decl : acc, accEmbedCnt)
          )
          ([], 0)
          decls

  -- If the struct literal has embedded fields, the constraints for the struct and the embedded fields will be stored in
  -- an additional constraint.
  let structCnstrsAddr = if embedCnt > 0 then addr `appendSeg` mkRegCnstrFeature 0 else addr
  elems <- mapM (\x -> transDecl x (embedCnt > 0) structCnstrsAddr) (reverse revRes)
  let struct = foldl (flip insertElemToStruct) (emptyStruct{stcID = sid}) elems
  -- If the result has embedded fields, then mark the embedded fields as embedded.
  let embeds = [tr | EmbedSAdder tr <- elems]
      embedCnstrs = foldl (\acc tr -> acc Seq.>< trDataEToCnstrsSeq tr) Seq.empty embeds
  if not (null embedCnstrs)
    then do
      -- trace (printf "struct with embeds, id: %d, embed constraints: %s" sid (show embedCnstrs)) (return ())
      return $ mkEmptyExprTrDataE (TrStructEmbed (ValCnstr (VStruct struct) Seq.<| embedCnstrs))
    else return $ mkEmptyExprTrDataE $ TrValue (VStruct struct)

strLitSegsToStr :: [StringLitSeg] -> ValAddr -> TM (Either Op BC.ByteString)
strLitSegsToStr segs addr = do
  -- TODO: efficiency
  (asM, aSegs, aExprs) <-
    foldM
      ( \(accCurStrM, accItpSegs, accItpExprs) seg -> case seg of
          UnicodeChars x ->
            return (Just x, accItpSegs, accItpExprs)
          AST.Interpolation _ e -> do
            t <- transExpr e (addr `appendSeg` mkOpArgFeature (length accItpExprs))
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
    | null rSegs -> return $ Right BC.empty
    | not (null aExprs) ->
        return $ Left $ mkItpSOp rSegs (map trDataEToVNode aExprs)
    | length rSegs == 1, IplSegStr s <- head rSegs -> return $ Right s
    | otherwise -> throwFatal $ printf "invalid simple string literal: %s" (show segs)

-- | Evaluates a declaration.
transDecl :: DeclWithEmbedIndex -> Bool -> ValAddr -> TM StructElemAdder
transDecl decli hasEmbeds structAddr = case decli of
  EmbedDecl idx ed -> do
    v <- transEmbedding False ed (structAddr `appendSeg` mkRegCnstrFeature idx)
    return $ EmbedSAdder v
  RegDecl decl -> case decl of
    EllipsisExpr (Ellipsis _ cM) ->
      maybe
        (return EmptyAdder) -- TODO: implement real ellipsis handling
        (\_ -> throwFatal "default constraints are not implemented yet")
        cM
    FieldDecl (AST.Field ls e) ->
      let declAddr = if hasEmbeds then structAddr `appendSeg` mkRegCnstrFeature 0 else structAddr
       in transFDeclLabels ls e declAddr
    DeclLet (LetClause _ ident binde) -> do
      idIdx <- identTokenToTextIndex ident
      res <- fromJust <$> lookupIdentCurEnv idIdx
      val <- transExpr binde res.identAddr
      let featIdx = getTextIndexFromFeature res.identFeat
      return $ LetSAdder featIdx (trDataEToVNode val)
    _ -> throwFatal $ printf "impossible declaration: %s" (show decl)

identTokenToTextIndex :: Token -> TM TextIndex
identTokenToTextIndex tk = case tk.tkType of
  Token.Identifier -> textToTextIndex tk.tkLiteral
  _ -> throwFatal $ printf "expected identifier token, got %s" (show tk)

transEmbedding :: Bool -> Embedding -> ValAddr -> TM TrDataE
transEmbedding _ (EmbeddingAlias (AliasExpr _ e)) addr = transExpr e addr
transEmbedding
  isListCompreh
  (EmbedComprehension (AST.Comprehension (Clauses (GuardClause _ ge) cls) lit))
  addr = do
    cid <- allocObjID
    let comprehAddr = addr `appendSeg` mkObjectFeature cid
    args <-
      mapM (\(j, c) -> transClause c (comprehAddr `appendSeg` mkComprehClausesFeature j)) (zip [1 ..] cls)
    gev <- transExpr ge (comprehAddr `appendSeg` mkComprehClausesFeature 0)
    let vs = ComprehArgIf (trDataEToVNode gev) : args
    sv <- transStructLit lit (comprehAddr `appendSeg` mkComprehClausesFeature (length vs))
    return $
      mkEmptyExprTrDataE $
        TrOp $
          Compreh $
            mkComprehension cid isListCompreh vs (trDataEToVNode sv)
transEmbedding
  isListCompreh
  (EmbedComprehension (AST.Comprehension (Clauses (ForClause _ i jM fe) cls) lit))
  addr = do
    iIdx <- identTokenToTextIndex i
    jIdxM <- case jM of
      Just j -> Just <$> identTokenToTextIndex j
      Nothing -> return Nothing
    cid <- allocObjID
    let comprehAddr = addr `appendSeg` mkObjectFeature cid
    let forClsAddr = comprehAddr `appendSeg` mkComprehClausesFeature 0
    inClauseScope iIdx jIdxM forClsAddr $ do
      args <-
        mapM
          (\(j, c) -> transClause c (comprehAddr `appendSeg` mkComprehClausesFeature j))
          (zip [1 ..] cls)
      fev <- transExpr fe forClsAddr
      let vs = ComprehArgFor iIdx jIdxM (trDataEToVNode fev) : args
      sv <- transStructLit lit (comprehAddr `appendSeg` mkComprehClausesFeature (length vs))
      return $ mkEmptyExprTrDataE $ TrOp $ Compreh $ mkComprehension cid isListCompreh vs (trDataEToVNode sv)

transClause :: Clause -> ValAddr -> TM ComprehArg
transClause c clAddr = case c of
  ClauseStart (GuardClause _ e) -> do
    t <- trDataEToVNode <$> transExpr e clAddr
    return $ ComprehArgIf t
  ClauseStart (ForClause _ i jM e) -> do
    iIdx <- identTokenToTextIndex i
    jIdxM <- case jM of
      Just j -> Just <$> identTokenToTextIndex j
      Nothing -> return Nothing
    inSubClauseScope iIdx jIdxM clAddr $ do
      t <- trDataEToVNode <$> transExpr e clAddr
      return $ ComprehArgFor iIdx jIdxM t
  ClauseLet (LetClause _ ident le) -> do
    idIdx <- identTokenToTextIndex ident
    inSubClauseScope idIdx Nothing clAddr $ do
      lt <- trDataEToVNode <$> transExpr le clAddr
      return $ ComprehArgLet idIdx lt

-- TODO: statically make sure l2's address is correct. l2 could be unified with not-yet-discovered labels.
transFDeclLabels :: [Label] -> AliasExpr -> ValAddr -> TM StructElemAdder
transFDeclLabels lbls ae@(AST.AliasExpr _ e) structAddr =
  case lbls of
    [] -> throwFatal "empty labels"
    -- The adder is created before translating the expression because the label might have alias that can be
    -- referred to in the expression, and the alias needs to be in scope when translating the expression.
    [l1] -> mkAdderWithValGen l1 $ transExpr e
    l1 : l2 : rs -> mkAdderWithValGen l1 $ \fAddr -> do
      sf2 <- transFDeclLabels (l2 : rs) ae fAddr
      sid <- allocObjID
      let struct = insertElemToStruct sf2 (emptyStruct{stcID = sid})
      return $ mkEmptyExprTrDataE $ TrValue (VStruct struct)
 where
  mkAdderWithValGen :: Label -> (ValAddr -> TM TrDataE) -> TM StructElemAdder
  mkAdderWithValGen (Label le) vgen = case le of
    LabelName ln c -> do
      let attr = LabelAttr{lbAttrCnstr = cnstrFrom c, lbAttrIsIdent = isVar ln}
      case ln of
        (toIDentLabel -> Just key) -> do
          keyIdx <- identTokenToTextIndex key
          tr <- vgen (structAddr `appendSeg` mkStringFeature keyIdx)
          return $ StaticSAdder keyIdx attr tr
        (toDynLabel -> Just se) -> do
          oid <- allocObjID
          selTree <- trDataEToVNode <$> transExpr se (structAddr `appendSeg` mkDynFieldFeature oid 0)
          val <- trDataEToCnstrsSeq <$> vgen (structAddr `appendSeg` mkDynFieldFeature oid 1)
          return $
            DynamicSAdder
              oid
              (DynamicField{dsfID = oid, dsfAttr = attr, dsfLabel = selTree, dsfLabelIsInterp = False, dsfValue = val})
        (toSStrLabel -> Just (SimpleStringLit _ segs)) -> do
          oid <- allocObjID
          rE <- strLitSegsToStr segs (structAddr `appendSeg` mkDynFieldFeature oid 0)
          case rE of
            Right str -> do
              strIdx <- textToTextIndex str
              tr <- vgen (structAddr `appendSeg` mkStringFeature strIdx)
              return $ StaticSAdder strIdx attr tr
            Left t -> do
              val <- trDataEToCnstrsSeq <$> vgen (structAddr `appendSeg` mkDynFieldFeature oid 1)
              return $
                DynamicSAdder
                  oid
                  ( DynamicField
                      { dsfID = oid
                      , dsfAttr = attr
                      , dsfLabel = mkOpVN t
                      , dsfLabelIsInterp = True
                      , dsfValue = val
                      }
                  )
        _ -> throwFatal "invalid label"
    LabelExpr _ (AliasExpr aliasM pe) _ -> do
      aliasIdxM <- case aliasM of
        Just tk -> Just <$> identTokenToTextIndex tk
        Nothing -> return Nothing
      cnstrid <- getEnvID
      let cnstrValAddr = structAddr `appendSeg` mkPatternFeature cnstrid 1
      -- We use the original alias identifier without the suffix here so that the alias can be looked up in the scope.
      -- However, for the adder we need to use the suffixed alias identifier.
      -- {
      -- [string]: cnstrval
      -- \^---------------^ -- the whole pattern value is a constraint scope
      --           ^-----^ -- This is the cnstrval scope. The alias is defined for this scope.
      ---}
      inCnstrValScope aliasIdxM cnstrValAddr $ do
        pat <- trDataEToVNode <$> transExpr pe (structAddr `appendSeg` mkPatternFeature cnstrid 0)
        cs <- trDataEToCnstrsSeq <$> vgen cnstrValAddr
        cnstrvid <- getEnvID
        updatedAliasIdxM <- case aliasIdxM of
          Just origIdx -> Just <$> modifyTISuffix cnstrvid origIdx
          Nothing -> return Nothing
        return $ CnstrSAdder cnstrid pat updatedAliasIdxM cs

  -- Returns the label identifier and the whether the label is static.

  toDynLabel :: LabelName -> Maybe Expression
  toDynLabel (LabelNameExpr _ (AliasExpr _ lne) _) = Just lne
  toDynLabel _ = Nothing

  toSStrLabel :: LabelName -> Maybe SimpleStringLit
  toSStrLabel (LabelString ls) = Just ls
  toSStrLabel _ = Nothing

  cnstrFrom :: Maybe TokenType -> StructFieldCnstr
  cnstrFrom (Just QuestionMark) = SFCOptional
  cnstrFrom (Just Exclamation) = SFCRequired
  cnstrFrom _ = SFCRegular

  isVar :: LabelName -> Bool
  isVar (LabelID _) = True
  -- Labels which are quoted or expressions are not variables.
  isVar _ = False

toIDentLabel :: LabelName -> Maybe Token
toIDentLabel (LabelID ident) = Just ident
toIDentLabel _ = Nothing

data StructElemAdder
  = StaticSAdder TextIndex LabelAttr TrDataE
  | DynamicSAdder !Int DynamicField
  | CnstrSAdder !Int VNode (Maybe TextIndex) ConstraintSeq
  | LetSAdder TextIndex VNode
  | EmbedSAdder TrDataE
  | EmptyAdder
  deriving (Show)

{- | Insert a new element into the struct.

If the field is already in the struct, then unify the field with the new field.
-}
insertElemToStruct :: StructElemAdder -> Struct -> Struct
insertElemToStruct adder struct = case adder of
  (StaticSAdder name attr tr) -> do
    case lookupStructField name struct of
      -- The label is already in the struct, so we need to unify the field.
      Just extSF ->
        -- FIXME: addresses for constraints
        let
          unifySFOp =
            Value.Field
              { ssfValue = appendStaticCnstrs (trDataEToCnstrsSeq tr) (ssfValue extSF)
              , ssfAttr = mergeAttrs (ssfAttr extSF) attr
              }
          newStruct = updateStubAndField name unifySFOp struct
         in
          newStruct
      -- The label is not seen before in the struct.
      _ -> insertNewStubAndField name (staticFieldMker (trDataEToVNode tr) attr) struct
  (DynamicSAdder i dsf) -> insertStructNewDynField i dsf struct
  (CnstrSAdder i pattern alias val) -> insertStructNewCnstr i pattern alias val struct
  (LetSAdder name val) -> insertStructLet name val struct
  _ -> struct

transListLit :: ElementList -> ValAddr -> TM TrDataE
transListLit (EllipsisList _) _ = return $ mkEmptyExprTrDataE $ TrValue $ VList $ mkList [] []
transListLit (EmbeddingList es _) addr = do
  xs <-
    mapM
      ( \(i, e) ->
          trDataEToVNode
            <$> transEmbedding
              True
              e
              (addr `appendValAddr` addrFromList [mkListStoreIdxFeature i, mkRegCnstrFeature 0])
      )
      (zip [0 ..] es)
  return $ mkEmptyExprTrDataE $ TrValue $ VList $ mkList xs []

transUnaryExpr :: UnaryExpr -> ValAddr -> TM TrDataE
transUnaryExpr ue addr = case ue of
  Primary primExpr -> transPrimExpr primExpr addr
  UnaryOp op e -> transUnaryOp op.tkType e addr

builtinOpNameTable :: [(String, TrData)]
builtinOpNameTable =
  -- built-in identifier names
  [("_", TrValue VTop)]
    ++ map (\b -> (show b, TrValue $ VBounds $ Bounds{bdsList = [BdType b]})) [minBound :: BdType .. maxBound :: BdType]
    -- built-in function names
    -- We use the function to distinguish the identifier from the string literal.
    ++ map (\(s, op) -> (s, TrOp op)) builtinFuncTable

transPrimExpr :: PrimaryExpr -> ValAddr -> TM TrDataE
transPrimExpr e addr = case e of
  (PrimExprOperand op) -> case op of
    OpLiteral lit -> transLiteral lit addr
    OpName (OperandName ident) -> case lookup (BC.unpack (tkLiteral ident)) builtinOpNameTable of
      Just v -> return $ mkEmptyExprTrDataE v
      Nothing -> do
        idIdx <- identTokenToTextIndex ident
        IdentLookupResult{identType, identFeat, identAddr} <- lookupIdentInScopes idIdx ident.tkLoc
        return $
          mkEmptyExprTrDataE $
            TrOp $
              Ref $
                singletonIdentRef
                  (getTextIndexFromFeature identFeat)
                  identType
                  (getResolvedIdentAddr identAddr identType)
    OpExpression _ expr _ -> transExpr expr addr
  (PrimExprSelector primExpr _ sel) -> transSelector primExpr sel addr
  (PrimExprIndex primExpr _ idx _) -> transIndex primExpr idx addr
  (PrimExprArguments primExpr _ aes _) -> do
    p <- transPrimExpr primExpr addr
    args <- mapM (\(i, ae) -> transExpr ae (addr `appendSeg` mkOpArgFeature i)) (zip [0 ..] aes)
    replaceFuncArgs p args

getResolvedIdentAddr :: ValAddr -> RefIdentType -> ValAddr
getResolvedIdentAddr addr _ =
  let xs = vFeatures addr
   in ValAddr $ V.filter (not . isFeatureNonCanonical) xs

-- | Creates a new function tree for the original function with the arguments applied.
replaceFuncArgs :: TrDataE -> [TrDataE] -> TM TrDataE
replaceFuncArgs TrDataE{trData = TrOp (RegOp fn)} args =
  return $
    mkEmptyExprTrDataE $
      TrOp $
        RegOp $
          fn{ropArgs = Seq.fromList (map trDataEToVNode args)}
replaceFuncArgs _ _ = throwFatal "expected a function value"

{- | Evaluates the selector.

Parameters:
- pe is the primary expression.
- sel is the segment.
- addr is the addr to the current expression that contains the segment.
For example, { a: b: x.y }
If the field is "y", and the addr is "a.b", expr is "x.y", the structValAddr is "x".
-}
transSelector :: PrimaryExpr -> Syntax.AST.Selector -> ValAddr -> TM TrDataE
transSelector pe astSel addr = do
  (oprdAddr, oid) <- getPrimaryExprValAddr pe addr
  oprnd <- transPrimExpr pe oprdAddr
  (selAddr, selVGen) <- getSelCons addr oprnd
  let f sel = selVGen oid (mkAtomTrDataE (String sel))
  case astSel of
    IDSelector ident -> return $ f (tkLiteral ident)
    StringSelector (SimpleStringLit _ segs) -> do
      rE <- strLitSegsToStr segs selAddr
      case rE of
        Left _ -> throwFatal "selector should not have interpolation"
        Right str -> return $ f str

getPrimaryExprValAddr :: PrimaryExpr -> ValAddr -> TM (ValAddr, Int)
getPrimaryExprValAddr pe addr = case pe of
  PrimExprIndex{} -> return (addr, 0)
  PrimExprSelector{} -> return (addr, 0)
  _ -> do
    oid <- allocObjID
    return (addr `appendSeg` mkObjectFeature oid, oid)

transIndex :: PrimaryExpr -> Expression -> ValAddr -> TM TrDataE
transIndex pe e addr = do
  (oprdAddr, oid) <- getPrimaryExprValAddr pe addr
  oprnd <- transPrimExpr pe oprdAddr
  (selAddr, selVGen) <- getSelCons addr oprnd
  sel <- transExpr e selAddr
  return $ selVGen oid sel

getSelCons :: ValAddr -> TrDataE -> TM (ValAddr, Int -> TrDataE -> TrDataE)
getSelCons addr oprnd = case trData oprnd of
  TrOp (Ref ref) -> do
    let n = length ref.selectors
    return
      ( appendSeg addr (mkOpArgFeature n)
      , \_ sel -> oprnd{trData = TrOp (Ref $ appendRefArg (trDataEToVNode sel) ref)}
      )
  TrOp (VSelect index@(ValueSelect _ _ indexes)) -> do
    let n = length indexes
    return
      ( appendSeg addr (mkOpArgFeature n)
      , \_ sel -> oprnd{trData = TrOp (VSelect $ appendValueSelectArg (trDataEToVNode sel) index)}
      )
  _ -> do
    let selAddr = appendSeg addr (mkOpArgFeature 0)
    return
      ( selAddr
      , \i sel ->
          oprnd
            { trData =
                TrOp $
                  VSelect $
                    ValueSelect
                      { bvID = i
                      , base = trDataEToVNode oprnd
                      , iSelectors = Seq.fromList [trDataEToVNode sel]
                      }
            }
      )

-- | Evaluates the unary operator.
transUnaryOp :: TokenType -> UnaryExpr -> ValAddr -> TM TrDataE
transUnaryOp op e addr = do
  r <- transUnaryExpr e (addr `appendSeg` mkOpArgFeature 0)
  return $ mkEmptyExprTrDataE $ TrOp $ mkUnaryOp op (trDataEToVNode r)

{- | order of arguments is important for disjunctions.

left is always before right.
-}
transBinary :: TokenType -> Expression -> Expression -> ValAddr -> TM TrDataE
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
transBinary Disjoin e1 e2 addr = transDisj e1 e2 addr
transBinary Unify e1 e2 addr = do
  let acc1 = flattenUnify e1 DList.empty
      exprs = DList.toList $ flattenUnify e2 acc1

  res <-
    mapM
      ( \(i, e) -> do
          r <- transExpr e (addr `appendSeg` mkRegCnstrFeature i)
          case trDataEToCnstr r of
            Just cnstr -> return cnstr
            Nothing -> throwFatal "unexpected constraints"
      )
      (zip [0 ..] exprs)
  return $ mkEmptyExprTrDataE $ TrCnstrs $ Seq.fromList res
transBinary op e1 e2 addr = do
  lv <- trDataEToVNode <$> transExpr e1 (appendSeg addr (mkOpArgFeature 0))
  rv <- trDataEToVNode <$> transExpr e2 (appendSeg addr (mkOpArgFeature 1))
  return $ mkEmptyExprTrDataE $ TrOp (mkBinaryOp op lv rv)

flattenUnify :: Expression -> DList.DList Expression -> DList.DList Expression
flattenUnify e acc = case e of
  Binary (tkType -> Unify) e1 e2 -> let acc1 = flattenUnify e1 acc in flattenUnify e2 acc1
  Unary (Primary (PrimExprOperand (OpExpression _ pe _))) -> flattenUnify pe acc
  _ -> DList.snoc acc e

{- | Translates a disjunction expression.

Since the leftmost node is the first term and the next term is always on the right, either at this
level or the next level, we can peek the left operand to determine the address for both operands and whether we treat
the current disjOp as an accumulator, which means we apply the right operand to the accumulating disjunction operator
that is on the left side.
-}
transDisj :: Expression -> Expression -> ValAddr -> TM TrDataE
transDisj e1 e2 addr = do
  let parseTerm e eAddr = case e of
        Unary (UnaryOp (tkType -> Token.Multiply) se) -> do
          v <- transUnaryExpr se eAddr
          return $ DisjTerm True (trDataEToVNode v)
        _ -> do
          v <- transExpr e eAddr
          return $ DisjTerm False (trDataEToVNode v)

      acc1 = flattenDisj e1 DList.empty
      terms = DList.toList $ flattenDisj e2 acc1

  res <- mapM (\(i, e) -> parseTerm e (addr `appendSeg` mkOpArgFeature i)) (zip [0 ..] terms)
  return $ mkEmptyExprTrDataE $ TrOp $ mkDisjoinOpFromList res

{- | Flattens the disjunction expression into a list of terms.

Notice that we do not descend into parenthesized expressions.
For example,
x: (*1 | 2) | *3
y: *1 | 2 | *3
gets
x: 3
y: 1 | 3
-}
flattenDisj :: Expression -> DList.DList Expression -> DList.DList Expression
flattenDisj e acc = case e of
  Binary (tkType -> Disjoin) e1 e2 -> let acc1 = flattenDisj e1 acc in flattenDisj e2 acc1
  _ -> DList.snoc acc e

data TransState = TransState
  { objID :: !Int
  , envs :: Environments
  , tIndexer :: TextIndexer
  }

instance HasTextIndexer TransState where
  getTextIndexer = tIndexer
  setTextIndexer ti ts = ts{tIndexer = ti}

emptyTransState :: TextIndexer -> TransState
emptyTransState ti = TransState{objID = 0, tIndexer = ti, envs = emptyEnvironments}

mapEnvs :: (Environments -> Environments) -> TransState -> TransState
mapEnvs f s = s{envs = f s.envs}

type TM = RWST () () TransState (ExceptT TransErr IO)

data TransErr
  = SemantErr String
  | FatalErr String
  deriving (Show)

allocObjID :: TM Int
allocObjID = do
  modify' $ \s -> let oid = objID s in s{objID = oid + 1}
  gets objID

throwFatal :: (HasCallStack) => String -> TM a
throwFatal msg = throwError $ FatalErr $ msg ++ "\n" ++ prettyCallStack callStack

getEnvID :: TM Int
getEnvID = do
  (Environments envs) <- gets envs
  case envs of
    [] -> throwFatal "no environment"
    (env : _) -> return env.envid

-- | Lookup the identifier in the scopes. If not found, return an error value.
lookupIdentInScopes :: TextIndex -> Location -> TM IdentLookupResult
lookupIdentInScopes identTI loc = do
  res <- lookupIdentInEnvs identTI
  case res of
    Just r -> return r
    Nothing -> notFoundMsg identTI (Just loc) >>= semanticError

notFoundMsg :: TextIndex -> Maybe Location -> TM String
notFoundMsg ident locM = do
  idStr <- tshow ident
  case locM of
    Nothing -> semanticError $ printf "reference %s is not found" (show idStr)
    Just loc -> semanticError $ printf "reference %s is not found:\n\t%s" (show idStr) (show loc)

data IdentLookupResult = IdentLookupResult
  { isInTopEnv :: Bool
  , envid :: Int
  , identType :: RefIdentType
  , identFeat :: Feature
  , identAddr :: ValAddr
  }

lookupIdentCurEnv :: TextIndex -> TM (Maybe IdentLookupResult)
lookupIdentCurEnv name = do
  (Environments envs) <- gets envs
  case envs of
    [] -> throwFatal "no environment"
    (env : _) -> return $ lookupIdentInEnv name env.envid env

lookupIdentInEnv :: TextIndex -> Int -> Environment -> Maybe IdentLookupResult
lookupIdentInEnv name topEnvID env = do
  (t, _) <- Map.lookup name env.names
  let identFeat = fromJust $ Map.lookup name env.nameFeatMap
  return
    IdentLookupResult
      { isInTopEnv = topEnvID == env.envid
      , envid = env.envid
      , identType = t
      , identFeat = identFeat
      , identAddr = env.envAddr `appendSeg` identFeat
      }

-- | Lookup the identifier in the environments.
lookupIdentInEnvs :: TextIndex -> TM (Maybe IdentLookupResult)
lookupIdentInEnvs name = do
  (Environments envs) <- gets envs
  let (res, updatedEnvs) = lookupInStack (topEnvID envs) [] envs
  modify' $ mapEnvs (const $ Environments updatedEnvs)
  return res
 where
  topEnvID envs = case envs of
    [] -> -1
    (env : _) -> env.envid

  lookupInStack _ acc [] = (Nothing, reverse acc)
  lookupInStack tenvid acc (env : rest) =
    case lookupIdentInEnv name tenvid env of
      Just res ->
        ( Just res
        , reverse acc ++ markNameAsReferenced name env : rest
        )
      Nothing -> lookupInStack tenvid (env : acc) rest

addNameToCurrentEnv :: TextIndex -> RefIdentType -> TM ()
addNameToCurrentEnv name identType = do
  checkIdentInEnvs name identType
  envid <- getEnvID
  feat <- case identType of
    ITField -> return $ mkStringFeature name
    ITLetBinding -> do
      tiWSuf <- modifyTISuffix envid name
      return $ mkLetFeature tiWSuf
    -- For the temporary iteration variable, we do not need to modify the text index with the env id suffix because
    -- the iteration is transient and in the reference we will fetch the value and make the reference a concrete
    -- value.
    ITIterBinding -> return $ mkLetFeature name
  modify' $ mapEnvs $ addName feat
 where
  addName feat (Environments envs) = case envs of
    [] -> Environments []
    (env : rest) ->
      Environments $
        env
          { names = Map.insert name (identType, False) env.names
          , nameFeatMap = Map.insert name feat env.nameFeatMap
          }
          : rest

checkIdentInEnvs :: TextIndex -> RefIdentType -> TM ()
checkIdentInEnvs key identType = do
  res <- lookupIdentInEnvs key
  case res of
    Just (IdentLookupResult{isInTopEnv, identType = targetIdentType})
      -- If the identifier exists and the types conflict, return an error.
      | isInTopEnv
      , targetIdentType `elem` [ITLetBinding, ITIterBinding]
      , identType `elem` [ITLetBinding, ITIterBinding] ->
          lbRedeclErr key
      | targetIdentType == ITField && identType == ITLetBinding
          || targetIdentType == ITLetBinding && identType == ITField ->
          aliasErr key
    _ -> return ()

aliasErr :: TextIndex -> TM ()
aliasErr name = do
  nameStr <- tshow name
  semanticError $ printf "can not have both alias and field with name %s in the same scope" (show nameStr)

lbRedeclErr :: TextIndex -> TM ()
lbRedeclErr name = do
  nameStr <- tshow name
  semanticError $ printf "%s redeclared in same scope" (show nameStr)

inStructScope :: [Declaration] -> ValAddr -> TM a -> TM a
inStructScope decls addr action = do
  enterStructScope decls addr
  result <- action
  leaveStructScope
  return result

enterStructScope :: [Declaration] -> ValAddr -> TM ()
enterStructScope decls addr = do
  sid <- allocObjID
  modify' $ mapEnvs (pushBlock sid EnvTypeStruct addr)
  -- First add all the immediate field and let binding identifiers to the current scope.
  -- This is to allow the references in the sub tree to refer to the identifiers that have not been translated yet.
  -- Unlike other languages, the order of field declarations does not matter.
  mapM_ addIdentDeclToScope decls

-- | Add the immediate field or let binding identifiers to the current scope.
addIdentDeclToScope :: Declaration -> TM ()
addIdentDeclToScope dl = case dl of
  FieldDecl (AST.Field ls _) -> addFieldIdent ls
  DeclLet (LetClause _ ident _) -> do
    keyIdx <- identTokenToTextIndex ident
    addNameToCurrentEnv keyIdx ITLetBinding
  _ -> return ()
 where
  addFieldIdent ls = do
    res <- addLabelToScope ls
    case res of
      Just keyIdx -> addNameToCurrentEnv keyIdx ITField
      Nothing -> return ()

  addLabelToScope :: [Label] -> TM (Maybe TextIndex)
  addLabelToScope (Label (LabelName ln _) : _)
    | Just key <- toIDentLabel ln = Just <$> identTokenToTextIndex key
  addLabelToScope _ = return Nothing

leaveStructScope :: TM ()
leaveStructScope = do
  envs <- gets envs
  let (poppedEnv, restEnvs) = popBlock envs
  modify' $ mapEnvs (const restEnvs)
  let unreferencedNames =
        Map.keys $
          Map.filter
            ( \(identType, isReferenced) -> case identType of
                ITLetBinding -> not isReferenced
                _ -> False
            )
            poppedEnv.names
  if null unreferencedNames
    then return ()
    else do
      let firstName = head unreferencedNames
      firstNameT <- tshow firstName
      semanticError $ printf "unreferenced let clause let %s" (show firstNameT)

{- | Enter a constraint value scope for evaluating a constraint body.

The alias identifier of the constraint, if exists, is added to the scope.
For example, [X=constraint]: value, a new environment is created for evaluating "value" with just X in the scope.
            ^---------------------^
              scope for evaluating "value"
-}
inCnstrValScope :: Maybe TextIndex -> ValAddr -> TM StructElemAdder -> TM StructElemAdder
inCnstrValScope aliasIdxM addr action = do
  enterCnstrValScope aliasIdxM addr
  result <- action
  leaveCnstrValScope
  return result

enterCnstrValScope :: Maybe TextIndex -> ValAddr -> TM ()
enterCnstrValScope aliasIdxM addr = do
  fid <- allocObjID
  modify' $ mapEnvs (pushBlock fid EnvTypeCnstr addr)
  case aliasIdxM of
    Just aliasIdx -> addNameToCurrentEnv aliasIdx ITLetBinding
    Nothing -> return ()

leaveCnstrValScope :: TM ()
leaveCnstrValScope = do
  envs <- gets envs
  let (_, restEnvs) = popBlock envs
  modify' $ mapEnvs (const restEnvs)

enterClauseScope :: TextIndex -> Maybe TextIndex -> ValAddr -> TM ()
enterClauseScope iIdx jIdxM addr = do
  fid <- allocObjID
  modify' $ mapEnvs (pushBlock fid EnvTypeClause addr)
  addNameToCurrentEnv iIdx ITIterBinding
  case jIdxM of
    Just jIdx -> addNameToCurrentEnv jIdx ITIterBinding
    Nothing -> return ()

leaveClauseScope :: TM ()
leaveClauseScope = do
  envs <- gets envs
  let (_, restEnvs) = popBlock envs
  modify' $ mapEnvs (const restEnvs)

inClauseScope :: TextIndex -> Maybe TextIndex -> ValAddr -> TM a -> TM a
inClauseScope iIdx jIdxM addr action = do
  enterClauseScope iIdx jIdxM addr
  cid <- getEnvID
  res <- action
  leaveUntil cid
  return res
 where
  leaveUntil cid = do
    subID <- getEnvID
    when (subID /= cid) $
      leaveClauseScope >> leaveUntil cid

{- | Enters a sub-clause scope for evaluating a clause argument without leaving the scope after evaluation.

The reason is that clause arguments can be nested, and we want to keep the outer clause scope active.
-}
inSubClauseScope :: TextIndex -> Maybe TextIndex -> ValAddr -> TM a -> TM a
inSubClauseScope iIdx jIdxM addr action = do
  enterClauseScope iIdx jIdxM addr
  action

-- | Environments is a stack of environments that is used to resolve identifiers.
newtype Environments = Environments
  { getEnvs :: [Environment]
  -- ^ It is a stack of pairs of address of a scope and the set of identifiers defined in that scope.
  }
  deriving (Eq)

instance Show Environments where
  show (Environments envs) = "Envs[" ++ concatMap (\e -> show e ++ "; ") envs ++ "]"

instance ShowWTIndexer Environments where
  tshow (Environments envs) = do
    envStrs <- mapM tshow envs
    return $ T.pack $ "Envs[" ++ concatMap (\e -> T.unpack e ++ "; ") envStrs ++ "]"

debugShowEnvs :: String -> TM ()
debugShowEnvs msg = do
  envsT <- tshow =<< gets envs
  trace (printf "In struct scope: %s envs=%s" msg (T.unpack envsT)) (return ())

data EnvType = EnvTypeStruct | EnvTypeClause | EnvTypeCnstr
  deriving (Eq, Show)

data Environment = Environment
  { envid :: !Int
  , envType :: EnvType
  , envAddr :: ValAddr
  , names :: Map.Map TextIndex (RefIdentType, Bool)
  -- ^ names maps identifiers to
  --  (1) their addresses,
  --  (2) their types (field, let binding, or iter binding),
  --  (3) a boolean indicating whether it is referenced.
  -- Notice the identifiers should not have suffix for let bindings so that the references in the sub tree can refer to
  -- them. But the reference address should have suffix to make sure the let bindings are unique in the struct scope.
  , nameFeatMap :: Map.Map TextIndex Feature
  -- ^ nameFeatMap is used to store the mapping from identifier to its corresponding feature.
  }
  deriving (Eq)

instance Show Environment where
  show (Environment envid typ addr names _) = printf "Env(id=%d, type=%s addr=[%s] names=[%s])" envid (show typ) (show addr) nameStr
   where
    nameStr :: String
    nameStr =
      concatMap
        ( \(k, (t, r)) ->
            printf "%s->(%s,%s,%s); " (show k) (show t) (show r)
        )
        (Map.toList names)

instance ShowWTIndexer Environment where
  tshow (Environment envid typ addr names _) = do
    addrT <- tshow addr
    nameStrs <-
      mapM
        ( \(k, (t, r)) -> do
            kT <- tshow k
            return $ T.pack $ printf "%s->(%s,%s); " (T.unpack kT) (show t) (show r)
        )
        (Map.toList names)
    return $
      T.pack $
        printf "Env(id=%d, type=%s, addr=%s, names=[%s])" envid (show typ) addrT (T.unpack $ T.concat nameStrs)

emptyEnvironments :: Environments
emptyEnvironments = Environments []

markNameAsReferenced :: TextIndex -> Environment -> Environment
markNameAsReferenced key env = env{names = Map.adjust markRef key env.names}
 where
  markRef (identType, _) = (identType, True)

pushBlock :: Int -> EnvType -> ValAddr -> Environments -> Environments
pushBlock envid typ addr (Environments envs) =
  Environments $
    Environment
      { names = Map.empty
      , envType = typ
      , envid = envid
      , envAddr = addr
      , nameFeatMap = Map.empty
      }
      : envs

popBlock :: Environments -> (Environment, Environments)
popBlock (Environments envs) = case envs of
  [] -> error "popBlock: empty environment stack"
  (env : rest) -> (env, Environments rest)

semanticError :: (HasCallStack) => String -> TM a
semanticError msg = throwError $ SemantErr msg