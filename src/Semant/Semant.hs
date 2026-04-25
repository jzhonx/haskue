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
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
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

transSourceFile :: SourceFile -> ValAddr -> TM Val
transSourceFile (SourceFile decls) = transStructLit (StructLit emptyLoc decls emptyLoc)

{- | transExpr and all trans* should return the same level tree cursor.

The label and the translated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every trans* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the addr of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
transExpr :: Expression -> ValAddr -> TM Val
transExpr e addr = do
  v <- case e of
    (Unary ue) -> transUnaryExpr ue addr
    (Binary op e1 e2) -> transBinary op.tkType e1 e2 addr
  return $ setExpr (Just e) v

transLiteral :: Literal -> ValAddr -> TM Val
transLiteral (LitStruct s) addr = transStructLit s addr
transLiteral (LitList (ListLit _ l _)) addr = transListLit l addr
transLiteral (LitBasic a) addr
  | (StringLit (SimpleStringL (SimpleStringLit _ segs))) <- a = segsToStrAtom segs
  | (StringLit (MultiLineStringL (MultiLineStringLit _ segs))) <- a = segsToStrAtom segs
 where
  segsToStrAtom segs = do
    rE <- strLitSegsToStr segs addr
    return $ case rE of
      Left t -> t
      Right str -> mkAtomVal $ String str
transLiteral (LitBasic a) _ = case a of
  IntLit i -> do
    let v = read (BC.unpack (tkLiteral i)) :: Integer
    return $ mkAtomVal $ Int v
  FloatLit f -> do
    let v = read (BC.unpack (tkLiteral f)) :: Double
    return $ mkAtomVal $ Float v
  BoolLit b -> do
    v <- case BC.unpack (tkLiteral b) of
      "true" -> return True
      "false" -> return False
      _ -> throwFatal $ printf "invalid boolean literal: %s" (show b)
    return $ mkAtomVal $ Bool v
  NullLit _ -> return $ mkAtomVal Null
  BottomLit _ -> return $ mkBottomVal ""

data DeclWithEmbedIndex
  = RegDecl Declaration
  | -- | The index should start from 1 because the first is reserved for the struct literal itself.
    EmbedDecl Int Embedding

transStructLit :: StructLit -> ValAddr -> TM Val
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
  elems <- mapM (\x -> transDecl x (embedCnt > 0) addr) (reverse revRes)
  res <-
    foldM
      ( \acc elm -> do
          case acc of
            IsStruct struct -> insertElemToStruct elm struct
            _ -> return acc
      )
      (mkStructVal $ emptyStruct{stcID = sid})
      elems

  case res of
    -- If the result is a struct and it has embedded fields, then mark the embedded fields as embedded.
    IsStruct _
      | let embeds = [v | EmbedSAdder v <- elems]
      , not (null embeds) ->
          return $ mkMutableVal (mkEmbedUnifyOp (res : embeds))
    _ -> return res

strLitSegsToStr :: [StringLitSeg] -> ValAddr -> TM (Either Val BC.ByteString)
strLitSegsToStr segs addr = do
  -- TODO: efficiency
  (asM, aSegs, aExprs) <-
    foldM
      ( \(accCurStrM, accItpSegs, accItpExprs) seg -> case seg of
          UnicodeChars x ->
            return (Just x, accItpSegs, accItpExprs)
          AST.Interpolation _ e -> do
            t <- transExpr e (addr `appendSeg` mkMutArgFeature (length accItpExprs) False)
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
        return $ Left $ mkMutableVal $ mkItpSOp rSegs aExprs
    | length rSegs == 1, IplSegStr s <- head rSegs -> return $ Right s
    | otherwise -> throwFatal $ printf "invalid simple string literal: %s" (show segs)

-- | Evaluates a declaration.
transDecl :: DeclWithEmbedIndex -> Bool -> ValAddr -> TM StructElemAdder
transDecl decli hasEmbeds structAddr = case decli of
  EmbedDecl idx ed -> do
    v <- transEmbedding False ed (structAddr `appendSeg` mkMutArgFeature idx True)
    return $ EmbedSAdder v
  RegDecl decl -> case decl of
    EllipsisExpr (Ellipsis _ cM) ->
      maybe
        (return EmptyAdder) -- TODO: implement real ellipsis handling
        (\_ -> throwFatal "default constraints are not implemented yet")
        cM
    FieldDecl (AST.Field ls e) ->
      let declAddr = if hasEmbeds then structAddr `appendSeg` mkMutArgFeature 0 True else structAddr
       in transFDeclLabels ls e declAddr
    DeclLet (LetClause _ ident binde) -> do
      idIdx <- identTokenToTextIndex ident
      res <- fromJust <$> lookupIdentCurEnv idIdx
      val <- transExpr binde res.identAddr
      let featIdx = getTextIndexFromFeature res.identFeat
      return $ LetSAdder featIdx val
    _ -> throwFatal $ printf "impossible declaration: %s" (show decl)

identTokenToTextIndex :: Token -> TM TextIndex
identTokenToTextIndex tk = case tk.tkType of
  Token.Identifier -> textToTextIndex tk.tkLiteral
  _ -> throwFatal $ printf "expected identifier token, got %s" (show tk)

transEmbedding :: Bool -> Embedding -> ValAddr -> TM Val
transEmbedding _ (EmbeddingAlias (AliasExpr _ e)) addr = transExpr e addr
transEmbedding
  isListCompreh
  (EmbedComprehension (AST.Comprehension (Clauses (GuardClause _ ge) cls) lit))
  addr = do
    argsE <- mapM (\(j, c) -> transClause c (addr `appendSeg` mkMutArgFeature j False)) (zip [1 ..] cls)
    case sequence argsE of
      Left errVal -> return errVal
      Right args -> do
        gev <- transExpr ge (addr `appendSeg` mkMutArgFeature 0 False)
        let vs = ComprehArgIf gev : args
        sv <- transStructLit lit (addr `appendSeg` mkMutArgFeature (length vs) False)
        return $
          mkMutableVal $
            withEmptyOpFrame $
              Compreh $
                mkComprehension isListCompreh vs sv
transEmbedding
  isListCompreh
  (EmbedComprehension (AST.Comprehension (Clauses (ForClause _ i jM fe) cls) lit))
  addr = do
    let forClsAddr = addr `appendSeg` mkMutArgFeature 0 False
    iIdx <- identTokenToTextIndex i
    jIdxM <- case jM of
      Just j -> Just <$> identTokenToTextIndex j
      Nothing -> return Nothing
    res <- inClauseScope iIdx jIdxM forClsAddr $ do
      argsE <-
        mapM
          (\(j, c) -> transClause c (addr `appendSeg` mkMutArgFeature j False))
          (zip [1 ..] cls)
      case sequence argsE of
        Left errVal -> return errVal
        Right args -> do
          fev <- transExpr fe forClsAddr
          let vs = ComprehArgFor iIdx jIdxM fev : args
          sv <- transStructLit lit (addr `appendSeg` mkMutArgFeature (length vs) False)
          return $ mkMutableVal $ withEmptyOpFrame $ Compreh $ mkComprehension isListCompreh vs sv
    case res of
      Left errVal -> return errVal
      Right v -> return v

transClause :: Clause -> ValAddr -> TM (Either Val ComprehArg)
transClause c clAddr = case c of
  ClauseStart (GuardClause _ e) -> do
    t <- transExpr e clAddr
    return $ Right $ ComprehArgIf t
  ClauseStart (ForClause _ i jM e) -> do
    iIdx <- identTokenToTextIndex i
    jIdxM <- case jM of
      Just j -> Just <$> identTokenToTextIndex j
      Nothing -> return Nothing
    inSubClauseScope iIdx jIdxM clAddr $ do
      t <- transExpr e clAddr
      return $ ComprehArgFor iIdx jIdxM t
  ClauseLet (LetClause _ ident le) -> do
    idIdx <- identTokenToTextIndex ident
    inSubClauseScope idIdx Nothing clAddr $ do
      lt <- transExpr le clAddr
      return $ ComprehArgLet idIdx lt

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
      insertElemToStruct sf2 (emptyStruct{stcID = sid})
 where
  mkAdderWithValGen :: Label -> (ValAddr -> TM Val) -> TM StructElemAdder
  mkAdderWithValGen (Label le) vgen = case le of
    LabelName ln c -> do
      let attr = LabelAttr{lbAttrCnstr = cnstrFrom c, lbAttrIsIdent = isVar ln}
      case ln of
        (toIDentLabel -> Just key) -> do
          keyIdx <- identTokenToTextIndex key
          val <- vgen (structAddr `appendSeg` mkStringFeature keyIdx)
          return $ StaticSAdder keyIdx (staticFieldMker val attr)
        (toDynLabel -> Just se) -> do
          oid <- allocObjID
          selTree <- transExpr se (structAddr `appendSeg` mkDynFieldFeature oid 0)
          val <- vgen (structAddr `appendSeg` mkDynFieldFeature oid 1)
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
              val <- vgen (structAddr `appendSeg` mkStringFeature strIdx)
              return $ StaticSAdder strIdx (staticFieldMker val attr)
            Left t -> do
              val <- vgen (structAddr `appendSeg` mkDynFieldFeature oid 1)
              return $
                DynamicSAdder
                  oid
                  ( DynamicField
                      { dsfID = oid
                      , dsfAttr = attr
                      , dsfLabel = t
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
        pat <- transExpr pe (structAddr `appendSeg` mkPatternFeature cnstrid 0)
        val <- vgen cnstrValAddr
        cnstrvid <- getEnvID
        updatedAliasIdxM <- case aliasIdxM of
          Just origIdx -> Just <$> modifyTISuffix cnstrvid origIdx
          Nothing -> return Nothing
        return $ CnstrSAdder cnstrid pat updatedAliasIdxM val

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
  = StaticSAdder TextIndex Field
  | DynamicSAdder !Int DynamicField
  | CnstrSAdder !Int Val (Maybe TextIndex) Val
  | LetSAdder TextIndex Val
  | EmbedSAdder Val
  | ErrorAdder Val
  | EmptyAdder

{- | Insert a new element into the struct.

If the field is already in the struct, then unify the field with the new field.
-}
insertElemToStruct :: StructElemAdder -> Struct -> TM Val
insertElemToStruct adder struct = case adder of
  (StaticSAdder name sf) -> do
    case lookupStructStaticFieldBase name struct of
      -- The label is already in the struct, so we need to unify the field.
      Just extSF ->
        let
          unifySFOp =
            Value.Field
              { ssfValue = mkMutableVal (mkUnifyOp [ssfValue extSF, ssfValue sf])
              , ssfAttr = mergeAttrs (ssfAttr extSF) (ssfAttr sf)
              , ssfObjects = Set.empty
              }
          newStruct = updateStubAndField name unifySFOp struct
         in
          retSt newStruct
      -- The label is not seen before in the struct.
      _ -> retSt $ insertNewStubAndField name sf struct
  (DynamicSAdder i dsf) -> retSt $ insertStructNewDynField i dsf struct
  (CnstrSAdder i pattern alias val) -> retSt $ insertStructNewCnstr i pattern alias val struct
  (LetSAdder name val) -> retSt $ insertStructLet name val struct
  (ErrorAdder errVal) -> return errVal
  _ -> retSt struct
 where
  retSt = return . mkStructVal

transListLit :: ElementList -> ValAddr -> TM Val
transListLit (EllipsisList _) _ = return $ mkListVal [] []
transListLit (EmbeddingList es _) addr = do
  xs <- mapM (\(i, e) -> transEmbedding True e (addr `appendSeg` mkListStoreIdxFeature i)) (zip [0 ..] es)
  return $ mkListVal xs []

transUnaryExpr :: UnaryExpr -> ValAddr -> TM Val
transUnaryExpr ue addr = do
  t <- case ue of
    Primary primExpr -> transPrimExpr primExpr addr
    UnaryOp op e -> transUnaryOp op.tkType e addr
  return $ setExpr (Just (Unary ue)) t

builtinOpNameTable :: [(String, Val)]
builtinOpNameTable =
  -- built-in identifier names
  [("_", mkNewVal VNTop)]
    ++
    -- bounds
    map (\b -> (show b, mkBoundsValFromList [BdType b])) [minBound :: BdType .. maxBound :: BdType]
    -- built-in function names
    -- We use the function to distinguish the identifier from the string literal.
    ++ builtinFuncTable

transPrimExpr :: PrimaryExpr -> ValAddr -> TM Val
transPrimExpr e addr = case e of
  (PrimExprOperand op) -> case op of
    OpLiteral lit -> transLiteral lit addr
    OpName (OperandName ident) -> case lookup (BC.unpack (tkLiteral ident)) builtinOpNameTable of
      Just v -> return v
      Nothing -> do
        idIdx <- identTokenToTextIndex ident
        res <- lookupIdentInScopes idIdx ident.tkLoc
        case res of
          Left errVal -> return errVal
          Right (IdentLookupResult{identType, identFeat, identAddr}) -> do
            return $
              mkMutableVal $
                withEmptyOpFrame $
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
    args <- mapM (\(i, ae) -> transExpr ae (addr `appendSeg` mkMutArgFeature i False)) (zip [0 ..] aes)
    replaceFuncArgs p args

getResolvedIdentAddr :: ValAddr -> RefIdentType -> ValAddr
-- If the ident is an iteration variable, it is transient so its immediate features should be kept.
getResolvedIdentAddr addr ITIterBinding = addr
getResolvedIdentAddr addr _ =
  let xs = vFeatures addr
      isStubFeature f = case fetchLabelType f of
        PatternLabelType -> True
        DynFieldLabelType -> True
        _ -> False
   in ValAddr $ V.filter (\f -> isFeatureReferable f || isStubFeature f) xs

-- | Creates a new function tree for the original function with the arguments applied.
replaceFuncArgs :: Val -> [Val] -> TM Val
replaceFuncArgs t args = case t of
  IsRegOp mut fn ->
    return $
      setTOp
        ( setOpInSOp
            (RegOp $ fn{ropArgs = Seq.fromList args})
            mut
        )
        t
  _ -> throwFatal $ printf "%s is not a SOp" (show t)

{- | Evaluates the selector.

Parameters:
- pe is the primary expression.
- sel is the segment.
- addr is the addr to the current expression that contains the segment.
For example, { a: b: x.y }
If the field is "y", and the addr is "a.b", expr is "x.y", the structValAddr is "x".
-}
transSelector :: PrimaryExpr -> Syntax.AST.Selector -> ValAddr -> TM Val
transSelector pe astSel addr = do
  let oprdAddr = case pe of
        PrimExprIndex{} -> addr
        PrimExprSelector{} -> addr
        _ -> addr `appendSeg` valueSelectFeature
  oprnd <- transPrimExpr pe oprdAddr
  (selAddr, selVGen) <- getSelCons addr oprnd
  let f sel = selVGen (mkAtomVal (String sel))
  case astSel of
    IDSelector ident -> return $ f (tkLiteral ident)
    StringSelector (SimpleStringLit _ segs) -> do
      rE <- strLitSegsToStr segs selAddr
      case rE of
        Left _ -> return $ mkBottomVal $ printf "selector should not have interpolation"
        Right str -> return $ f str

transIndex :: PrimaryExpr -> Expression -> ValAddr -> TM Val
transIndex pe e addr = do
  let oprdAddr = case pe of
        PrimExprIndex{} -> addr
        PrimExprSelector{} -> addr
        _ -> addr `appendSeg` valueSelectFeature
  oprnd <- transPrimExpr pe oprdAddr
  (selAddr, selVGen) <- getSelCons addr oprnd
  sel <- transExpr e selAddr
  return $ selVGen sel

getSelCons :: ValAddr -> Val -> TM (ValAddr, Val -> Val)
getSelCons addr oprnd = case oprnd of
  IsValMutable sop@(Op (Ref ref)) -> do
    let n = length ref.selectors
    return
      ( appendSeg addr (mkMutArgFeature n False)
      , \sel -> mkMutableVal $ setOpInSOp (Ref $ appendRefArg sel ref) sop
      )
  IsValMutable sop@(Op (VSelect index@(ValueSelect _ indexes))) -> do
    let n = length indexes
    return
      ( appendSeg addr (mkMutArgFeature n False)
      , \sel -> mkMutableVal $ setOpInSOp (VSelect $ appendValueSelectArg sel index) sop
      )
  _ -> do
    let selAddr = appendSeg addr (mkMutArgFeature 0 False)
    return
      ( selAddr
      , \sel -> mkMutableVal $ withEmptyOpFrame $ VSelect $ ValueSelect oprnd (Seq.fromList [sel])
      )

-- | Create an index or reference to select val from an operand.
selectValFromVal :: Val -> Val -> Val
selectValFromVal oprnd selArg = case oprnd of
  IsValMutable sop@(Op (Ref ref)) ->
    mkMutableVal $ setOpInSOp (Ref $ appendRefArg selArg ref) sop
  IsValMutable sop@(Op (VSelect index)) ->
    mkMutableVal $ setOpInSOp (VSelect $ appendValueSelectArg selArg index) sop
  _ -> mkMutableVal $ withEmptyOpFrame $ VSelect $ ValueSelect oprnd (Seq.fromList [selArg])

{- | Evaluates the unary operator.

unary operator should only be applied to atoms.
-}
transUnaryOp :: TokenType -> UnaryExpr -> ValAddr -> TM Val
transUnaryOp op e addr = do
  t <- transUnaryExpr e (addr `appendSeg` mkMutArgFeature 0 False)
  let tWithE = setExpr (Just (Unary e)) t
  return $ mkMutableVal (mkUnaryOp op tWithE)

{- | order of arguments is important for disjunctions.

left is always before right.
-}
transBinary :: TokenType -> Expression -> Expression -> ValAddr -> TM Val
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
transBinary Disjoin e1 e2 addr = transDisj e1 e2 addr
transBinary Unify e1 e2 addr = do
  -- Peek the left operand to determine the address for both operands.
  -- If the left operand is not a regular unify op, then the leftmost node is the first conjunct.
  -- The next node is always on the right side of the unify op.
  let laddr = case e1 of
        Binary (tkType -> Unify) _ _ -> addr
        _ -> addr `appendSeg` mkMutArgFeature 0 True
  lv <- transExpr e1 laddr

  -- If the left operand is a regular unify op, then we just need to append the new conjunct to the unify op. Otherwise,
  -- the right node is the second conjunct.
  let raddr = case lv of
        IsRegularUnifyOp _ u -> addr `appendSeg` mkMutArgFeature (length u.conjs) True
        _ -> addr `appendSeg` mkMutArgFeature 1 True
  rv <- transExpr e2 raddr
  let res = case lv of
        IsRegularUnifyOp mut u -> mkMutableVal (setOpInSOp (UOp (appendUnifyConj rv u)) mut)
        _ -> mkMutableVal $ mkUnifyOp [lv, rv]
  return res
transBinary op e1 e2 addr = do
  lv <- transExpr e1 (appendSeg addr (mkMutArgFeature 0 False))
  rv <- transExpr e2 (appendSeg addr (mkMutArgFeature 1 False))
  return $ mkMutableVal (mkBinaryOp op lv rv)

{- | Translates a disjunction expression.

Since the leftmost node is the first term and the next term is always on the right, either at this
level or the next level, we can peek the left operand to determine the address for both operands and whether we treat
the current disjOp as an accumulator, which means we apply the right operand to the accumulating disjunction operator
that is on the left side.
-}
transDisj :: Expression -> Expression -> ValAddr -> TM Val
transDisj e1 e2 addr = do
  let parseE e eAddr = case e of
        Unary (UnaryOp (tkType -> Token.Multiply) se) -> do
          v <- transUnaryExpr se eAddr
          return (v, True)
        _ -> do
          v <- transExpr e eAddr
          return (v, False)

  let (laddr, leftIsDisjOp) = case e1 of
        Binary (tkType -> Disjoin) _ _ -> (addr, True)
        _ -> (addr `appendSeg` mkMutArgFeature 0 False, False)
  (lv, isLStar) <- parseE e1 laddr

  let raddr = case lv of
        IsDisjoinOp _ d -> addr `appendSeg` mkMutArgFeature (length d.djoTerms) False
        _ -> addr `appendSeg` mkMutArgFeature 1 False
  (rv, isRStar) <- parseE e2 raddr
  let res = case lv of
        -- The left expression must be a disjOp too. Otherwise expressions like OpExpression that can be parsed as
        -- disjunction will be incorrectly flattened.
        -- For example, (*a | b) | c should only yield a disjunction with two terms, not a disjunction with three terms.
        -- The same applies to (a | b) | c.
        IsDisjoinOp mut d | leftIsDisjOp -> mkMutableVal (setOpInSOp (DisjOp (appendDisjTerm isRStar rv d)) mut)
        _ -> mkMutableVal $ mkDisjoinOpFromList [DisjTerm isLStar lv, DisjTerm isRStar rv]
  return res

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

type TM = RWST () () TransState (ExceptT String IO)

allocObjID :: TM Int
allocObjID = do
  modify' $ \s -> let oid = objID s in s{objID = oid + 1}
  gets objID

throwFatal :: (HasCallStack) => String -> TM a
throwFatal msg = throwError $ msg ++ "\n" ++ prettyCallStack callStack

getEnvID :: TM Int
getEnvID = do
  (Environments envs) <- gets envs
  case envs of
    [] -> throwFatal "no environment"
    (env : _) -> return env.envid

-- | Lookup the identifier in the scopes. If not found, return an error value.
lookupIdentInScopes :: TextIndex -> Location -> TM (Either Val IdentLookupResult)
lookupIdentInScopes identTI loc = do
  res <- lookupIdentInEnvs identTI
  case res of
    Just r -> return $ Right r
    Nothing -> do
      errMsg <- notFoundMsg identTI (Just loc)
      return $ Left $ mkBottomVal errMsg

notFoundMsg :: TextIndex -> Maybe Location -> TM String
notFoundMsg ident locM = do
  idStr <- tshow ident
  case locM of
    Nothing -> return $ printf "reference %s is not found" (show idStr)
    Just loc -> do return $ printf "reference %s is not found:\n\t%s" (show idStr) (show loc)

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

addNameToCurrentEnv :: TextIndex -> RefIdentType -> TM (Either Val ())
addNameToCurrentEnv name identType = do
  checked <- checkIdentInEnvs name identType
  case checked of
    Left errVal -> return $ Left errVal
    Right _ -> do
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
      return $ Right ()
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

checkIdentInEnvs :: TextIndex -> RefIdentType -> TM (Either Val ())
checkIdentInEnvs key identType = do
  res <- lookupIdentInEnvs key
  case res of
    Just (IdentLookupResult{isInTopEnv, identType = targetIdentType})
      -- If the identifier exists and the types conflict, return an error.
      | isInTopEnv
      , targetIdentType `elem` [ITLetBinding, ITIterBinding]
      , identType `elem` [ITLetBinding, ITIterBinding] ->
          Left <$> lbRedeclErr key
      | targetIdentType == ITField && identType == ITLetBinding
          || targetIdentType == ITLetBinding && identType == ITField ->
          Left <$> aliasErr key
    _ -> return $ Right ()

aliasErr :: TextIndex -> TM Val
aliasErr name = do
  nameStr <- tshow name
  return $ mkBottomVal $ printf "can not have both alias and field with name %s in the same scope" (show nameStr)

lbRedeclErr :: TextIndex -> TM Val
lbRedeclErr name = do
  nameStr <- tshow name
  return $ mkBottomVal $ printf "%s redeclared in same scope" (show nameStr)

inStructScope :: [Declaration] -> ValAddr -> TM Val -> TM Val
inStructScope decls addr action = do
  enterRes <- enterStructScope decls addr
  case enterRes of
    Left errVal -> return errVal
    Right () -> do
      result <- action
      leaveRes <- leaveStructScope
      case leaveRes of
        Left errVal -> return errVal
        Right () -> return result

enterStructScope :: [Declaration] -> ValAddr -> TM (Either Val ())
enterStructScope decls addr = do
  sid <- allocObjID
  modify' $ mapEnvs (pushBlock sid EnvTypeStruct addr)
  -- First add all the immediate field and let binding identifiers to the current scope.
  -- This is to allow the references in the sub tree to refer to the identifiers that have not been translated yet.
  -- Unlike other languages, the order of field declarations does not matter.
  foldM
    ( \acc dl -> do
        res <- addIdentDeclToScope dl
        case acc >> res of
          Left errVal -> return $ Left errVal
          Right () -> return $ Right ()
    )
    (Right ())
    decls

-- | Add the immediate field or let binding identifiers to the current scope.
addIdentDeclToScope :: Declaration -> TM (Either Val ())
addIdentDeclToScope dl = case dl of
  FieldDecl (AST.Field ls _) -> addFieldIdent ls
  DeclLet (LetClause _ ident _) -> do
    keyIdx <- identTokenToTextIndex ident
    addNameToCurrentEnv keyIdx ITLetBinding
  _ -> return $ Right ()
 where
  addFieldIdent ls = do
    res <- addLabelToScope ls
    case res of
      Just keyIdx -> addNameToCurrentEnv keyIdx ITField
      Nothing -> return $ Right ()

  addLabelToScope :: [Label] -> TM (Maybe TextIndex)
  addLabelToScope (Label (LabelName ln _) : _)
    | Just key <- toIDentLabel ln = Just <$> identTokenToTextIndex key
  addLabelToScope _ = return Nothing

leaveStructScope :: TM (Either Val ())
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
    then return $ Right ()
    else do
      let firstName = head unreferencedNames
      firstNameT <- tshow firstName
      return $ Left $ mkBottomVal $ printf "unreferenced let clause let %s" (show firstNameT)

{- | Enter a constraint value scope for evaluating a constraint body.

The alias identifier of the constraint, if exists, is added to the scope.
For example, [X=constraint]: value, a new environment is created for evaluating "value" with just X in the scope.
            ^---------------------^
              scope for evaluating "value"
-}
inCnstrValScope :: Maybe TextIndex -> ValAddr -> TM StructElemAdder -> TM StructElemAdder
inCnstrValScope aliasIdxM addr action = do
  enterRes <- enterCnstrValScope aliasIdxM addr
  case enterRes of
    Left errVal -> return (ErrorAdder errVal)
    Right () -> do
      result <- action
      leaveCnstrValScope
      return result

enterCnstrValScope :: Maybe TextIndex -> ValAddr -> TM (Either Val ())
enterCnstrValScope aliasIdxM addr = do
  fid <- allocObjID
  modify' $ mapEnvs (pushBlock fid EnvTypeCnstr addr)
  case aliasIdxM of
    Just aliasIdx -> addNameToCurrentEnv aliasIdx ITLetBinding
    Nothing -> return $ Right ()

leaveCnstrValScope :: TM ()
leaveCnstrValScope = do
  envs <- gets envs
  let (_, restEnvs) = popBlock envs
  modify' $ mapEnvs (const restEnvs)

enterClauseScope :: TextIndex -> Maybe TextIndex -> ValAddr -> TM (Either Val ())
enterClauseScope iIdx jIdxM addr = do
  fid <- allocObjID
  modify' $ mapEnvs (pushBlock fid EnvTypeClause addr)
  res1 <- addNameToCurrentEnv iIdx ITIterBinding
  case res1 of
    Left errVal -> return $ Left errVal
    Right () -> case jIdxM of
      Just jIdx -> addNameToCurrentEnv jIdx ITIterBinding
      Nothing -> return $ Right ()

leaveClauseScope :: TM ()
leaveClauseScope = do
  envs <- gets envs
  let (_, restEnvs) = popBlock envs
  modify' $ mapEnvs (const restEnvs)

inClauseScope :: TextIndex -> Maybe TextIndex -> ValAddr -> TM a -> TM (Either Val a)
inClauseScope iIdx jIdxM addr action = do
  enterRes <- enterClauseScope iIdx jIdxM addr
  cid <- getEnvID
  res <- action
  leaveUntil cid
  case enterRes of
    Left errVal -> return $ Left errVal
    Right () -> return $ Right res
 where
  leaveUntil cid = do
    subID <- getEnvID
    when (subID /= cid) $
      leaveClauseScope >> leaveUntil cid

{- | Enters a sub-clause scope for evaluating a clause argument without leaving the scope after evaluation.

The reason is that clause arguments can be nested, and we want to keep the outer clause scope active.
-}
inSubClauseScope :: TextIndex -> Maybe TextIndex -> ValAddr -> TM a -> TM (Either Val a)
inSubClauseScope iIdx jIdxM addr action = do
  enterRes <- enterClauseScope iIdx jIdxM addr
  res <- action
  case enterRes of
    Left errVal -> return $ Left errVal
    Right () -> return $ Right res

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
