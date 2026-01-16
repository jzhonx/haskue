{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module EvalExpr where

import Control.Monad (foldM)
import qualified Data.ByteString.Char8 as BC
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import Reduce.Monad (RM, allocRMObjID, throwFatal)
import StringIndex (ShowWTIndexer (..), TextIndex, bsToTextIndex, textToTextIndex)
import Syntax.AST
import qualified Syntax.AST as AST
import Syntax.Token (
  Token,
  TokenType (Disjoin, Exclamation, QuestionMark, Unify),
  emptyLoc,
  tkLiteral,
  tkLiteralToText,
  tkType,
 )
import qualified Syntax.Token as Token
import Text.Printf (printf)
import Value

evalSourceFile :: SourceFile -> RM Val
evalSourceFile (SourceFile decls) = evalStructLit (StructLit emptyLoc decls emptyLoc)

{- | evalExpr and all expr* should return the same level tree cursor.
The label and the evaluated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every eval* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the addr of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
evalExpr :: Expression -> RM Val
evalExpr e = do
  t <- case e of
    (Unary ue) -> evalUnaryExpr ue
    (Binary op e1 e2) -> evalBinary op.tkType e1 e2
  return $ setExpr (Just e) t

evalLiteral :: Literal -> RM Val
evalLiteral (LitStruct s) = evalStructLit s
evalLiteral (LitList (ListLit _ l _)) = evalListLit l
evalLiteral (LitBasic a)
  | (StringLit (SimpleStringL (SimpleStringLit _ segs))) <- a = segsToStrAtom segs
  | (StringLit (MultiLineStringL (MultiLineStringLit _ segs))) <- a = segsToStrAtom segs
 where
  segsToStrAtom segs = do
    rE <- strLitSegsToStr segs
    return $ case rE of
      Left t -> t
      Right str -> mkAtomVal $ String str
evalLiteral (LitBasic a) = case a of
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
  -- TopLit -> mkNewVal VNTop
  BottomLit _ -> return $ mkBottomVal ""

evalStructLit :: StructLit -> RM Val
evalStructLit (StructLit _ decls _) = do
  sid <- allocRMObjID
  elems <- mapM evalDecl decls
  res <-
    foldM
      ( \acc elm -> case acc of
          IsStruct struct -> insertElemToStruct elm struct
          _ -> return acc
      )
      (mkStructVal $ emptyStruct{stcID = sid})
      elems
  case res of
    -- If the result is a struct and it has embedded fields, then mark the embedded fields as embedded.
    IsStruct _
      | let embeds = [v{embType = ETEmbedded sid} | EmbedSAdder v <- elems]
      , not (null embeds) -> do
          return $ mkMutableVal (mkEmbedUnifyOp $ res{embType = ETEnclosing} : embeds)
    _ -> return res

strLitSegsToStr :: [StringLitSeg] -> RM (Either Val T.Text)
strLitSegsToStr segs = do
  -- TODO: efficiency
  (asM, aSegs, aExprs) <-
    foldM
      ( \(accCurStrM, accItpSegs, accItpExprs) seg -> case seg of
          UnicodeChars x ->
            return
              ( Just x
              , accItpSegs
              , accItpExprs
              )
          AST.Interpolation _ e -> do
            t <- evalExpr e
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
    | null rSegs -> return $ Right T.empty
    | not (null aExprs) ->
        return $ Left $ mkMutableVal $ mkItpSOp rSegs aExprs
    | length rSegs == 1, IplSegStr s <- head rSegs -> return $ Right s
    | otherwise -> throwFatal $ printf "invalid simple string literal: %s" (show segs)

-- | Evaluates a declaration.
evalDecl :: Declaration -> RM StructElemAdder
evalDecl decl = case decl of
  Embedding ed -> do
    v <- evalEmbedding False ed
    return $ EmbedSAdder v
  EllipsisDecl (Ellipsis _ cM) ->
    maybe
      (return EmptyAdder) -- TODO: implement real ellipsis handling
      (\_ -> throwFatal "default constraints are not implemented yet")
      cM
  FieldDecl (AST.Field ls e) ->
    evalFDeclLabels ls e
  DeclLet (LetClause _ ident binde) -> do
    idIdx <- identTokenToTextIndex ident
    val <- evalExpr binde
    return $ LetSAdder idIdx val

identTokenToTextIndex :: Token -> RM TextIndex
identTokenToTextIndex tk = case tk.tkType of
  Token.Identifier -> bsToTextIndex tk.tkLiteral
  _ -> throwFatal $ printf "expected identifier token, got %s" (show tk)

evalEmbedding :: Bool -> Embedding -> RM Val
evalEmbedding _ (AliasExpr e) = evalExpr e
evalEmbedding
  isListCompreh
  ( EmbedComprehension
      (AST.Comprehension (Clauses (GuardClause _ ge) cls) lit)
    ) = do
    gev <- evalExpr ge
    clsv <- mapM evalClause cls
    sv <- evalStructLit lit
    return $ mkMutableVal $ withEmptyOpFrame $ Compreh $ mkComprehension isListCompreh (ComprehArgIf gev : clsv) sv
evalEmbedding
  isListCompreh
  (EmbedComprehension (AST.Comprehension (Clauses (ForClause _ i jM fe) cls) lit)) = do
    fev <- evalExpr fe
    clsv <- mapM evalClause cls
    sv <- evalStructLit lit
    iidx <- identTokenToTextIndex i
    jidxM <- case jM of
      Just j -> Just <$> identTokenToTextIndex j
      Nothing -> return Nothing
    return $
      mkMutableVal $
        withEmptyOpFrame $
          Compreh $
            mkComprehension isListCompreh (ComprehArgFor iidx jidxM fev : clsv) sv

evalClause :: Clause -> RM ComprehArg
evalClause c = case c of
  ClauseStart (GuardClause _ e) -> do
    t <- evalExpr e
    return $ ComprehArgIf t
  ClauseStart (ForClause _ i jM e) -> do
    iidx <- identTokenToTextIndex i
    jidxM <- case jM of
      Just j -> Just <$> identTokenToTextIndex j
      Nothing -> return Nothing
    t <- evalExpr e
    return $ ComprehArgFor iidx jidxM t
  ClauseLet (LetClause _ ident le) -> do
    idIdx <- identTokenToTextIndex ident
    lt <- evalExpr le
    return $ ComprehArgLet idIdx lt

evalFDeclLabels :: [Label] -> Expression -> RM StructElemAdder
evalFDeclLabels lbls e =
  case lbls of
    [] -> throwFatal "empty labels"
    [l1] ->
      do
        val <- evalExpr e
        mkAdder l1 val
    l1 : l2 : rs ->
      do
        sf2 <- evalFDeclLabels (l2 : rs) e
        sid <- allocRMObjID
        val <- insertElemToStruct sf2 (emptyStruct{stcID = sid})
        mkAdder l1 val
 where
  mkAdder :: Label -> Val -> RM StructElemAdder
  mkAdder (Label le) val = case le of
    LabelName ln c ->
      let attr = LabelAttr{lbAttrCnstr = cnstrFrom c, lbAttrIsIdent = isVar ln}
       in case ln of
            (toIDentLabel -> Just key) -> do
              keyIdx <- identTokenToTextIndex key
              return $ StaticSAdder keyIdx (staticFieldMker val attr)
            (toDynLabel -> Just se) -> do
              selTree <- evalExpr se
              oid <- allocRMObjID
              return $ DynamicSAdder oid (DynamicField oid attr selTree False val)
            (toSStrLabel -> Just (SimpleStringLit _ segs)) -> do
              rE <- strLitSegsToStr segs
              case rE of
                Right str -> do
                  strIdx <- textToTextIndex str
                  return $ StaticSAdder strIdx (staticFieldMker val attr)
                Left t -> do
                  oid <- allocRMObjID
                  return $ DynamicSAdder oid (DynamicField oid attr t True val)
            _ -> throwFatal "invalid label"
    LabelExpr _ pe _ -> do
      pat <- evalExpr pe
      oid <- allocRMObjID
      return (CnstrSAdder oid pat val)

  -- Returns the label identifier and the whether the label is static.
  toIDentLabel :: LabelName -> Maybe Token
  toIDentLabel (LabelID ident) = Just ident
  toIDentLabel _ = Nothing

  toDynLabel :: LabelName -> Maybe Expression
  toDynLabel (LabelNameExpr _ lne _) = Just lne
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

data StructElemAdder
  = StaticSAdder TextIndex Field
  | DynamicSAdder !Int DynamicField
  | CnstrSAdder !Int Val Val
  | LetSAdder TextIndex Val
  | EmbedSAdder Val
  | EmptyAdder

{- | Insert a new element into the struct.

If the field is already in the struct, then unify the field with the new field.
-}
insertElemToStruct :: StructElemAdder -> Struct -> RM Val
insertElemToStruct adder struct = case adder of
  (StaticSAdder name sf) -> do
    nameStr <- tshow name
    maybe
      ( case lookupStructStubVal name struct of
          -- The label is already in the struct, so we need to unify the field.
          [StructStubField extSF] ->
            let
              unifySFOp =
                Value.Field
                  { ssfValue = mkMutableVal (mkUnifyOp [ssfValue extSF, ssfValue sf])
                  , ssfAttr = mergeAttrs (ssfAttr extSF) (ssfAttr sf)
                  , ssfObjects = Set.empty
                  }
              newStruct = updateStubAndField name unifySFOp struct
             in
              return $ mkStructVal newStruct
          [StructStubLet _] -> do
            return $ aliasErr nameStr
          -- The label is not seen before in the struct.
          [] -> return $ mkStructVal $ insertNewStubAndField name sf struct
          _ -> return $ aliasErr nameStr
      )
      return
      (existCheck name nameStr False)
  (DynamicSAdder i dsf) -> return . mkStructVal $ insertStructNewDynField i dsf struct
  (CnstrSAdder i pattern val) -> return . mkStructVal $ insertStructNewCnstr i pattern val struct
  (LetSAdder name val) -> do
    -- Use the pure identifier for error messages.
    nameStr <- tshow name
    return $
      fromMaybe
        -- The name is not seen before in the block.
        (mkStructVal $ insertStructLet name val struct)
        (existCheck name nameStr True)
  _ -> return $ mkStructVal struct
 where
  -- In both errors, we show the name so that the name is quoted.
  aliasErr name = mkBottomVal $ printf "can not have both alias and field with name %s in the same scope" (show name)
  lbRedeclErr name = mkBottomVal $ printf "%s redeclared in same scope" (show name)

  -- Checks if name is already in the block. If it is, then return an error message.
  existCheck :: TextIndex -> T.Text -> Bool -> Maybe Val
  existCheck nameIdx name isNameLet =
    case (lookupStructStubVal nameIdx struct, isNameLet) of
      ([StructStubField f], True)
        | lbAttrIsIdent (ssfAttr f) -> Just $ aliasErr name
      ([StructStubLet _], True) -> Just $ lbRedeclErr name
      ([StructStubLet _], False) -> Just $ aliasErr name
      ([_, _], _) -> Just $ aliasErr name
      _ -> Nothing

evalListLit :: ElementList -> RM Val
evalListLit (EmbeddingList es) = do
  xs <- mapM (evalEmbedding True) es
  return $ mkListVal xs []

evalUnaryExpr :: UnaryExpr -> RM Val
evalUnaryExpr ue = do
  t <- case ue of
    Primary primExpr -> evalPrimExpr primExpr
    UnaryOp op e -> evalUnaryOp op.tkType e
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

evalPrimExpr :: PrimaryExpr -> RM Val
evalPrimExpr e = case e of
  (PrimExprOperand op) -> case op of
    OpLiteral lit -> evalLiteral lit
    OpName (OperandName ident) -> case lookup (T.unpack (tkLiteralToText ident)) builtinOpNameTable of
      Just v -> return v
      Nothing -> do
        idIdx <- identTokenToTextIndex ident
        return $ mkMutableVal $ withEmptyOpFrame $ Ref $ emptyIdentRef idIdx
    OpExpression _ expr _ -> do
      x <- evalExpr expr
      return $ x{isRootOfSubVal = True}
  (PrimExprSelector primExpr _ sel) -> do
    p <- evalPrimExpr primExpr
    evalSelector e sel p
  (PrimExprIndex primExpr _ idx _) -> do
    p <- evalPrimExpr primExpr
    evalIndex e idx p
  (PrimExprArguments primExpr _ aes _) -> do
    p <- evalPrimExpr primExpr
    args <- mapM evalExpr aes
    replaceFuncArgs p args

-- | Creates a new function tree for the original function with the arguments applied.
replaceFuncArgs :: Val -> [Val] -> RM Val
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
evalSelector :: PrimaryExpr -> Selector -> Val -> RM Val
evalSelector _ astSel oprnd = do
  let f sel = appendSelToRefVal oprnd (mkAtomVal (String sel))
  case astSel of
    IDSelector ident -> return $ f (tkLiteralToText ident)
    StringSelector (SimpleStringLit _ segs) -> do
      rE <- strLitSegsToStr segs
      case rE of
        Left _ -> return $ mkBottomVal $ printf "selector should not have interpolation"
        Right str -> return $ f str

evalIndex :: PrimaryExpr -> Expression -> Val -> RM Val
evalIndex _ e oprnd = do
  sel <- evalExpr e
  return $ appendSelToRefVal oprnd sel

{- | Evaluates the unary operator.

unary operator should only be applied to atoms.
-}
evalUnaryOp :: TokenType -> UnaryExpr -> RM Val
evalUnaryOp op e = do
  t <- evalUnaryExpr e
  let tWithE = setExpr (Just (Unary e)) t
  return $ mkMutableVal (mkUnaryOp op tWithE)

{- | order of arguments is important for disjunctions.

left is always before right.
-}
evalBinary :: TokenType -> Expression -> Expression -> RM Val
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary Disjoin e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  case op of
    Unify -> return $ flattenUnify lt rt
    _ -> return $ mkMutableVal (mkBinaryOp op lt rt)

flattenUnify :: Val -> Val -> Val
flattenUnify l r = case getLeftAcc of
  Just acc -> mkMutableVal $ mkUnifyOp (toList acc ++ [r])
  Nothing -> mkMutableVal $ mkUnifyOp [l, r]
 where
  getLeftAcc = case l of
    -- The left tree is an accumulator only if it is a unify op.
    IsValMutable (Op (UOp u)) -> Just u.conjs
    _ -> Nothing

evalDisj :: Expression -> Expression -> RM Val
evalDisj e1 e2 = do
  ((isLStar, lt), (isRStar, rt)) <- case (e1, e2) of
    ( Unary (UnaryOp (tkType -> Token.Multiply) se1)
      , Unary (UnaryOp (tkType -> Token.Multiply) se2)
      ) -> do
        l <- evalUnaryExpr se1
        r <- evalUnaryExpr se2
        return ((,) True l, (,) True r)
    (Unary (UnaryOp (tkType -> Token.Multiply) se1), _) -> do
      l <- evalUnaryExpr se1
      r <- evalExpr e2
      return ((,) True l, (,) False r)
    (_, Unary (UnaryOp (tkType -> Token.Multiply) se2)) -> do
      l <- evalExpr e1
      r <- evalUnaryExpr se2
      return ((,) False l, (,) True r)
    (_, _) -> do
      l <- evalExpr e1
      r <- evalExpr e2
      return ((,) False l, (,) False r)
  let r = flattenDisj (DisjTerm isLStar lt) (DisjTerm isRStar rt)
  return r

{- | Flatten the disjoin op tree.

Since the leftmost term is in the deepest left and the next term is always on the right, either at this
level or the next level, we can append the right term to accumulating disjunction terms.

For example, a | b | c is parsed as
     |
   /   \
   |    c
 /   \
 a   b

We start with the a, where a is one of a root disj, a marked term or a regular non-disjunction value. Then append b to
it, and then append c to the accumulator.
We never need to go deeper into the right nodes.
-}
flattenDisj :: DisjTerm -> DisjTerm -> Val
flattenDisj l r = case getLeftAcc of
  Just acc -> mkMutableVal $ mkDisjoinOp (acc Seq.|> r)
  Nothing -> mkMutableVal $ mkDisjoinOp (Seq.fromList [l, r])
 where
  getLeftAcc = case dstValue l of
    IsValMutable (Op (DisjOp dj))
      -- The left term is an accumulator only if it is a disjoin op and not marked nor the root.
      -- If the left term is a marked term, it implies that it is a root.
      | not (dstMarked l) && not (isRootOfSubVal (dstValue l)) -> Just (djoTerms dj)
    _ -> Nothing
