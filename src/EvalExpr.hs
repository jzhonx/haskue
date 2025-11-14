{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module EvalExpr where

import AST
import Control.Monad (foldM)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import Reduce.RMonad (RM, allocRMObjID, throwFatal)
import StringIndex (ShowWithTextIndexer (..), TextIndex, textToTextIndex)
import Text.Printf (printf)
import Value

evalSourceFile :: SourceFile -> RM Tree
evalSourceFile (SourceFile decls) = evalStructLit (pure $ StructLit decls)

{- | evalExpr and all expr* should return the same level tree cursor.
The label and the evaluated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every eval* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the addr of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
evalExpr :: Expression -> RM Tree
evalExpr e = do
  t <- case anVal e of
    (ExprUnaryExpr ue) -> evalUnaryExpr ue
    (ExprBinaryOp op e1 e2) -> evalBinary op e1 e2
  return $ setExpr t (Just e)

evalLiteral :: Literal -> RM Tree
evalLiteral (anVal -> LitStructLit s) = evalStructLit s
evalLiteral (anVal -> ListLit l) = evalListLit l
evalLiteral (anVal -> StringLit (anVal -> SimpleStringL s)) = do
  rE <- simpleStringLitToStr s
  return $ case rE of
    Left t -> t
    Right str -> mkAtomTree $ String str
evalLiteral lit = return v
 where
  v = case anVal lit of
    IntLit i -> mkAtomTree $ Int i
    FloatLit a -> mkAtomTree $ Float a
    BoolLit b -> mkAtomTree $ Bool b
    NullLit -> mkAtomTree Null
    TopLit -> mkNewTree TNTop
    BottomLit -> mkBottomTree ""
    _ -> error "evalLiteral: invalid literal"

evalStructLit :: StructLit -> RM Tree
evalStructLit (anVal -> StructLit decls) = do
  sid <- allocRMObjID
  elems <- mapM evalDecl decls
  res <-
    foldM
      ( \acc elm -> case acc of
          IsStruct struct -> insertElemToStruct elm struct
          _ -> return acc
      )
      (mkStructTree $ emptyStruct{stcID = sid})
      elems
  case res of
    -- If the result is a struct and it has embedded fields, then mark the embedded fields as embedded.
    IsStruct _
      | let embeds = [v{embType = ETEmbedded sid} | EmbedSAdder v <- elems]
      , not (null embeds) -> do
          return $ mkMutableTree (mkUnifyOp $ res{embType = ETEnclosing} : embeds)
    _ -> return res

simpleStringLitToStr :: SimpleStringLit -> RM (Either Tree T.Text)
simpleStringLitToStr (anVal -> SimpleStringLit segs) = do
  (asM, aSegs, aExprs) <-
    foldM
      ( \(accCurStrM, accItpSegs, accItpExprs) seg -> case seg of
          UnicodeVal x ->
            return
              -- TODO: efficiency
              ( maybe (Just (T.singleton x)) (\y -> Just $ T.snoc y x) accCurStrM
              , accItpSegs
              , accItpExprs
              )
          InterpolationStr (anVal -> AST.Interpolation e) -> do
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
        return $ Left $ mkMutableTree $ mkItpMutable rSegs aExprs
    | length rSegs == 1, IplSegStr s <- head rSegs -> return $ Right s
    | otherwise -> throwFatal $ printf "invalid simple string literal: %s" (show segs)

-- | Evaluates a declaration.
evalDecl :: Declaration -> RM StructElemAdder
evalDecl decl = case anVal decl of
  AST.Embedding ed -> do
    v <- evalEmbedding False ed
    return $ EmbedSAdder v
  EllipsisDecl (anVal -> Ellipsis cM) ->
    maybe
      (return EmptyAdder) -- TODO: implement real ellipsis handling
      (\_ -> throwFatal "default constraints are not implemented yet")
      cM
  FieldDecl (anVal -> AST.Field ls e) ->
    evalFDeclLabels ls e
  DeclLet (anVal -> LetClause ident binde) -> do
    idIdx <- textToTextIndex (anVal ident)
    val <- evalExpr binde
    return $ LetSAdder idIdx val

evalEmbedding :: Bool -> AST.Embedding -> RM Tree
evalEmbedding _ (anVal -> AliasExpr e) = evalExpr e
evalEmbedding
  isListCompreh
  ( anVal ->
      EmbedComprehension
        (anVal -> AST.Comprehension (anVal -> Clauses (anVal -> GuardClause ge) cls) lit)
    ) = do
    gev <- evalExpr ge
    clsv <- mapM evalClause cls
    sv <- evalStructLit lit
    return $ mkMutableTree $ withEmptyMutFrame $ Compreh $ mkComprehension isListCompreh (ComprehArgIf gev : clsv) sv
evalEmbedding
  isListCompreh
  ( anVal ->
      EmbedComprehension (anVal -> AST.Comprehension (anVal -> Clauses (anVal -> ForClause i jM fe) cls) lit)
    ) = do
    fev <- evalExpr fe
    clsv <- mapM evalClause cls
    sv <- evalStructLit lit
    iidx <- textToTextIndex (anVal i)
    jidxM <- case jM of
      Just j -> Just <$> textToTextIndex (anVal j)
      Nothing -> return Nothing
    return $
      mkMutableTree $
        withEmptyMutFrame $
          Compreh $
            mkComprehension isListCompreh (ComprehArgFor iidx jidxM fev : clsv) sv
evalEmbedding _ _ = throwFatal "invalid embedding"

evalClause :: Clause -> RM ComprehArg
evalClause c = case anVal c of
  ClauseStartClause (anVal -> GuardClause e) -> do
    t <- evalExpr e
    return $ ComprehArgIf t
  ClauseStartClause (anVal -> ForClause (anVal -> i) jM e) -> do
    iidx <- textToTextIndex i
    jidxM <- case jM of
      Just j -> Just <$> textToTextIndex (anVal j)
      Nothing -> return Nothing
    t <- evalExpr e
    return $ ComprehArgFor iidx jidxM t
  ClauseLetClause (anVal -> LetClause (anVal -> ident) le) -> do
    idIdx <- textToTextIndex ident
    lt <- evalExpr le
    return $ ComprehArgLet idIdx lt
  _ -> throwFatal $ printf "invalid clause: %s" (show c)

evalFDeclLabels :: [AST.Label] -> AST.Expression -> RM StructElemAdder
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
  mkAdder :: Label -> Tree -> RM StructElemAdder
  mkAdder (anVal -> Label le) val = case anVal le of
    AST.LabelName ln c ->
      let attr = LabelAttr{lbAttrCnstr = cnstrFrom c, lbAttrIsIdent = isVar ln}
       in case ln of
            (toIDentLabel -> Just key) -> do
              keyIdx <- textToTextIndex key
              return $ StaticSAdder keyIdx (staticFieldMker val attr)
            (toDynLabel -> Just se) -> do
              selTree <- evalExpr se
              oid <- allocRMObjID
              return $ DynamicSAdder oid (DynamicField oid attr selTree False val)
            (toSStrLabel -> Just ss) -> do
              rE <- simpleStringLitToStr ss
              case rE of
                Right str -> do
                  strIdx <- textToTextIndex str
                  return $ StaticSAdder strIdx (staticFieldMker val attr)
                Left t -> do
                  oid <- allocRMObjID
                  return $ DynamicSAdder oid (DynamicField oid attr t True val)
            _ -> throwFatal "invalid label"
    AST.LabelPattern pe -> do
      pat <- evalExpr pe
      oid <- allocRMObjID
      return (CnstrSAdder oid pat val)

  -- Returns the label name and the whether the label is static.
  toIDentLabel :: LabelName -> Maybe T.Text
  toIDentLabel (anVal -> LabelID (anVal -> ident)) = Just ident
  toIDentLabel _ = Nothing

  toDynLabel :: LabelName -> Maybe AST.Expression
  toDynLabel (anVal -> LabelNameExpr lne) = Just lne
  toDynLabel _ = Nothing

  toSStrLabel :: LabelName -> Maybe AST.SimpleStringLit
  toSStrLabel (anVal -> LabelString ls) = Just ls
  toSStrLabel _ = Nothing

  cnstrFrom :: AST.LabelConstraint -> StructFieldCnstr
  cnstrFrom c = case c of
    RegularLabel -> SFCRegular
    OptionalLabel -> SFCOptional
    RequiredLabel -> SFCRequired

  isVar :: LabelName -> Bool
  isVar (anVal -> LabelID _) = True
  -- Labels which are quoted or expressions are not variables.
  isVar _ = False

data StructElemAdder
  = StaticSAdder TextIndex Field
  | DynamicSAdder !Int DynamicField
  | CnstrSAdder !Int Tree Tree
  | LetSAdder TextIndex Tree
  | EmbedSAdder Tree
  | EmptyAdder

{- | Insert a new element into the struct.

If the field is already in the struct, then unify the field with the new field.
-}
insertElemToStruct :: StructElemAdder -> Struct -> RM Tree
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
                  { ssfValue = mkMutableTree (mkUnifyOp [ssfValue extSF, ssfValue sf])
                  , ssfAttr = mergeAttrs (ssfAttr extSF) (ssfAttr sf)
                  , ssfObjects = Set.empty
                  }
              newStruct = updateStubAndField name unifySFOp struct
             in
              return $ mkStructTree newStruct
          [StructStubLet _] -> do
            return $ aliasErr nameStr
          -- The label is not seen before in the struct.
          [] -> return $ mkStructTree $ insertNewStubAndField name sf struct
          _ -> return $ aliasErr nameStr
      )
      return
      (existCheck name nameStr False)
  (DynamicSAdder i dsf) -> return . mkStructTree $ insertStructNewDynField i dsf struct
  (CnstrSAdder i pattern val) -> return . mkStructTree $ insertStructNewCnstr i pattern val struct
  (LetSAdder name val) -> do
    -- Use the pure identifier for error messages.
    nameStr <- tshow name
    return $
      fromMaybe
        -- The name is not seen before in the block.
        (mkStructTree $ insertStructLet name val struct)
        (existCheck name nameStr True)
  _ -> return $ mkStructTree struct
 where
  -- In both errors, we show the name so that the name is quoted.
  aliasErr name = mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" (show name)
  lbRedeclErr name = mkBottomTree $ printf "%s redeclared in same scope" (show name)

  -- Checks if name is already in the block. If it is, then return an error message.
  existCheck :: TextIndex -> T.Text -> Bool -> Maybe Tree
  existCheck nameIdx name isNameLet =
    case (lookupStructStubVal nameIdx struct, isNameLet) of
      ([StructStubField f], True)
        | lbAttrIsIdent (ssfAttr f) -> Just $ aliasErr name
      ([StructStubLet _], True) -> Just $ lbRedeclErr name
      ([StructStubLet _], False) -> Just $ aliasErr name
      ([_, _], _) -> Just $ aliasErr name
      _ -> Nothing

evalListLit :: AST.ElementList -> RM Tree
evalListLit (anVal -> AST.EmbeddingList es) = do
  xs <- mapM (evalEmbedding True) es
  return $ mkListTree xs []

evalUnaryExpr :: UnaryExpr -> RM Tree
evalUnaryExpr ue = do
  t <- case anVal ue of
    UnaryExprPrimaryExpr primExpr -> evalPrimExpr primExpr
    UnaryExprUnaryOp op e -> evalUnaryOp op e
  return $ setExpr t (Just (AST.ExprUnaryExpr ue <$ ue))

builtinOpNameTable :: [(String, Tree)]
builtinOpNameTable =
  -- bounds
  map (\b -> (show b, mkBoundsTreeFromList [BdType b])) [minBound :: BdType .. maxBound :: BdType]
    -- built-in function names
    -- We use the function to distinguish the identifier from the string literal.
    ++ builtinMutableTable

evalPrimExpr :: PrimaryExpr -> RM Tree
evalPrimExpr e = case anVal e of
  (PrimExprOperand op) -> case anVal op of
    OpLiteral lit -> evalLiteral lit
    OperandName (anVal -> Identifier (anVal -> ident)) -> case lookup (T.unpack ident) builtinOpNameTable of
      Just v -> return v
      Nothing -> do
        idIdx <- textToTextIndex ident
        return $ mkMutableTree $ withEmptyMutFrame $ Ref $ emptyIdentRef idIdx
    OpExpression expr -> do
      x <- evalExpr expr
      return $ x{isRootOfSubTree = True}
  (PrimExprSelector primExpr sel) -> do
    p <- evalPrimExpr primExpr
    evalSelector e sel p
  (PrimExprIndex primExpr idx) -> do
    p <- evalPrimExpr primExpr
    evalIndex e idx p
  (PrimExprArguments primExpr aes) -> do
    p <- evalPrimExpr primExpr
    args <- mapM evalExpr aes
    replaceFuncArgs p args

-- | Creates a new function tree for the original function with the arguments applied.
replaceFuncArgs :: Tree -> [Tree] -> RM Tree
replaceFuncArgs t args = case t of
  IsRegOp mut fn ->
    return $
      setTValGenEnv
        ( TGenOp $
            setMutOp
              (RegOp $ fn{ropArgs = Seq.fromList args})
              mut
        )
        t
  _ -> throwFatal $ printf "%s is not a Mutable" (show t)

{- | Evaluates the selector.
Parameters:
- pe is the primary expression.
- sel is the segment.
- addr is the addr to the current expression that contains the segment.
For example, { a: b: x.y }
If the field is "y", and the addr is "a.b", expr is "x.y", the structTreeAddr is "x".
-}
evalSelector ::
  PrimaryExpr -> AST.Selector -> Tree -> RM Tree
evalSelector _ astSel oprnd = do
  let f sel = appendSelToRefTree oprnd (mkAtomTree (String sel))
  case anVal astSel of
    IDSelector ident -> return $ f (anVal ident)
    AST.StringSelector s -> do
      rE <- simpleStringLitToStr s
      case rE of
        Left _ -> return $ mkBottomTree $ printf "selector should not have interpolation"
        Right str -> return $ f str

evalIndex ::
  PrimaryExpr -> AST.Index -> Tree -> RM Tree
evalIndex _ (anVal -> AST.Index e) oprnd = do
  sel <- evalExpr e
  return $ appendSelToRefTree oprnd sel

{- | Evaluates the unary operator.

unary operator should only be applied to atoms.
-}
evalUnaryOp :: UnaryOp -> UnaryExpr -> RM Tree
evalUnaryOp op e = do
  t <- evalUnaryExpr e
  let tWithE = setExpr t (Just (AST.ExprUnaryExpr e <$ e))
  return $ mkMutableTree (mkUnaryOp op tWithE)

{- | order of arguments is important for disjunctions.

left is always before right.
-}
evalBinary :: BinaryOp -> Expression -> Expression -> RM Tree
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
evalBinary (anVal -> AST.Disjoin) e1 e2 = evalDisj e1 e2
evalBinary op e1 e2 = do
  lt <- evalExpr e1
  rt <- evalExpr e2
  case op of
    (anVal -> AST.Unify) -> return $ flattenUnify lt rt
    _ -> return $ mkMutableTree (mkBinaryOp op lt rt)

flattenUnify :: Tree -> Tree -> Tree
flattenUnify l r = case getLeftAcc of
  Just acc -> mkMutableTree $ mkUnifyOp (toList acc ++ [r])
  Nothing -> mkMutableTree $ mkUnifyOp [l, r]
 where
  getLeftAcc = case l of
    -- The left tree is an accumulator only if it is a unify op.
    IsTGenOp (MutOp (UOp u)) -> Just (ufConjuncts u)
    _ -> Nothing

evalDisj :: Expression -> Expression -> RM Tree
evalDisj e1 e2 = do
  ((isLStar, lt), (isRStar, rt)) <- case (anVal e1, anVal e2) of
    ( ExprUnaryExpr (anVal -> UnaryExprUnaryOp (anVal -> Star) se1)
      , ExprUnaryExpr (anVal -> UnaryExprUnaryOp (anVal -> Star) se2)
      ) -> do
        l <- evalUnaryExpr se1
        r <- evalUnaryExpr se2
        return ((,) True l, (,) True r)
    (ExprUnaryExpr (anVal -> UnaryExprUnaryOp (anVal -> Star) se1), _) -> do
      l <- evalUnaryExpr se1
      r <- evalExpr e2
      return ((,) True l, (,) False r)
    (_, ExprUnaryExpr (anVal -> UnaryExprUnaryOp (anVal -> Star) se2)) -> do
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
flattenDisj :: DisjTerm -> DisjTerm -> Tree
flattenDisj l r = case getLeftAcc of
  Just acc -> mkMutableTree $ mkDisjoinOp (acc Seq.|> r)
  Nothing -> mkMutableTree $ mkDisjoinOp (Seq.fromList [l, r])
 where
  getLeftAcc = case dstValue l of
    IsTGenOp (MutOp (DisjOp dj))
      -- The left term is an accumulator only if it is a disjoin op and not marked nor the root.
      -- If the left term is a marked term, it implies that it is a root.
      | not (dstMarked l) && not (isRootOfSubTree (dstValue l)) -> Just (djoTerms dj)
    _ -> Nothing
