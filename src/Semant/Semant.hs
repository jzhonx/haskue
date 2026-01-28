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
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import Debug.Trace (trace)
import Feature (modifyTISuffix)
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import StringIndex (HasTextIndexer (..), ShowWTIndexer (..), TextIndex, TextIndexer, bsToTextIndex, textToTextIndex)
import Syntax.AST
import qualified Syntax.AST as AST
import Syntax.Token (
  Location,
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

transSourceFile :: SourceFile -> TM Val
transSourceFile (SourceFile decls) = transStructLit (StructLit emptyLoc decls emptyLoc)

{- | transExpr and all trans* should return the same level tree cursor.

The label and the translated result of the expression will be added to the input tree cursor, making the tree one
level deeper with the label as the key.
Every trans* function should return a tree cursor that is at the same level as the input tree cursor.
For example, if the addr of the input tree is {a: b: {}} with cursor pointing to the {}, and label being c, the output
tree should be { a: b: {c: 42} }, with the cursor pointing to the {c: 42}.
-}
transExpr :: Expression -> TM Val
transExpr e = do
  t <- case e of
    (Unary ue) -> transUnaryExpr ue
    (Binary op e1 e2) -> transBinary op.tkType e1 e2
  return $ setExpr (Just e) t

transLiteral :: Literal -> TM Val
transLiteral (LitStruct s) = transStructLit s
transLiteral (LitList (ListLit _ l _)) = transListLit l
transLiteral (LitBasic a)
  | (StringLit (SimpleStringL (SimpleStringLit _ segs))) <- a = segsToStrAtom segs
  | (StringLit (MultiLineStringL (MultiLineStringLit _ segs))) <- a = segsToStrAtom segs
 where
  segsToStrAtom segs = do
    rE <- strLitSegsToStr segs
    return $ case rE of
      Left t -> t
      Right str -> mkAtomVal $ String str
transLiteral (LitBasic a) = case a of
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

transStructLit :: StructLit -> TM Val
transStructLit (StructLit _ decls _) = inStructScope decls $ do
  sid <- getEnvID
  elems <- mapM transDecl decls
  res <-
    foldM
      ( \acc elm -> case acc of
          IsStruct struct -> mkStructVal <$> insertElemToStruct elm struct
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

strLitSegsToStr :: [StringLitSeg] -> TM (Either Val T.Text)
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
            t <- transExpr e
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
transDecl :: Declaration -> TM StructElemAdder
transDecl decl = case decl of
  Embedding ed -> do
    v <- transEmbedding False ed
    return $ EmbedSAdder v
  EllipsisDecl (Ellipsis _ cM) ->
    maybe
      (return EmptyAdder) -- TODO: implement real ellipsis handling
      (\_ -> throwFatal "default constraints are not implemented yet")
      cM
  FieldDecl (AST.Field ls e) ->
    transFDeclLabels ls e
  DeclLet (LetClause _ ident binde) -> do
    idIdx <- identTokenToTextIndex ident
    val <- transExpr binde
    envid <- getEnvID
    idIdxUpdated <- modifyTISuffix envid idIdx
    return $ LetSAdder idIdxUpdated val

identTokenToTextIndex :: Token -> TM TextIndex
identTokenToTextIndex tk = case tk.tkType of
  Token.Identifier -> bsToTextIndex tk.tkLiteral
  _ -> throwFatal $ printf "expected identifier token, got %s" (show tk)

transEmbedding :: Bool -> Embedding -> TM Val
transEmbedding _ (AliasExpr e) = transExpr e
transEmbedding
  isListCompreh
  (EmbedComprehension (AST.Comprehension (Clauses (GuardClause _ ge) cls) lit)) = do
    clsvE <- mapM transClause cls
    case sequence clsvE of
      Left errVal -> return errVal
      Right clsv -> do
        gev <- transExpr ge
        sv <- transStructLit lit
        return $
          mkMutableVal $
            withEmptyOpFrame $
              Compreh $
                mkComprehension isListCompreh (ComprehArgIf gev : clsv) sv
transEmbedding
  isListCompreh
  (EmbedComprehension (AST.Comprehension (Clauses (ForClause _ i jM fe) cls) lit)) = do
    iIdx <- identTokenToTextIndex i
    jIdxM <- case jM of
      Just j -> Just <$> identTokenToTextIndex j
      Nothing -> return Nothing
    res <- inClauseScope iIdx jIdxM $ do
      -- EnvID must be fetched early because transClause does not pop child envs.
      cid <- getEnvID
      clsvE <- mapM transClause cls
      case sequence clsvE of
        Left errVal -> return errVal
        Right clsv -> do
          fev <- transExpr fe
          iIdxUpdated <- modifyTISuffix cid iIdx
          jIdxMUpdated <- case jIdxM of
            Just jIdx -> Just <$> modifyTISuffix cid jIdx
            Nothing -> return Nothing
          let vs = ComprehArgFor iIdxUpdated jIdxMUpdated fev : clsv
          sv <- transStructLit lit
          return $ mkMutableVal $ withEmptyOpFrame $ Compreh $ mkComprehension isListCompreh vs sv
    case res of
      Left errVal -> return errVal
      Right v -> return v

transClause :: Clause -> TM (Either Val ComprehArg)
transClause c = case c of
  ClauseStart (GuardClause _ e) -> do
    t <- transExpr e
    return $ Right $ ComprehArgIf t
  ClauseStart (ForClause _ i jM e) -> do
    iIdx <- identTokenToTextIndex i
    jIdxM <- case jM of
      Just j -> Just <$> identTokenToTextIndex j
      Nothing -> return Nothing
    inSubClauseScope iIdx jIdxM $ do
      cid <- getEnvID
      t <- transExpr e
      iIdxUpdated <- modifyTISuffix cid iIdx
      jIdxMUpdated <- case jIdxM of
        Just jIdx -> Just <$> modifyTISuffix cid jIdx
        Nothing -> return Nothing
      return $ ComprehArgFor iIdxUpdated jIdxMUpdated t
  ClauseLet (LetClause _ ident le) -> do
    idIdx <- identTokenToTextIndex ident
    inSubClauseScope idIdx Nothing $ do
      cid <- getEnvID
      lt <- transExpr le
      idIdxUpdated <- modifyTISuffix cid idIdx
      return $ ComprehArgLet idIdxUpdated lt

transFDeclLabels :: [Label] -> Expression -> TM StructElemAdder
transFDeclLabels lbls e =
  case lbls of
    [] -> throwFatal "empty labels"
    [l1] ->
      do
        val <- transExpr e
        mkAdder l1 val
    l1 : l2 : rs ->
      do
        sf2 <- transFDeclLabels (l2 : rs) e
        sid <- allocObjID
        val <- insertElemToStruct sf2 (emptyStruct{stcID = sid})
        mkAdder l1 (mkStructVal val)
 where
  mkAdder :: Label -> Val -> TM StructElemAdder
  mkAdder (Label le) val = case le of
    LabelName ln c ->
      let attr = LabelAttr{lbAttrCnstr = cnstrFrom c, lbAttrIsIdent = isVar ln}
       in case ln of
            (toIDentLabel -> Just key) -> do
              keyIdx <- identTokenToTextIndex key
              return $ StaticSAdder keyIdx (staticFieldMker val attr)
            (toDynLabel -> Just se) -> do
              selTree <- transExpr se
              oid <- allocObjID
              return $ DynamicSAdder oid (DynamicField oid attr selTree False val)
            (toSStrLabel -> Just (SimpleStringLit _ segs)) -> do
              rE <- strLitSegsToStr segs
              case rE of
                Right str -> do
                  strIdx <- textToTextIndex str
                  return $ StaticSAdder strIdx (staticFieldMker val attr)
                Left t -> do
                  oid <- allocObjID
                  return $ DynamicSAdder oid (DynamicField oid attr t True val)
            _ -> throwFatal "invalid label"
    LabelExpr _ pe _ -> do
      pat <- transExpr pe
      oid <- allocObjID
      return (CnstrSAdder oid pat val)

  -- Returns the label identifier and the whether the label is static.

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

toIDentLabel :: LabelName -> Maybe Token
toIDentLabel (LabelID ident) = Just ident
toIDentLabel _ = Nothing

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
insertElemToStruct :: StructElemAdder -> Struct -> TM Struct
insertElemToStruct adder struct = case adder of
  (StaticSAdder name sf) -> do
    case lookupStructStubVal name struct of
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
          return newStruct
      -- The label is not seen before in the struct.
      _ -> return $ insertNewStubAndField name sf struct
  (DynamicSAdder i dsf) -> return $ insertStructNewDynField i dsf struct
  (CnstrSAdder i pattern val) -> return $ insertStructNewCnstr i pattern val struct
  (LetSAdder name val) -> return $ insertStructLet name val struct
  _ -> return struct

transListLit :: ElementList -> TM Val
transListLit (EmbeddingList es) = do
  xs <- mapM (transEmbedding True) es
  return $ mkListVal xs []

transUnaryExpr :: UnaryExpr -> TM Val
transUnaryExpr ue = do
  t <- case ue of
    Primary primExpr -> transPrimExpr primExpr
    UnaryOp op e -> transUnaryOp op.tkType e
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

transPrimExpr :: PrimaryExpr -> TM Val
transPrimExpr e = case e of
  (PrimExprOperand op) -> case op of
    OpLiteral lit -> transLiteral lit
    OpName (OperandName ident) -> case lookup (T.unpack (tkLiteralToText ident)) builtinOpNameTable of
      Just v -> return v
      Nothing -> do
        idIdx <- identTokenToTextIndex ident
        res <- lookupIdentInScopes idIdx ident.tkLoc
        case res of
          Left errVal -> return errVal
          Right (inTopScope, identEnvID, identType) -> do
            idIdxUpdated <- case identType of
              ITField -> return idIdx
              _ -> modifyTISuffix identEnvID idIdx
            return $ mkMutableVal $ withEmptyOpFrame $ Ref $ singletonIdentRef idIdxUpdated
    OpExpression _ expr _ -> do
      x <- transExpr expr
      return $ x{isRootOfSubVal = True}
  (PrimExprSelector primExpr _ sel) -> do
    p <- transPrimExpr primExpr
    transSelector e sel p
  (PrimExprIndex primExpr _ idx _) -> do
    p <- transPrimExpr primExpr
    transIndex e idx p
  (PrimExprArguments primExpr _ aes _) -> do
    p <- transPrimExpr primExpr
    args <- mapM transExpr aes
    replaceFuncArgs p args

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
transSelector :: PrimaryExpr -> Selector -> Val -> TM Val
transSelector _ astSel oprnd = do
  let f sel = selectValFromVal oprnd (mkAtomVal (String sel))
  case astSel of
    IDSelector ident -> return $ f (tkLiteralToText ident)
    StringSelector (SimpleStringLit _ segs) -> do
      rE <- strLitSegsToStr segs
      case rE of
        Left _ -> return $ mkBottomVal $ printf "selector should not have interpolation"
        Right str -> return $ f str

transIndex :: PrimaryExpr -> Expression -> Val -> TM Val
transIndex _ e oprnd = do
  sel <- transExpr e
  return $ selectValFromVal oprnd sel

{- | Evaluates the unary operator.

unary operator should only be applied to atoms.
-}
transUnaryOp :: TokenType -> UnaryExpr -> TM Val
transUnaryOp op e = do
  t <- transUnaryExpr e
  let tWithE = setExpr (Just (Unary e)) t
  return $ mkMutableVal (mkUnaryOp op tWithE)

{- | order of arguments is important for disjunctions.

left is always before right.
-}
transBinary :: TokenType -> Expression -> Expression -> TM Val
-- disjunction is a special case because some of the operators can only be valid when used with disjunction.
transBinary Disjoin e1 e2 = transDisj e1 e2
transBinary op e1 e2 = do
  lt <- transExpr e1
  rt <- transExpr e2
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
    IsRegularUnifyOp _ u -> Just u.conjs
    -- If the left tree is an embed unify op, we also treat its whole as an accumulator.
    _ -> Nothing

transDisj :: Expression -> Expression -> TM Val
transDisj e1 e2 = do
  ((isLStar, lt), (isRStar, rt)) <- case (e1, e2) of
    ( Unary (UnaryOp (tkType -> Token.Multiply) se1)
      , Unary (UnaryOp (tkType -> Token.Multiply) se2)
      ) -> do
        l <- transUnaryExpr se1
        r <- transUnaryExpr se2
        return ((,) True l, (,) True r)
    (Unary (UnaryOp (tkType -> Token.Multiply) se1), _) -> do
      l <- transUnaryExpr se1
      r <- transExpr e2
      return ((,) True l, (,) False r)
    (_, Unary (UnaryOp (tkType -> Token.Multiply) se2)) -> do
      l <- transExpr e1
      r <- transUnaryExpr se2
      return ((,) False l, (,) True r)
    (_, _) -> do
      l <- transExpr e1
      r <- transExpr e2
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

data RefIdentType
  = ITField
  | ITLetBinding
  | ITIterBinding
  deriving (Eq, Show)

-- | Lookup the identifier in the scopes. If not found, return an error value.
lookupIdentInScopes :: TextIndex -> Location -> TM (Either Val (Bool, Int, RefIdentType))
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

{- | Lookup the identifier in the environments.

Returns (isInTopEnv, EnvID, identType) if found.
-}
lookupIdentInEnvs :: TextIndex -> TM (Maybe (Bool, Int, RefIdentType))
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
    case Map.lookup name env.names of
      Just (t, _) ->
        ( Just (env.envid == tenvid, env.envid, t)
        , reverse acc ++ markNameAsReferenced name env : rest
        )
      Nothing -> lookupInStack tenvid (env : acc) rest

addNameToCurrentEnv :: TextIndex -> RefIdentType -> TM (Either Val ())
addNameToCurrentEnv ti identType = do
  checked <- checkIdentInEnvs ti identType
  case checked of
    Left errVal -> return $ Left errVal
    Right _ -> do
      modify' $ mapEnvs $ addName ti
      return $ Right ()
 where
  addName name (Environments envs) = case envs of
    [] -> Environments []
    (env : rest) -> Environments $ env{names = Map.insert name (identType, False) env.names} : rest

checkIdentInEnvs :: TextIndex -> RefIdentType -> TM (Either Val ())
checkIdentInEnvs key identType = do
  res <- lookupIdentInEnvs key
  case res of
    Just (isInTopEnv, _, targetIdentType)
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

inStructScope :: [Declaration] -> TM Val -> TM Val
inStructScope decls action = do
  enterRes <- enterStructScope decls
  case enterRes of
    Left errVal -> return errVal
    Right () -> do
      result <- action
      leaveRes <- leaveStructScope
      case leaveRes of
        Left errVal -> return errVal
        Right () -> return result

enterStructScope :: [Declaration] -> TM (Either Val ())
enterStructScope decls = do
  sid <- allocObjID
  modify' $ mapEnvs (pushBlock sid EnvTypeStruct)
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

enterClauseScope :: TextIndex -> Maybe TextIndex -> TM (Either Val ())
enterClauseScope iIdx jIdxM = do
  fid <- allocObjID
  modify' $ mapEnvs (pushBlock fid EnvTypeClause)
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

inClauseScope :: TextIndex -> Maybe TextIndex -> TM a -> TM (Either Val a)
inClauseScope iIdx jIdxM action = do
  enterRes <- enterClauseScope iIdx jIdxM
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
inSubClauseScope :: TextIndex -> Maybe TextIndex -> TM a -> TM (Either Val a)
inSubClauseScope iIdx jIdxM action = do
  enterRes <- enterClauseScope iIdx jIdxM
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

data EnvType = EnvTypeStruct | EnvTypeClause
  deriving (Eq, Show)

data Environment = Environment
  { envid :: !Int
  , envType :: EnvType
  , names :: Map.Map TextIndex (RefIdentType, Bool)
  -- ^ names maps identifiers to
  --  (1) their addresses,
  --  (2) their types (field, let binding, or iter binding),
  --  (3) a boolean indicating whether it is referenced.
  -- Notice the identifiers should not have suffix for let bindings.
  }
  deriving (Eq)

instance Show Environment where
  show (Environment envid typ names) = printf "Env(id=%d, type=%s names=[%s])" envid (show typ) nameStr
   where
    nameStr :: String
    nameStr =
      concatMap
        ( \(k, (t, r)) ->
            printf "%s->(%s,%s,%s); " (show k) (show t) (show r)
        )
        (Map.toList names)

instance ShowWTIndexer Environment where
  tshow (Environment envid typ names) = do
    nameStrs <-
      mapM
        ( \(k, (t, r)) -> do
            kT <- tshow k
            return $ T.pack $ printf "%s->(%s,%s); " (T.unpack kT) (show t) (show r)
        )
        (Map.toList names)
    return $ T.pack $ printf "Env(id=%d, type=%s, names=[%s])" envid (show typ) (T.unpack $ T.concat nameStrs)

emptyEnvironments :: Environments
emptyEnvironments = Environments []

markNameAsReferenced :: TextIndex -> Environment -> Environment
markNameAsReferenced key env = env{names = Map.adjust markRef key env.names}
 where
  markRef (identType, _) = (identType, True)

pushBlock :: Int -> EnvType -> Environments -> Environments
pushBlock envid typ (Environments envs) =
  Environments $ Environment{names = Map.empty, envType = typ, envid = envid} : envs

popBlock :: Environments -> (Environment, Environments)
popBlock (Environments envs) = case envs of
  [] -> error "popBlock: empty environment stack"
  (env : rest) -> (env, Environments rest)
