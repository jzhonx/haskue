{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

module Eval where

import           AST
import           Control.Monad.Except (MonadError, throwError)
import           Control.Monad.State  (MonadState, get, modify, put, runStateT)
import qualified Data.Map.Strict      as Map
import           Data.Maybe           (fromJust, isJust)
import qualified Data.Set             as Set
import           Debug.Trace
import           Unify                (unify)
import           Value

initState :: Context
initState = Context (emptyStruct, []) Map.empty

eval :: (MonadError String m) => Expression -> Path -> m Value
eval expr path = fst <$> runStateT (doEval expr path) initState

doEval :: (MonadError String m, MonadState Context m) => Expression -> Path -> m Value
doEval (UnaryExprCons e)       = evalUnaryExpr e
doEval (BinaryOpCons op e1 e2) = evalBinary op e1 e2

evalLiteral :: (MonadError String m, MonadState Context m) => Literal -> Path -> m Value
evalLiteral = f
  where
    f :: (MonadError String m, MonadState Context m) => Literal -> Path -> m Value
    f (StringLit (SimpleStringLit s)) _ = return $ String s
    f (IntLit i) _                      = return $ Int i
    f (BoolLit b) _                     = return $ Bool b
    f TopLit _                          = return Top
    f BottomLit _                       = return $ Bottom ""
    f NullLit _                         = return Null
    f (StructLit s) path                = evalStructLit s path

evalStructLit :: (MonadError String m, MonadState Context m) => [(Label, Expression)] -> Path -> m Value
evalStructLit s path =
  let orderedKeys = map evalLabel s
      (filteredKeys, _) =
        foldr
          (\k (l, set) -> if Set.notMember k set then (k : l, Set.insert k set) else (l, set))
          ([], Set.empty)
          orderedKeys
      fieldsStub = foldr (\k acc -> Map.insert k Unevaluated acc) Map.empty filteredKeys
      idSet = Set.fromList (getVarLabels s)
      structStub = StructValue filteredKeys fieldsStub idSet
   in do
        -- create a new block since we are entering a new struct.
        enterNewBlock structStub path

        evaled <-
          mapM evalField (zipWith (\name (_, e) -> (name, e)) orderedKeys s)
            >>= unifySameFields

        let newStructVal = StructValue filteredKeys evaled idSet
        -- restore the current block.
        modify (\ctx -> ctx {ctxCurBlock = attach newStructVal (ctxCurBlock ctx)})

        tryEvalPendings path

        (Context (block, _) _) <- get

        return $ Struct block
  where
    evalLabel (Label (LabelName ln), _) =
      let name = case ln of
            LabelID ident  -> ident
            LabelString ls -> ls
       in name

    evalField (name, e) = do
      v <- doEval e $ path ++ [StringSelector name]
      return (name, v)

    -- unifySameFields is used to build a map from the field names to the values.
    unifySameFields :: (MonadError String m, MonadState Context m) => [(String, Value)] -> m (Map.Map String Value)
    unifySameFields fds = sequence $ Map.fromListWith (\mx my -> do x <- mx; y <- my; u x y) fieldsM
      where
        fieldsM = (map (\(k, v) -> (k, return v)) fds)

        u :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
        u = binFunc unify

    fetchVarLabel :: Label -> Maybe String
    fetchVarLabel (Label (LabelName (LabelID var))) = Just var
    fetchVarLabel _                                 = Nothing

    getVarLabels :: [(Label, Expression)] -> [String]
    getVarLabels xs = map (\(l, _) -> fromJust (fetchVarLabel l)) (filter (\(l, _) -> isJust (fetchVarLabel l)) xs)

-- evalPending :: (MonadError String m, MonadState Context m) => Map.Map String Value -> String -> Value -> m Value
-- evalPending mx _ p@(Pending [dep] evalf) = do
--   Context curPath _ _ <- get
--   case relPath (snd dep) curPath of
--     [] -> throwError "evalPending: empty path"
--     -- the var is defined in the current block.
--     [StringSelector localVar] -> case Map.lookup localVar mx of
--       Just v  -> evalf [(snd dep, v)]
--       Nothing -> throwError $ localVar ++ "is not defined"
--     -- the var is defined in the parent block.
--     _ -> return p
-- evalPending _ _ (Pending _ _) = throwError "evalPending: TODO"
-- evalPending _ _ v = return v
--
-- -- TODO:
-- evalPendings :: (MonadError String m, MonadState Context m) => Map.Map String Value -> m (Map.Map String Value)
-- evalPendings mx = sequence $ Map.mapWithKey (evalPending mx) mx

tryEvalPendings :: (MonadError String m, MonadState Context m) => Path -> m ()
tryEvalPendings path = do
  (Context (StructValue _ fds _, _) _) <- get
  sequence_ $ Map.mapWithKey tryEvalPending fds
  where
    tryEvalPending :: (MonadError String m, MonadState Context m) => String -> Value -> m ()
    tryEvalPending k v = checkEvalPen (path ++ [StringSelector k], v)

enterNewBlock :: (MonadError String m, MonadState Context m) => StructValue -> Path -> m ()
enterNewBlock structStub path = do
  ctx@(Context block _) <- get
  let blockName = case last path of
        StringSelector name -> name
        _                   -> error "block does not have a string name"
  let newBlock = addSubBlock blockName structStub block
  put $ ctx {ctxCurBlock = newBlock}

evalUnaryExpr :: (MonadError String m, MonadState Context m) => UnaryExpr -> Path -> m Value
evalUnaryExpr (PrimaryExprCons (Operand (Literal lit))) = evalLiteral lit
evalUnaryExpr (PrimaryExprCons (Operand (OpExpression expr))) = doEval expr
evalUnaryExpr (PrimaryExprCons (Operand (OperandName (Identifier ident)))) = lookupVar ident
evalUnaryExpr (UnaryOpCons op e) = evalUnaryOp op e

evalUnaryOp :: (MonadError String m, MonadState Context m) => UnaryOp -> UnaryExpr -> Path -> m Value
evalUnaryOp op e path = do
  val <- evalUnaryExpr e path
  f val
  where
    f v@(Pending {}) = unaFunc (conEval op) v
    f v              = conEval op v
    -- conEval evaluates non-pending operands.
    conEval :: (MonadError String m, MonadState Context m) => UnaryOp -> Value -> m Value
    conEval Plus (Int i)  = return $ Int i
    conEval Minus (Int i) = return $ Int (-i)
    conEval Not (Bool b)  = return $ Bool (not b)
    conEval _ _           = throwError "conEval: unsupported unary operator"

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (MonadError String m, MonadState Context m) => BinaryOp -> Expression -> Expression -> Path -> m Value
evalBinary AST.Disjunction e1 e2 path = evalDisjunction e1 e2 path
evalBinary op e1 e2 path = do
  v1 <- doEval e1 path
  v2 <- doEval e2 path
  binOp v1 v2
  where
    intf :: (MonadError String m, MonadState Context m) => (Integer -> Integer -> Integer) -> Value -> Value -> m Value
    intf f = binFunc g
      where
        g :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
        g (Int i1) (Int i2) = return $ Int (f i1 i2)
        g v1 v2 = throwError $ "intf: unsupported binary operator for values: " ++ show v1 ++ ", " ++ show v2

    binOp :: (MonadError String m, MonadState Context m) => Value -> Value -> m Value
    binOp
      | op == Unify = binFunc unify
      | op == Add = intf (+)
      | op == Sub = intf (-)
      | op == Mul = intf (*)
      | op == Div = intf div
      | otherwise = \_ _ -> throwError $ "binOp: unsupported binary operator: " ++ show op

data DisjunctItem = DisjunctDefault Value | DisjunctRegular Value

-- evalDisjunction is used to evaluate a disjunction.
evalDisjunction :: (MonadError String m, MonadState Context m) => Expression -> Expression -> Path -> m Value
evalDisjunction e1 e2 path = case (e1, e2) of
  (UnaryExprCons (UnaryOpCons Star e1'), UnaryExprCons (UnaryOpCons Star e2')) ->
    evalExprPair (evalUnaryExpr e1' path) DisjunctDefault (evalUnaryExpr e2' path) DisjunctDefault
  (UnaryExprCons (UnaryOpCons Star e1'), _) ->
    evalExprPair (evalUnaryExpr e1' path) DisjunctDefault (doEval e2 path) DisjunctRegular
  (_, UnaryExprCons (UnaryOpCons Star e2')) ->
    evalExprPair (doEval e1 path) DisjunctRegular (evalUnaryExpr e2' path) DisjunctDefault
  (_, _) -> evalExprPair (doEval e1 path) DisjunctRegular (doEval e2 path) DisjunctRegular
  where
    -- evalExprPair is used to evaluate a disjunction with both sides still being unevaluated.
    evalExprPair :: (MonadError String m, MonadState Context m) => m Value -> (Value -> DisjunctItem) -> m Value -> (Value -> DisjunctItem) -> m Value
    evalExprPair m1 cons1 m2 cons2 = do
      v1 <- m1
      v2 <- m2
      evalDisjPair (cons1 v1) (cons2 v2)

    -- evalDisjPair is used to evaluate a disjunction whose both sides are evaluated.
    evalDisjPair :: (MonadError String m, MonadState Context m) => DisjunctItem -> DisjunctItem -> m Value
    evalDisjPair (DisjunctDefault v1) r2 =
      evalLeftPartial (\(df1, ds1, df2, ds2) -> newDisj df1 ds1 df2 ds2) v1 r2
    -- reverse v2 r1 and also the order to the disjCons.
    evalDisjPair r1@(DisjunctRegular _) (DisjunctDefault v2) =
      evalLeftPartial (\(df2, ds2, df1, ds1) -> newDisj df1 ds1 df2 ds2) v2 r1
    evalDisjPair (DisjunctRegular v1) (DisjunctRegular v2) = evalRegularDisj v1 v2

    -- evalLeftPartial is used to evaluate a disjunction whose left side is a default.
    -- the first argument is a function that takes the four lists of values and returns a disjunction.
    evalLeftPartial :: (MonadError String m) => (([Value], [Value], [Value], [Value]) -> m Value) -> Value -> DisjunctItem -> m Value
    evalLeftPartial disjCons (Value.Disjunction df1 ds1) (DisjunctRegular (Value.Disjunction _ ds2)) =
      -- This is rule M2 and M3. We eliminate the defaults from the right side.
      disjCons (df1, ds1, [], ds2)
    evalLeftPartial disjCons v1 (DisjunctRegular (Value.Disjunction df2 ds2)) =
      -- This is rule M1.
      disjCons ([v1], [v1], df2, ds2)
    evalLeftPartial disjCons v1 (DisjunctRegular v2) =
      disjCons ([v1], [v1], [], [v2])
    evalLeftPartial disjCons v1 (DisjunctDefault v2) =
      disjCons ([], [v1], [], [v2])

    -- evalFullDisj is used to evaluate a disjunction whose both sides are regular.
    -- Rule: D1, D2
    evalRegularDisj (Value.Disjunction df1 ds1) (Value.Disjunction df2 ds2) = newDisj df1 ds1 df2 ds2
    evalRegularDisj (Value.Disjunction d ds) y = newDisj d ds [] [y]
    evalRegularDisj x (Value.Disjunction d ds) = newDisj [] [x] d ds
    -- Rule D0
    evalRegularDisj x y = newDisj [] [x] [] [y]

    -- dedupAppend appends unique elements in ys to the xs list, but only if they are not already in xs.
    -- xs and ys are guaranteed to be unique.
    dedupAppend :: [Value] -> [Value] -> [Value]
    dedupAppend xs ys = xs ++ foldr (\y acc -> if y `elem` xs then acc else y : acc) [] ys

    newDisj df1 ds1 df2 ds2 = return $ Value.Disjunction (dedupAppend df1 df2) (dedupAppend ds1 ds2)

-- lookupVar looks up the variable denoted by the name.
lookupVar :: (MonadError String m, MonadState Context m) => String -> Path -> m Value
lookupVar name path = do
  Context block revDeps <- get
  case searchVarUp name block of
    -- TODO: currently we should only look up the current block.
    Just Unevaluated ->
      let depPath = init path ++ [StringSelector name]
       in do
            modify (\ctx -> ctx {ctxReverseDeps = Map.insert depPath path revDeps})
            return $ newPending path depPath
    Just v -> return v
    Nothing ->
      throwError $
        name
          ++ " is not found"
          ++ ", path: "
          ++ show path
          ++ ", block: "
          ++ show (snd block)
