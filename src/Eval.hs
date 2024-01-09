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
initState = Context [TopSelector] (emptyStruct, []) Map.empty

eval :: (MonadError String m) => Expression -> m Value
eval expr = fst <$> runStateT (eval' expr) initState

eval' :: (MonadError String m, MonadState Context m) => Expression -> m Value
eval' (UnaryExprCons e)       = evalUnaryExpr e
eval' (BinaryOpCons op e1 e2) = evalBinary op e1 e2

evalLiteral :: (MonadError String m, MonadState Context m) => Literal -> m Value
evalLiteral = f
  where
    f (StringLit (SimpleStringLit s)) = return $ String s
    f (IntLit i)                      = return $ Int i
    f (BoolLit b)                     = return $ Bool b
    f TopLit                          = return Top
    f BottomLit                       = return $ Bottom ""
    f NullLit                         = return Null
    f (StructLit s)                   = evalStructLit s

evalStructLit :: (MonadError String m, MonadState Context m) => [(Label, Expression)] -> m Value
evalStructLit s =
  let orderedKeys = map evalLabel s
      (filteredKeys, _) =
        foldr
          (\k (l, set) -> if Set.notMember k set then (k : l, Set.insert k set) else (l, set))
          ([], Set.empty)
          orderedKeys
      fieldsStub = foldr (\k acc -> Map.insert k Unevaluated acc) Map.empty filteredKeys
      idSet = Set.fromList (getVarLabels s)
      structStub = Struct (StructValue filteredKeys fieldsStub idSet)
   in do
        ctx@(Context path' cblock _) <- get
        -- create a new block since we are entering a new struct.
        let newBlock = addSubTree (last path') structStub cblock
        put $ ctx {curBlock = newBlock}

        evaled <-
          mapM evalField (zipWith (\name (_, e) -> (name, e)) orderedKeys s)
            >>= unifySameFields

        let newStruct = Struct (StructValue filteredKeys evaled idSet)
        let newBlock' = attach newStruct newBlock
        -- restore the current block.
        modify (\ctx' -> ctx' {curBlock = newBlock'})

        tryEvalPendings

        (Context _ (blockVal, _) _) <- get

        return blockVal
  where
    evalLabel (Label (LabelName ln), _) =
      let name = case ln of
            LabelID ident  -> ident
            LabelString ls -> ls
       in name

    evalField (name, e) = do
      -- push the current field to the path.
      modify (\estate -> estate {path = path estate ++ [StringSelector name]})
      v <- eval' e
      -- restore path.
      modify (\estate -> estate {path = init (path estate)})
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

    tryEvalPendings :: (MonadError String m, MonadState Context m) => m ()
    tryEvalPendings = do
      (Context blockPath (blockVal, _) revDeps) <- get
      case trace ("revDeps: " ++ show revDeps) blockVal of
        Struct (StructValue _ fds _) ->
          sequence_ $ Map.mapWithKey (tryEvalPending blockPath) fds
        _ -> return ()
      where
        tryEvalPending :: (MonadError String m, MonadState Context m) => Path -> String -> Value -> m ()
        tryEvalPending blockPath k v = checkEvalPen (blockPath ++ [StringSelector k], v)

evalUnaryExpr :: (MonadError String m, MonadState Context m) => UnaryExpr -> m Value
evalUnaryExpr (PrimaryExprCons (Operand (Literal lit))) = evalLiteral lit
evalUnaryExpr (PrimaryExprCons (Operand (OpExpression expr))) = eval' expr
evalUnaryExpr (PrimaryExprCons (Operand (OperandName (Identifier ident)))) = lookupVar ident
evalUnaryExpr (UnaryOpCons op e) = evalUnaryOp op e

evalUnaryOp :: (MonadError String m, MonadState Context m) => UnaryOp -> UnaryExpr -> m Value
evalUnaryOp op e = do
  val <- evalUnaryExpr e
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
evalBinary :: (MonadError String m, MonadState Context m) => BinaryOp -> Expression -> Expression -> m Value
evalBinary AST.Disjunction e1 e2 = evalDisjunction e1 e2
evalBinary op e1 e2 = do
  v1 <- eval' e1
  v2 <- eval' e2
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
evalDisjunction :: (MonadError String m, MonadState Context m) => Expression -> Expression -> m Value
evalDisjunction e1 e2 = case (e1, e2) of
  (UnaryExprCons (UnaryOpCons Star e1'), UnaryExprCons (UnaryOpCons Star e2')) ->
    evalExprPair (evalUnaryExpr e1') DisjunctDefault (evalUnaryExpr e2') DisjunctDefault
  (UnaryExprCons (UnaryOpCons Star e1'), _) ->
    evalExprPair (evalUnaryExpr e1') DisjunctDefault (eval' e2) DisjunctRegular
  (_, UnaryExprCons (UnaryOpCons Star e2')) ->
    evalExprPair (eval' e1) DisjunctRegular (evalUnaryExpr e2') DisjunctDefault
  (_, _) -> evalExprPair (eval' e1) DisjunctRegular (eval' e2) DisjunctRegular
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
lookupVar :: (MonadError String m, MonadState Context m) => String -> m Value
lookupVar name = do
  Context curPath block revDeps <- get
  case searchUp name block of
    -- TODO: currently we should only look up the current block.
    Just Unevaluated ->
      let depPath = init curPath ++ [StringSelector name]
       in do
            modify (\estate -> estate {reverseDeps = Map.insert depPath curPath revDeps})
            return $ newPending curPath depPath
    Just v -> return v
    Nothing ->
      throwError $
        name
          ++ " is not found"
          ++ ", path: "
          ++ show curPath
          ++ ", block: "
          ++ show (snd block)
