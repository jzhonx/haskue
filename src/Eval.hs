{-# LANGUAGE FlexibleContexts #-}

module Eval where

import           AST
import           Control.Monad.Except (MonadError, liftEither, throwError)
import           Control.Monad.State  (MonadState, get, modify, put, runStateT)
import qualified Data.Map.Strict      as Map
import           Data.Maybe           (fromJust, isJust)
import qualified Data.Set             as Set
import           Debug.Trace
import           Unify                (unify)
import           Value

type FlatValue = Map.Map Path Value

data EvalState = EvalState
  { -- path is the path to the current expression.
    -- the path should be the full path.
    path      :: Path,
    -- curBlock is the current block that contains the variables.
    -- A new block will replace the current one when a new block is entered.
    -- A new block is entered when one of the following is encountered:
    -- - The "{" token
    -- - for and let clauses
    curBlockZ :: Zipper,
    store     :: FlatValue
  }

initState :: EvalState
initState = EvalState [StringSelector "."] (Top, []) Map.empty

eval :: (MonadError String m) => Expression -> m Value
eval expr = fst <$> runStateT (eval' expr) initState

eval' :: (MonadError String m, MonadState EvalState m) => Expression -> m Value
eval' (UnaryExprCons e)       = evalUnaryExpr e
eval' (BinaryOpCons op e1 e2) = evalBinary op e1 e2

evalLiteral :: (MonadError String m, MonadState EvalState m) => Literal -> m Value
evalLiteral = f
  where
    f (StringLit (SimpleStringLit s)) = return $ String s
    f (IntLit i)                      = return $ Int i
    f (BoolLit b)                     = return $ Bool b
    f TopLit                          = return Top
    f BottomLit                       = return $ Bottom ""
    f NullLit                         = return Null
    f (StructLit s)                   = evalStructLit s

evalStructLit :: (MonadError String m, MonadState EvalState m) => [(Label, Expression)] -> m Value
evalStructLit s =
  let orderedKeys = map evalLabel s
      (filteredKeys, _) =
        foldr
          (\k (l, set) -> if Set.notMember k set then (k : l, Set.insert k set) else (l, set))
          ([], Set.empty)
          orderedKeys
      emptyStructValue = Struct filteredKeys Map.empty Set.empty
      identifiers' = Set.fromList (getVarLabels s)
   in do
        estate@(EvalState path' cblock oldStore) <- get
        -- create a new block since we are entering a new struct.
        let curBlock = addSubZipper (last path') emptyStructValue cblock
        let newStore = foldr (\k acc -> Map.insert (path' ++ [StringSelector k]) Unevaluated acc) oldStore filteredKeys
        put $ estate {curBlockZ = curBlock, store = newStore}

        fields' <- mapM evalField (zipWith (\name (_, e) -> (name, e)) orderedKeys s)
        unified <- buildFieldsMap fields'

        evaled <- evalPendings unified

        let newStruct = Struct filteredKeys Map.empty identifiers'
        let newBlock' = attach newStruct curBlock
        -- restore the current block.
        put $ estate {curBlockZ = trace ("put new block" ++ show newBlock' ++ show path') newBlock'}
        return newStruct
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
      -- pop the current field from the path.
      modify (\estate -> estate {path = init (path estate)})
      return (name, v)

    -- buildFieldsMap is used to build a map from the field names to the values.
    buildFieldsMap :: (MonadError String m, MonadState EvalState m) => [(String, Value)] -> m (Map.Map String Value)
    buildFieldsMap fields' = sequence $ Map.fromListWith (\mx my -> do x <- mx; y <- my; unifySameKeys x y) fieldsM
      where
        fieldsM = (map (\(k, v) -> (k, return v)) fields')

        unifySameKeys :: (MonadError String m, MonadState EvalState m) => Value -> Value -> m Value
        unifySameKeys (Pending d ev) (Pending d' ev') = undefined
        unifySameKeys (Pending d ev) v                = undefined
        unifySameKeys v1 v2                           = liftEither $ unify v1 v2

    fetchVarLabel :: Label -> Maybe String
    fetchVarLabel (Label (LabelName (LabelID var))) = Just var
    fetchVarLabel _                                 = Nothing

    getVarLabels :: [(Label, Expression)] -> [String]
    getVarLabels xs = map (\(l, _) -> fromJust (fetchVarLabel l)) (filter (\(l, _) -> isJust (fetchVarLabel l)) xs)

    evalPending :: (MonadError String m, MonadState EvalState m) => Map.Map String Value -> String -> Value -> m Value
    evalPending mx _ p@(Pending [dep] evalf) = do
      EvalState path' _ _ <- get
      case relPath (snd dep) path' of
        [] -> throwError "evalPending: empty path"
        -- the var is defined in the current block.
        [StringSelector localVar] -> case Map.lookup localVar mx of
          Just v  -> liftEither $ evalf [v]
          Nothing -> throwError $ localVar ++ "is not defined"
        -- the var is defined in the parent block.
        _ -> return p
    evalPending _ _ (Pending _ _) = throwError "evalPending: TODO"
    evalPending _ _ v = return v

    -- TODO:
    evalPendings :: (MonadError String m, MonadState EvalState m) => Map.Map String Value -> m (Map.Map String Value)
    evalPendings mx = sequence $ Map.mapWithKey (evalPending mx) mx

evalUnaryExpr :: (MonadError String m, MonadState EvalState m) => UnaryExpr -> m Value
evalUnaryExpr (PrimaryExprCons (Operand (Literal lit))) = evalLiteral lit
evalUnaryExpr (PrimaryExprCons (Operand (OpExpression expr))) = eval' expr
evalUnaryExpr (PrimaryExprCons (Operand (OperandName (Identifier ident)))) = lookupVar ident
evalUnaryExpr (UnaryOpCons op e) = evalUnaryOp op e

evalUnaryOp :: (MonadError String m, MonadState EvalState m) => UnaryOp -> UnaryExpr -> m Value
evalUnaryOp op e = do
  val <- evalUnaryExpr e
  f val
  where
    f v@(Pending {}) = chainPending (\x _ -> conEval op x) v Top
    f v              = liftEither $ conEval op v
    -- conEval evaluates non-pending operands.
    conEval :: UnaryOp -> Value -> EvalMonad Value
    conEval Plus (Int i)  = return $ Int i
    conEval Minus (Int i) = return $ Int (-i)
    conEval Not (Bool b)  = return $ Bool (not b)
    conEval _ _           = throwError "conEval: unsupported unary operator"

-- order of arguments is important for disjunctions.
-- left is always before right.
evalBinary :: (MonadError String m, MonadState EvalState m) => BinaryOp -> Expression -> Expression -> m Value
evalBinary AST.Disjunction e1 e2 = evalDisjunction e1 e2
evalBinary op e1 e2 = do
  v1 <- eval' e1
  v2 <- eval' e2
  binOp v1 v2
  where
    intf :: (MonadError String m) => (Integer -> Integer -> Integer) -> Value -> Value -> m Value
    intf f = evalBinVals f'
      where
        f' (Int i1) (Int i2) = return $ Int (f i1 i2)
        f' _ _               = throwError "intf: unsupported binary operator"

    binOp :: (MonadError String m) => Value -> Value -> m Value
    binOp
      | op == Unify = evalBinVals unify
      | op == Add = intf (+)
      | op == Sub = intf (-)
      | op == Mul = intf (*)
      | op == Div = intf div
      | otherwise = \_ _ -> throwError "binOp: unsupported binary operator"

evalBinVals :: (MonadError String m) => (Value -> Value -> EvalMonad Value) -> Value -> Value -> m Value
evalBinVals bin li v2@(Pending {}) = chainPending (evalBinVals bin) li v2
evalBinVals bin v1@(Pending {}) ri = chainPending (evalBinVals bin) v1 ri
evalBinVals bin v1 v2              = liftEither $ bin v1 v2

chainPending ::
  (MonadError String m) => (Value -> Value -> EvalMonad Value) -> Value -> Value -> m Value
chainPending bin (Pending d1 ef1) v2 =
  return $
    Pending
      d1
      ( \vs -> do
          v1 <- ef1 vs
          bin v1 v2
      )
chainPending bin v1 (Pending d2 ef2) = chainPending (flip bin) (Pending d2 ef2) v1
chainPending _ _ _ = throwError "chainPending: values are not pending"

data DisjunctItem = DisjunctDefault Value | DisjunctRegular Value

-- evalDisjunction is used to evaluate a disjunction.
evalDisjunction :: (MonadError String m, MonadState EvalState m) => Expression -> Expression -> m Value
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
    evalExprPair :: (MonadError String m, MonadState EvalState m) => m Value -> (Value -> DisjunctItem) -> m Value -> (Value -> DisjunctItem) -> m Value
    evalExprPair m1 cons1 m2 cons2 = do
      v1 <- m1
      v2 <- m2
      evalDisjPair (cons1 v1) (cons2 v2)

    -- evalDisjPair is used to evaluate a disjunction whose both sides are evaluated.
    evalDisjPair :: (MonadError String m, MonadState EvalState m) => DisjunctItem -> DisjunctItem -> m Value
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
lookupVar :: (MonadError String m, MonadState EvalState m) => String -> m Value
lookupVar name = do
  EvalState path' block _ <- get
  case searchUp name block of
    -- TODO: currently we should only look up the current block.
    Just Unevaluated -> return $ Pending [(path', init path' ++ [StringSelector name])] (return . head)
    Just v -> return v
    Nothing ->
      throwError $
        name
          ++ " is not found"
          ++ ", path: "
          ++ show path'
          ++ ", block: "
          ++ show (snd block)
