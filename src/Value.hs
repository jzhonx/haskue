{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Value
  ( Context (..),
    EvalMonad,
    Evaluator,
    Value (..),
    PendingValue (..),
    StructValue (..),
    DelayValidator (..),
    TreeCursor,
    Runtime,
    bindEval,
    delayBinaryOp,
    delayUnaryOp,
    dump,
    emptyStruct,
    getTemp,
    getValueFromCtx,
    goToScope,
    hasConcreteTemp,
    isValueAtom,
    isValueConcrete,
    isValueDep,
    isValuePending,
    isValueUnevaluated,
    mergeArgs,
    mkRef,
    mkReference,
    prettyRevDeps,
    putValueInCtx,
    searchUpVar,
    -- strBld,
    toExpr,
  )
where

import qualified AST
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Logger (MonadLogger, logDebugN)
import Control.Monad.State.Strict (MonadState, get, modify, put)
import Data.ByteString.Builder
  ( Builder,
    char7,
    integerDec,
    string7,
  )
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.Text (pack)
import Path
import Text.Printf (printf)

svFromVal :: Value -> Maybe StructValue
svFromVal (Struct sv) = Just sv
svFromVal _ = Nothing

dump :: (MonadLogger m) => String -> m ()
dump = logDebugN . pack

-- | Context
data Context = Context
  { -- curBlock is the current block that contains the variables.
    -- A new block will replace the current one when a new block is entered.
    -- A new block is entered when one of the following is encountered:
    -- - The "{" token
    -- - for and let clauses
    ctxCurBlock :: TreeCursor,
    ctxReverseDeps :: Map.Map Path Path
  }

prettyRevDeps :: Map.Map Path Path -> String
prettyRevDeps = intercalate ", " . map (\(k, v) -> printf "(%s->%s)" (show k) (show v)) . Map.toList

type Runtime m = (MonadError String m, MonadState Context m, MonadLogger m)

type EvalMonad a = forall m. (Runtime m) => m a

-- | Evaluator is a function that takes a list of tuples values and their paths and returns a value.
type Evaluator = [(Path, Value)] -> EvalMonad Value

data Value
  = Top
  | String String
  | Int Integer
  | Bool Bool
  | Struct StructValue
  | Disjunction
      { defaults :: [Value],
        disjuncts :: [Value]
      }
  | Null
  | Bottom String
  | Pending PendingValue
  | Validator DelayValidator
  | Unevaluated {uePath :: Path}

isValueAtom :: Value -> Bool
isValueAtom (String _) = True
isValueAtom (Int _) = True
isValueAtom (Bool _) = True
isValueAtom Null = True
isValueAtom _ = False

isValueConcrete :: Value -> Bool
isValueConcrete v
  | isValueAtom v = True
isValueConcrete (Struct sv) = Set.size (svConcretes sv) == Map.size (svFields sv)
isValueConcrete (Disjunction dfs _) = not (null dfs)
isValueConcrete _ = False

isValueDep :: Value -> Bool
isValueDep (Pending {}) = True
isValueDep (Unevaluated {}) = True
isValueDep _ = False

isValuePending :: Value -> Bool
isValuePending (Pending _) = True
isValuePending _ = False

hasConcreteTemp :: Value -> Bool
hasConcreteTemp (Pending pv) = isValueConcrete (pvTemp pv)
hasConcreteTemp _ = False

getTemp :: (MonadError String m) => Value -> m Value
getTemp (Pending pv) = return $ pvTemp pv
getTemp _ = throwError "getTemp: value is not pending"

isValueUnevaluated :: Value -> Bool
isValueUnevaluated (Unevaluated {}) = True
isValueUnevaluated _ = False

data StructValue = StructValue
  { svLabels :: [String],
    svFields :: Map.Map String Value,
    svVars :: Set.Set String,
    svConcretes :: Set.Set String
  }

instance Show StructValue where
  show (StructValue ols fds _ concretes) =
    printf
      "{labels: %s, fields: %s, concretes: %s}"
      (show ols)
      (show (Map.toAscList fds))
      (show (Set.toAscList concretes))

-- | For now we don't compare IDs and Concrete fields.
instance Eq StructValue where
  (==) (StructValue ols1 fields1 _ _) (StructValue ols2 fields2 _ _) =
    ols1 == ols2 && fields1 == fields2

-- PendingValue is created by reference and its value can change.
data PendingValue = PendingValue
  { -- pvPath is the path to the pending value.
    pvPath :: Path,
    -- pvDeps is a list of paths to the non-atom values.
    -- path should be the full path.
    -- the element is the path to referenced values.
    -- It should not be shrunk because its size is used to decide whether we can trigger the evaluation.
    pvDeps :: [Path],
    -- pvArgs contains non-pending values.
    pvArgs :: [(Path, Value)],
    -- pvEvaluator is a function that takes a list of values and returns a value.
    -- The order of the values in the list is the same as the order of the paths in deps.
    pvEvaluator :: Evaluator,
    -- pvTemp is the temporary value that is used to store the non-atom result of the evaluation.
    pvTemp :: Value,
    pvExpr :: AST.Expression
  }

instance Show PendingValue where
  show (PendingValue p d a _ t e) =
    printf
      "(P, %s, deps: %s, args: %s, temp: %s, expr: %s)"
      (show p)
      prettyDeps
      (show a)
      (show t)
      (AST.exprStr e)
    where
      prettyDeps = intercalate ", " $ map (\p2 -> printf "(%s->%s)" (show p) (show p2)) d

-- TODO: compare Deps, Args and Temps
instance Eq PendingValue where
  (==) pv1 pv2 = pvPath pv1 == pvPath pv2 && pvTemp pv1 == pvTemp pv2

data DelayValidator = DelayValidator
  { dvPath :: Path,
    dvAtom :: Value,
    dvPend :: PendingValue
  }

instance Show DelayValidator where
  show (DelayValidator p a pv) =
    printf "(DV, %s, atom: %s, pend: %s)" (show p) (show a) (show pv)

instance Eq DelayValidator where
  (==) (DelayValidator p1 a1 pv1) (DelayValidator p2 a2 pv2) = p1 == p2 && a1 == a2 && pv1 == pv2

-- TODO: merge same keys handler
-- two embeded structs can have same keys
-- mergeStructValues :: StructValue -> StructValue -> StructValue
-- mergeStructValues (StructValue ols1 fields1 ids1 atoms1) (StructValue ols2 fields2 ids2 atoms2) =
--   StructValue (ols1 ++ ols2) (Map.union fields1 fields2) (Set.union ids1 ids2) (isAtom1 && isAtom2)

mergeArgs :: [(Path, Value)] -> [(Path, Value)] -> [(Path, Value)]
mergeArgs xs ys = Map.toList $ Map.fromList (xs ++ ys)

-- | Binds the evaluator to a function that uses the value as the argument.
bindEval :: Evaluator -> (Value -> EvalMonad Value) -> Evaluator
bindEval evalf f xs = evalf xs >>= f

-- | Create a reference for a value.
-- Parameters:
--  path is the path to the current expression that contains the selector.
--  expr is the expression that contains the selector.
--  valPath is the path to the referenced value.
--  val is the referenced value.
--  For example,
--  { a: b: x.y, x: y: 42 }
--  Even if the reference is "y", the expr should be "x.y".
mkRef :: Runtime m => (Path, AST.Expression) -> (Path, Value) -> m Value
mkRef _ (_, val)
  | isValueAtom val = return val
mkRef (ePath, expr) (origPath, origVal) = case origVal of
  Unevaluated {} ->
    if origPath == ePath
      then do
        dump $ printf "mkRef: epath: %s, self cycle detected" (show ePath)
        return Top
      else do
        dump $ printf "mkRef: epath: %s, %s is unevaluated" (show ePath) (show origPath)
        createRef (Unevaluated ePath)
  Pending pv -> do
    cycleDetected <- checkCycle (ePath, origPath)
    if cycleDetected
      then do
        dump $
          printf
            "mkRef: epath: %s, cycle detected: %s->%s, making %s temp Top"
            (show ePath)
            (show ePath)
            (show origPath)
            (show origPath)
        return $ mkReference expr ePath origPath Top
      else do
        dump $ printf "mkRef: epath: %s, references another pending value: %s" (show ePath) (show pv)
        createRef (Unevaluated ePath)
  _ -> do
    dump $ printf "mkRef: epath: %s, references regular val: %s" (show ePath) (show origVal)
    createRef origVal
  where
    checkCycle :: Runtime m => (Path, Path) -> m Bool
    checkCycle (src, dst) = do
      Context _ revDeps <- get
      -- we have to reverse the new edge because the graph is reversed.
      return $ depsHasCycle ((dst, src) : Map.toList revDeps)

    -- createRef creates a pending value that depends on the value of the origPath.
    createRef :: Runtime m => Value -> m Value
    createRef orig = do
      modify (\ctx -> ctx {ctxReverseDeps = Map.insert origPath ePath (ctxReverseDeps ctx)})
      -- TODO: fix the expr
      let v = mkReference expr ePath origPath orig
      dump $ printf "mkRef: epath: %s, pending value created: %s" (show ePath) (show v)
      return v

-- | Bind a pending value to a function "f" and generate a new value.
-- For example, { a: b: !x }, or { a: b: x.y.z }.
-- If x is not evaluated or not concrete, the result is pending. For the later case, the expr is the AST of x.y.z.
delayUnaryOp ::
  Runtime m => AST.Expression -> (Value -> EvalMonad Value) -> PendingValue -> m Value
delayUnaryOp expr f pv =
  return . Pending $
    pv
      { pvEvaluator = bindEval (pvEvaluator pv) f,
        pvTemp = Unevaluated (pvPath pv),
        pvExpr = expr
      }

-- | Bind two pending values to a function "bin" and generate a new value.
-- The bin should do the followings:
--  1. return an unevaluated value if any of the value is unevaluated.
--  2. return any value if the two values can be used to generate a value.
--    a. If the value is atom, then the new value is atom.
--    b. Otherwise, the new value is still pending.
-- For example, { a: b: x+y }
-- x and y must have the same path.
-- Or, { a: b: x & y }
-- x and y are not required to be concrete.
delayBinaryOp ::
  Runtime m => AST.BinaryOp -> (Value -> Value -> EvalMonad Value) -> PendingValue -> PendingValue -> m Value
delayBinaryOp op bin pv1 pv2
  | pvPath pv1 == pvPath pv2 =
      return . Pending $
        PendingValue
          (pvPath pv1)
          (mergePaths (pvDeps pv1) (pvDeps pv2))
          (mergeArgs (pvArgs pv1) (pvArgs pv2))
          -- no matter what the newTemp is, evaluator must be updated to reflect the new bin function.
          ( \xs -> do
              v1 <- pvEvaluator pv1 xs
              v2 <- pvEvaluator pv2 xs
              bin v1 v2
          )
          (Unevaluated (pvPath pv1))
          (AST.ExprBinaryOp op (pvExpr pv1) (pvExpr pv2))
  | otherwise =
      throwError $
        printf
          "delayBinaryOp: two pending values have different paths, p1: %s, p2: %s"
          (show (pvPath pv1))
          (show (pvPath pv2))

-- | Creates a new simple reference.
mkReference :: AST.Expression -> Path -> Path -> Value -> Value
mkReference expr src dst temp = Pending $ newReference expr src dst temp

-- | Creates a reference.
newReference :: AST.Expression -> Path -> Path -> Value -> PendingValue
newReference expr src dst temp = PendingValue src [dst] [] f temp expr
  where
    f xs = do
      case lookup dst xs of
        Just v -> return v
        Nothing ->
          throwError $
            printf
              "Pending value can not find its dependent value, path: %s, depPath: %s, args: %s"
              (show src)
              (show dst)
              (show xs)

-- | TreeCrumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type TreeCrumb = (Selector, StructValue)

type TreeCursor = (StructValue, [TreeCrumb])

goUp :: TreeCursor -> Maybe TreeCursor
goUp (_, []) = Nothing
goUp (_, (_, v') : vs) = Just (v', vs)

goDown :: Path -> TreeCursor -> Maybe TreeCursor
goDown (Path sels) = go (reverse sels)
  where
    next :: Selector -> TreeCursor -> Maybe TreeCursor
    next n@(StringSelector name) (sv@(StructValue _ fields _ _), vs) = do
      val <- Map.lookup name fields
      newSv <- svFromVal val
      return (newSv, (n, sv) : vs)

    go :: [Selector] -> TreeCursor -> Maybe TreeCursor
    go [] cursor = Just cursor
    go (x : xs) cursor = do
      nextCur <- next x cursor
      go xs nextCur

attach :: StructValue -> TreeCursor -> TreeCursor
attach sv (_, vs) = (sv, vs)

-- addSubBlock :: Maybe Selector -> StructValue -> TreeCursor -> TreeCursor
-- addSubBlock Nothing newSv (sv, vs) = (mergeStructValues newSv sv, vs)
-- addSubBlock (Just (StringSelector sel)) newSv (sv, vs) =
--   (sv {structFields = Map.insert sel (Struct newSv) (structFields sv)}, vs)

-- | Search the var upwards in the tree. Returns the path to the value and the value.
searchUpVar :: String -> TreeCursor -> Maybe (Path, Value)
searchUpVar var = go
  where
    go :: TreeCursor -> Maybe (Path, Value)
    go (sv, []) = case Map.lookup var (svFields sv) of
      Just v -> Just (Path [StringSelector var], v)
      Nothing -> Nothing
    go cursor@(sv, _) =
      case Map.lookup var (svFields sv) of
        Just v -> Just (appendSel (StringSelector var) (pathFromBlock cursor), v)
        Nothing -> goUp cursor >>= go

pathFromBlock :: TreeCursor -> Path
pathFromBlock (_, crumbs) = Path . reverse $ go crumbs []
  where
    go :: [TreeCrumb] -> [Selector] -> [Selector]
    go [] acc = acc
    go ((n, _) : cs) acc = go cs (n : acc)

goToBlock :: TreeCursor -> Path -> Maybe TreeCursor
goToBlock block p =
  let topBlock = propagateBack block
   in goDown p topBlock

-- | propagateBack propagates the changes to the parent blocks until the root block.
propagateBack :: TreeCursor -> TreeCursor
propagateBack (sv, cs) = go cs sv
  where
    go :: [TreeCrumb] -> StructValue -> TreeCursor
    go [] acc = (acc, [])
    go ((StringSelector sel, parSV) : restCS) acc =
      go restCS (parSV {svFields = Map.insert sel (Struct acc) (svFields parSV)})

-- | Go to the block that contains the value.
-- The path should be the full path to the value.
goToScope :: TreeCursor -> Path -> Maybe TreeCursor
goToScope cursor p = goToBlock cursor (fromJust $ initPath p)

-- | Locates the value by the path starting from the given block.
locateGetValue :: (MonadError String m) => TreeCursor -> Path -> m Value
locateGetValue block (Path []) = return $ Struct $ fst block
locateGetValue block path = case goToScope block path of
  Nothing -> throwError $ printf "locateGetValue: holding block is not found, path: %s" (show path)
  Just parentBlock -> getVal (fromJust $ lastSel path) parentBlock
    where
      getVal :: (MonadError String m) => Selector -> TreeCursor -> m Value
      getVal (StringSelector name) (StructValue _ fields _ _, _) =
        case Map.lookup name fields of
          Nothing -> throwError $ printf "locateGetValue: path: %s, field: %s is not found" (show path) name
          Just penVal -> return penVal

getValueFromCtx :: (MonadError String m, MonadState Context m) => Path -> m Value
getValueFromCtx path = do
  (Context block _) <- get
  locateGetValue block path

locateSetValue :: (MonadError String m) => TreeCursor -> Path -> Value -> m TreeCursor
locateSetValue block (Path []) (Struct sv) = return $ attach sv block
locateSetValue _ (Path []) v =
  throwError $ printf "locateSetValue: cannot set value to a non-struct value, value: %s" (show v)
locateSetValue block path val = case goToScope block path of
  Nothing -> throwError $ printf "locateSetValue: scope is not found, path: %s" (show path)
  Just scope -> updateVal (fromJust $ lastSel path) val scope
  where
    updateVal :: (MonadError String m) => Selector -> Value -> TreeCursor -> m TreeCursor
    updateVal (StringSelector name) newVal (sv, vs) =
      let newFields = Map.insert name newVal (svFields sv)
          newConcrSet =
            if isValueConcrete newVal
              then Set.insert name (svConcretes sv)
              else svConcretes sv
       in return (sv {svFields = newFields, svConcretes = newConcrSet}, vs)

-- | Put value to the context at the given path. The ctx is updated to the root.
putValueInCtx :: (Runtime m) => Path -> Value -> m ()
putValueInCtx path val = do
  ctx@(Context block _) <- get
  newBlock <- locateSetValue block path val
  dump $ printf "putValueInCtx: path: %s, value: %s" (show path) (show val)
  put $ ctx {ctxCurBlock = propagateBack newBlock}

emptyStruct :: StructValue
emptyStruct = StructValue [] Map.empty Set.empty Set.empty

-- | Show is only used for debugging.
instance Show Value where
  show (String s) = s
  show (Int i) = show i
  show (Bool b) = show b
  show Top = "_"
  show Null = "null"
  show (Struct sv) = show sv
  show (Disjunction dfs djs) = "D: " ++ show dfs ++ ", " ++ show djs
  show (Bottom msg) = "_|_: " ++ msg
  show (Pending v) = show v
  show (Unevaluated p) = "U: " ++ show p
  show (Validator dv) = show dv

instance Eq Value where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) (Struct sv1) (Struct sv2) = sv1 == sv2
  (==) (Disjunction defaults1 disjuncts1) (Disjunction defaults2 disjuncts2) =
    disjuncts1 == disjuncts2 && defaults1 == defaults2
  (==) (Bottom _) (Bottom _) = True
  (==) Top Top = True
  (==) Null Null = True
  (==) (Pending pv1) (Pending pv2) = pv1 == pv2
  (==) (Unevaluated p1) (Unevaluated p2) = p1 == p2
  (==) _ _ = False

toExpr :: (MonadError String m) => Value -> m AST.Expression
toExpr Top = return $ AST.litCons AST.TopLit
toExpr (String s) = return $ AST.litCons (AST.StringLit (AST.SimpleStringLit s))
toExpr (Int i) = return $ AST.litCons (AST.IntLit i)
toExpr (Bool b) = return $ AST.litCons (AST.BoolLit b)
toExpr Null = return $ AST.litCons AST.NullLit
toExpr (Bottom _) = return $ AST.litCons AST.BottomLit
toExpr (Struct sv) =
  let fields = Map.toList (svFields sv)
   in do
        fieldList <-
          mapM
            ( \(label, val) -> do
                e <- toExpr val
                let ln = if Set.member label (svVars sv) then AST.LabelID label else AST.LabelString label
                return (AST.Label . AST.LabelName $ ln, e)
            )
            fields
        return $ AST.litCons (AST.StructLit fieldList)
toExpr (Disjunction dfs djs) =
  let valList = if not $ null dfs then dfs else djs
   in do
        es <- mapM toExpr valList
        return $ foldr1 (\x y -> AST.ExprBinaryOp AST.Disjunction x y) es
toExpr (Pending pv) =
  if not $ isValueUnevaluated (pvTemp pv)
    then toExpr (pvTemp pv)
    else throwError "toExpr: unevaluated temp value of pending value"
toExpr (Unevaluated _) = throwError "toExpr: unevaluated value"
