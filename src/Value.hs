{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Value where

import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (MonadState, get, modify, put)
import Control.Monad.Trans.Maybe (MaybeT (..))
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
import Debug.Trace
import Path
import Text.Printf (printf)

svFromVal :: Value -> Maybe StructValue
svFromVal (Struct sv) = Just sv
svFromVal _ = Nothing

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

type EvalMonad a = forall m. (MonadError String m, MonadState Context m) => m a

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

data StructValue = StructValue
  { structOrderedLabels :: [String],
    structFields :: Map.Map String Value,
    structIDs :: Set.Set String
  }
  deriving (Show, Eq)

data PendingValue
  = PendingValue
      { -- pendPath is the path to the pending value.
        pendPath :: Path,
        -- depEdges is a list of paths to the unresolved immediate references.
        -- path should be the full path.
        -- The edges are primarily used to detect cycles.
        -- the first element of the tuple is the path to a pending value.
        -- the second element of the tuple is the path to a value that the pending value depends on.
        pendDeps :: [(Path, Path)],
        pendArgs :: [(Path, Value)],
        -- evaluator is a function that takes a list of values and returns a value.
        -- The order of the values in the list is the same as the order of the paths in deps.
        pendEvaluator :: Evaluator
      }
  | Unevaluated {unevalPath :: Path}

instance Show PendingValue where
  show (PendingValue p d a _) =
    printf "(Pending, path: %s deps: %s, args: %s)" (show p) (show d) (show a)
  show (Unevaluated p) = printf "(Unevaluated, path: %s)" (show p)

-- TODO: merge same keys handler
-- two embeded structs can have same keys
mergeStructValues :: StructValue -> StructValue -> StructValue
mergeStructValues (StructValue ols1 fields1 ids1) (StructValue ols2 fields2 ids2) =
  StructValue (ols1 ++ ols2) (Map.union fields1 fields2) (Set.union ids1 ids2)

mergeArgs :: [(Path, Value)] -> [(Path, Value)] -> [(Path, Value)]
mergeArgs xs ys = Map.toList $ Map.fromList (xs ++ ys)

-- | The binFunc is used to evaluate a binary function with two arguments.
binFunc :: (MonadError String m, MonadState Context m) => (Value -> Value -> EvalMonad Value) -> Value -> Value -> m Value
binFunc bin (Pending (PendingValue p1 d1 a1 e1)) (Pending (PendingValue p2 d2 a2 e2))
  | p1 == p2 =
      return $
        Pending $
          PendingValue
            p1
            (mergePaths d1 d2)
            (mergeArgs a1 a2)
            ( \xs -> do
                v1 <- e1 xs
                v2 <- e2 xs
                bin v1 v2
            )
  | otherwise =
      throwError $
        printf "binFunc: two pending values have different paths, p1: %s, p2: %s" (show p1) (show p2)
binFunc bin v1@(Pending {}) v2 = unaFunc (`bin` v2) v1
binFunc bin v1 v2@(Pending {}) = unaFunc (bin v1) v2
binFunc bin v1 v2 = bin v1 v2

-- | The unaFunc is used to evaluate a unary function.
-- The first argument is the function that takes the value and returns a value.
unaFunc :: (MonadError String m, MonadState Context m) => (Value -> EvalMonad Value) -> Value -> m Value
unaFunc f (Pending (PendingValue p d a e)) = return $ Pending $ PendingValue p d a (bindEval e f)
unaFunc f v = f v

-- | Binds the evaluator to a function that uses the value as the argument.
bindEval :: Evaluator -> (Value -> EvalMonad Value) -> Evaluator
bindEval evalf f xs = evalf xs >>= f

mkUnevaluated :: Path -> Value
mkUnevaluated = Pending . Unevaluated

-- | Creates a new simple pending value.
mkPending :: Path -> Path -> Value
mkPending src dst = Pending $ newPendingValue src dst

-- | Creates a new pending value.
newPendingValue :: Path -> Path -> PendingValue
newPendingValue src dst = PendingValue src [(src, dst)] [] f
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
    next n@(StringSelector name) (sv@(StructValue _ fields _), vs) = do
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

addSubBlock :: Maybe Selector -> StructValue -> TreeCursor -> TreeCursor
addSubBlock Nothing newSv (sv, vs) = (mergeStructValues newSv sv, vs)
addSubBlock (Just (StringSelector sel)) newSv (sv, vs) =
  (sv {structFields = Map.insert sel (Struct newSv) (structFields sv)}, vs)

searchUpVar :: String -> TreeCursor -> Maybe (Value, TreeCursor)
searchUpVar var = go
  where
    go :: TreeCursor -> Maybe (Value, TreeCursor)
    go cursor@(StructValue _ fields _, []) = case Map.lookup var fields of
      Just v -> Just (v, cursor)
      Nothing -> Nothing
    go cursor@(StructValue _ fields _, _) =
      case Map.lookup var fields of
        Just v -> Just (v, cursor)
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
      go restCS (parSV {structFields = Map.insert sel (Struct acc) (structFields parSV)})

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
      getVal (StringSelector name) (StructValue _ fields _, _) =
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
  Nothing -> throwError $ printf "locateSetValue: holding block is not found, path: %s" (show path)
  Just parentBlock -> updateVal (fromJust $ lastSel path) val parentBlock
  where
    updateVal :: (MonadError String m) => Selector -> Value -> TreeCursor -> m TreeCursor
    updateVal (StringSelector name) newVal (StructValue ols fields ids, vs) =
      return (StructValue ols (Map.insert name newVal fields) ids, vs)

-- | Put value to the context at the given path. The ctx is updated to the root.
putValueInCtx :: (MonadError String m, MonadState Context m) => Path -> Value -> m ()
putValueInCtx path val = do
  ctx@(Context block _) <- get
  newBlock <- locateSetValue block path val
  put $ ctx {ctxCurBlock = propagateBack newBlock}

-- | Checks whether the given value can be applied to the pending value that depends on the given value. If it can, then
-- apply the value to the pending value.
tryEvalPen ::
  (MonadError String m, MonadState Context m) => (Path, Value) -> m ()
tryEvalPen (_, Pending {}) = return ()
tryEvalPen (valPath, val) = do
  Context curBlock revDeps <- get
  case Map.lookup valPath revDeps of
    Nothing -> return ()
    Just penPath -> do
      penVal <- locateGetValue curBlock penPath
      trace
        ( printf
            "checkEvalPen pre: %s->%s, val: %s, penVal: %s"
            (show valPath)
            (show penPath)
            (show val)
            (show penVal)
        )
        pure
        ()
      newPenVal <- applyPen (penPath, penVal) (valPath, val)
      case newPenVal of
        Pending {} -> pure ()
        -- Once the pending value is evaluated, we should trigger the fillPen for other pending values that depend
        -- on this value.
        v -> tryEvalPen (penPath, v)
      -- update the pending block.
      putValueInCtx penPath newPenVal
      trace
        ( printf
            "checkEvalPen post: %s->%s, val: %s, penVal: %s, newPenVal: %s"
            (show valPath)
            (show penPath)
            (show val)
            (show penVal)
            (show newPenVal)
        )
        pure
        ()

-- | Apply value to the pending value. It returns the new updated value.
-- It keeps applying the value to the pending value until the pending value is evaluated.
applyPen :: (MonadError String m, MonadState Context m) => (Path, Value) -> (Path, Value) -> m Value
applyPen (penPath, penV@(Pending {})) pair = go penV pair
  where
    go :: (MonadError String m, MonadState Context m) => Value -> (Path, Value) -> m Value
    go (Pending (PendingValue selfPath deps args f)) (valPath, val) =
      let newDeps = filter (\(_, depPath) -> depPath /= valPath) deps
          newArgs = ((valPath, val) : args)
       in do
            modify (\ctx -> ctx {ctxReverseDeps = Map.delete valPath (ctxReverseDeps ctx)})
            trace
              ( printf
                  "applyPen: %s->%s, args: %s, newDeps: %s"
                  (show valPath)
                  (show penPath)
                  (show newArgs)
                  (show newDeps)
              )
              pure
              ()
            if null newDeps
              then f newArgs >>= \v -> go v pair
              else return $ Pending $ PendingValue selfPath newDeps newArgs f
    go v _ = return v
applyPen (_, v) _ = throwError $ printf "applyPen expects a pending value, but got %s" (show v)

-- | Looks up the variable denoted by the name in the current block or the parent blocks.
-- If the variable is not evaluated yet or pending, a new pending value is created and returned.
-- Parameters:
--   var denotes the variable name.
--   path is the path to the current expression that contains the selector.
-- For example,
--  { a: b: x+y }
-- If the name is "y", and the path is "a.b".
lookupVar :: (MonadError String m, MonadState Context m) => String -> Path -> m Value
lookupVar var path = do
  ctx <- get
  let scope = case goToScope (ctxCurBlock ctx) path of
        Just b -> b
        Nothing -> ctxCurBlock ctx
  case searchUpVar var scope of
    Just (Pending v, _) -> depend path v
    Just (v, _) -> do
      trace (printf "lookupVar found var %s, block: %s, value: %s" (show var) (show scope) (show v)) pure ()
      pure v
    Nothing ->
      throwError $
        printf "variable %s is not found, path: %s, scope: %s" var (show path) (show scope)

-- | access the named field of the struct.
-- Parameters:
--   s is the name of the field.
--   path is the path to the current expression that contains the selector.
dot :: (MonadError String m, MonadState Context m) => String -> Path -> Value -> m Value
dot field path value = case value of
  Disjunction [x] _ -> lookupStructField x
  _ -> lookupStructField value
  where
    lookupStructField (Struct (StructValue _ fields _)) = case Map.lookup field fields of
      -- The referenced value could be a pending value. Once the pending value is evaluated, the selector should be
      -- populated with the value.
      Just (Pending v) -> depend path v
      Just v -> return v
      Nothing -> return $ Bottom $ field ++ " is not found"
    lookupStructField _ =
      return $
        Bottom $
          printf
            "evalSelector: path: %s, sel: %s, value: %s is not a struct"
            (show path)
            (show field)
            (show value)

-- | Creates a dependency between the current value of the curPath to the value of the depPath.
-- If there is a cycle, the Top is returned.
depend :: (MonadError String m, MonadState Context m) => Path -> PendingValue -> m Value
depend path val = case val of
  (Unevaluated p) ->
    if p == path
      then do
        trace (printf "depend Cycle detected: path: %s" (show path)) pure ()
        createTop
      else createDepVal p
  (PendingValue p _ _ _) -> createDepVal p
  where
    createTop :: (MonadError String m, MonadState Context m) => m Value
    createTop = do
      -- checkEvalPen (path, Top)
      return Top

    checkCycle :: (MonadError String m, MonadState Context m) => (Path, Path) -> m Bool
    checkCycle (src, dst) = do
      Context _ revDeps <- get
      -- we have to reverse the new edge because the graph is reversed.
      return $ depsHasCycle ((dst, src) : Map.toList revDeps)

    createDepVal :: (MonadError String m, MonadState Context m) => Path -> m Value
    createDepVal depPath = do
      cycleDetected <- checkCycle (path, depPath)
      if cycleDetected
        then do
          trace (printf "depend Cycle detected: path: %s" (show path)) pure ()
          createTop
        else do
          modify (\ctx -> ctx {ctxReverseDeps = Map.insert depPath path (ctxReverseDeps ctx)})
          trace (printf "depend: path: %s, depPath: %s" (show path) (show depPath)) pure ()
          return $ Pending $ newPendingValue path depPath

emptyStruct :: StructValue
emptyStruct = StructValue [] Map.empty Set.empty

-- | Show is only used for debugging.
instance Show Value where
  show (String s) = s
  show (Int i) = show i
  show (Bool b) = show b
  show Top = "_"
  show Null = "null"
  show (Struct (StructValue ols fds _)) = "{ labels:" ++ show ols ++ ", fields: " ++ show fds ++ "}"
  show (Disjunction dfs djs) = "Disjunction: " ++ show dfs ++ ", " ++ show djs
  show (Bottom msg) = "_|_: " ++ msg
  show (Pending v) = show v

instance Eq Value where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) (Struct (StructValue orderedLabels1 edges1 _)) (Struct (StructValue orderedLabels2 edges2 _)) =
    orderedLabels1 == orderedLabels2 && edges1 == edges2
  (==) (Disjunction defaults1 disjuncts1) (Disjunction defaults2 disjuncts2) =
    disjuncts1 == disjuncts2 && defaults1 == defaults2
  (==) (Bottom _) (Bottom _) = True
  (==) Top Top = True
  (==) Null Null = True
  (==) _ _ = False

buildCUEStr :: Value -> Builder
buildCUEStr = buildCUEStr' 0

buildCUEStr' :: Int -> Value -> Builder
buildCUEStr' _ (String s) = char7 '"' <> string7 s <> char7 '"'
buildCUEStr' _ (Int i) = integerDec i
buildCUEStr' _ (Bool b) = if b then string7 "true" else string7 "false"
buildCUEStr' _ Top = string7 "_"
buildCUEStr' _ Null = string7 "null"
buildCUEStr' ident (Struct (StructValue ols fds _)) =
  buildStructStr ident (map (\label -> (label, fds Map.! label)) ols)
buildCUEStr' ident (Disjunction dfs djs) =
  if null dfs
    then buildList djs
    else buildList dfs
  where
    buildList xs = foldl1 (\x y -> x <> string7 " | " <> y) (map (\d -> buildCUEStr' ident d) xs)
buildCUEStr' _ (Bottom _) = string7 "_|_"
buildCUEStr' _ (Pending {}) = string7 "_|_"

buildStructStr :: Int -> [(String, Value)] -> Builder
buildStructStr ident xs =
  if null xs
    then string7 "{}"
    else
      char7 '{'
        <> char7 '\n'
        <> buildFieldsStr ident xs
        <> string7 (replicate (ident * 2) ' ')
        <> char7 '}'

buildFieldsStr :: Int -> [(String, Value)] -> Builder
buildFieldsStr _ [] = string7 ""
buildFieldsStr ident (x : xs) =
  f x <> buildFieldsStr ident xs
  where
    f (label, val) =
      string7 (replicate ((ident + 1) * 2) ' ')
        <> string7 label
        <> string7 ": "
        <> buildCUEStr' (ident + 1) val
        <> char7 '\n'
