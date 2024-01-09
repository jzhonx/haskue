{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

module Value where

import           Control.Monad.Except       (MonadError, throwError)
import           Control.Monad.State.Strict (MonadState, get, modify, put,
                                             runStateT)
import           Data.ByteString.Builder    (Builder, char7, integerDec,
                                             string7)
import           Data.Graph                 (SCC (CyclicSCC), graphFromEdges,
                                             reverseTopSort, stronglyConnComp)
import qualified Data.Map.Strict            as Map
import qualified Data.Set                   as Set

-- TODO: IntSelector
data Selector = TopSelector | StringSelector String deriving (Eq, Ord, Show)

type Path = [Selector]

-- relPath x base returns the relative path from base to x.
-- If base is not a prefix of x, then x is returned.
relPath :: Path -> Path -> Path
relPath x base =
  let (prefix, suffix) = splitAt (length base) x
   in if prefix == base then suffix else x

-- TODO: dedeup
mergePaths :: [(Path, Path)] -> [(Path, Path)] -> [(Path, Path)]
mergePaths p1 p2 = p1 ++ p2

-- | TreeCrumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type TreeCrumb = (Selector, Value)

type TreeCursor = (Value, [TreeCrumb])

goUp :: TreeCursor -> Maybe TreeCursor
goUp (_, [])           = Nothing
goUp (_, (_, v') : vs) = Just (v', vs)

goTo :: Path -> TreeCursor -> Maybe TreeCursor
goTo [] cursor = Just cursor
goTo (x : xs) cursor = do
  next <- g x cursor
  goTo xs next
  where
    g :: Selector -> TreeCursor -> Maybe TreeCursor
    g n@(StringSelector name) (val@(Struct (StructValue _ fields' _)), vs) = do
      val' <- Map.lookup name fields'
      return (val', (n, val) : vs)
    g _ (_, _) = Nothing

topTo :: Path -> TreeCursor -> Maybe TreeCursor
topTo to cursor = goTo to $ topMost cursor

attach :: Value -> TreeCursor -> TreeCursor
attach val (_, vs) = (val, vs)

addSubTree :: Selector -> Value -> TreeCursor -> TreeCursor
addSubTree sel new (old, vs) = (new, (sel, old) : vs)

searchUp :: String -> TreeCursor -> Maybe Value
searchUp name (Struct (StructValue _ fields' _), []) = Map.lookup name fields'
searchUp name z@(Struct (StructValue _ fields' _), _) =
  case Map.lookup name fields' of
    Just v -> Just v
    Nothing -> do
      z' <- goUp z
      searchUp name z'
searchUp _ _ = Nothing

topMost :: TreeCursor -> TreeCursor
topMost (v, [])          = (v, [])
topMost (_, (_, v) : vs) = topMost (v, vs)

-- -- | Takes a list of paths and returns a list of paths in the dependency order.
-- -- In the returned list, the first element is the path that has can be evaluated.
-- depEdgesOrder :: [(Path, Path)] -> Maybe [Path]
-- depEdgesOrder ps = depsOrder edges
--   where
--     depMap = Map.fromListWith (++) (map (\(k, v) -> (k, [v])) ps)
--     edges = Map.toList depMap

-- depsOrder :: [(Path, [Path])] -> Maybe [Path]
-- depsOrder dps =
--   if hasCycle edgesForGraph
--     then Nothing
--     else Just $ map (\v -> let (_, p, _) = nodeFromVertex v in p) (reverseTopSort graph)
--   where
--     edgesForGraph = map (\(k, vs) -> ((), k, vs)) dps
--     (graph, nodeFromVertex, _) = graphFromEdges edgesForGraph

-- hasCycle :: Ord key => [(node, key, [key])] -> Bool
hasCycle :: [(Path, [Path])] -> Bool
hasCycle edges = any isCycle (stronglyConnComp edgesForGraph)
  where
    edgesForGraph = map (\(k, vs) -> ((), k, vs)) edges

    isCycle (CyclicSCC _) = True
    isCycle _             = False

-- structPenOrder :: Path -> Map.Map String Value -> Maybe [String]
-- structPenOrder curPath xs = undefined
--   where
--     penSubGraph :: String -> Value -> Maybe (Path, String, [Path])
--     penSubGraph k (Pending dps _) = Just (curPath ++ [StringSelector k], k, map snd dps)
--     penSubGraph _ _ = Nothing
--
--     penFields :: [(Path, String, [Path])]
--     penFields = Map.foldrWithKey (\k field acc -> case penSubGraph k field of Just res -> res : acc; Nothing -> acc) [] xs
--
--     penOrder :: Maybe [Path]
--     penOrder = depsOrder $ map (\(p, _, dps) -> (p, dps)) penFields

-- | Context
data Context = Context
  { -- path is the path to the current expression.
    -- the path should be the full path.
    path        :: Path,
    -- curBlock is the current block that contains the variables.
    -- A new block will replace the current one when a new block is entered.
    -- A new block is entered when one of the following is encountered:
    -- - The "{" token
    -- - for and let clauses
    curBlock    :: TreeCursor,
    reverseDeps :: Map.Map Path Path
  }

type EvalMonad a = forall m. (MonadError String m, MonadState Context m) => m a

type Evaluator = [(Path, Value)] -> EvalMonad Value

data Value
  = Top
  | String String
  | Int Integer
  | Bool Bool
  | Struct StructValue
  | Disjunction
      { defaults  :: [Value],
        disjuncts :: [Value]
      }
  | Null
  | Bottom String
  | Pending
      { -- depEdges is a list of paths to the unresolved references.
        -- path should be the full path.
        -- The edges are primarily used to detect cycles.
        -- the first element of the tuple is the variable path.
        -- the second element of the tuple is the reference path.
        depEdges  :: [(Path, Path)],
        -- evaluator is a function that takes a list of values and returns a value.
        -- The order of the values in the list is the same as the order of the paths in deps.
        evaluator :: Evaluator
      }
  | Unevaluated

data StructValue = StructValue
  { orderedLabels :: [String],
    fields        :: Map.Map String Value,
    identifiers   :: Set.Set String
  }

-- | The binFunc is used to evaluate a binary function with two arguments.
binFunc :: (MonadError String m, MonadState Context m) => (Value -> Value -> EvalMonad Value) -> Value -> Value -> m Value
binFunc bin v1@(Pending {}) v2@(Pending {}) = unaFunc (\x -> unaFunc (bin x) v2) v1
binFunc bin v1@(Pending {}) v2 = unaFunc (`bin` v2) v1
binFunc bin v1 v2@(Pending {}) = unaFunc (bin v1) v2
binFunc bin v1 v2 = bin v1 v2

-- | The unaFunc is used to evaluate a unary function.
-- The first argument is the function that takes the evaluated value (inclduing pending) and returns a value.
unaFunc :: (MonadError String m, MonadState Context m) => (Value -> EvalMonad Value) -> Value -> m Value
unaFunc una (Pending d ev) = return $ Pending d (bindEval ev una)
unaFunc una v              = una v

-- | The bindEval function is used to bind the evaluator to the function.
bindEval :: Evaluator -> (Value -> EvalMonad Value) -> Evaluator
bindEval evalf f vs = evalf vs >>= f

newPending :: Path -> Path -> Value
newPending selfPath depPath =
  Pending
    [(selfPath, depPath)]
    ( \xs -> do
        case lookup depPath xs of
          Just v -> return v
          Nothing ->
            throwError $
              "Pending value can not find the dependent value, depPath: "
                ++ show depPath
                ++ ", args: "
                ++ show xs
    )

-- | Checks whether the given value can be applied to the pending value that depends on the given value. If it can, then
-- apply the value to the pending value.
checkEvalPen ::
  (MonadError String m, MonadState Context m) => (Path, Value) -> m ()
checkEvalPen (valPath, val) = do
  ctx <- get
  case Map.lookup valPath (reverseDeps ctx) of
    Nothing -> return ()
    Just penPath -> do
      case goToBlock (curBlock ctx) penPath of
        Nothing ->
          throwError $
            "pending value block, path: "
              ++ show penPath
              ++ " is not found"
        Just penBlock -> do
          let penValM = getPenVal penBlock (last penPath)
          case penValM of
            Nothing -> throwError $ "pending value, path: " ++ show penPath ++ " is not found"
            Just penVal -> do
              put $ ctx {path = penPath, curBlock = penBlock}
              penVal' <- applyPen (penPath, penVal) (valPath, val)
              -- restore the context.
              modify (\ctx' -> ctx' {path = path ctx, curBlock = setPenVal (curBlock ctx') (last penPath) penVal'})
  where
    goToBlock :: TreeCursor -> Path -> Maybe TreeCursor
    goToBlock block p =
      let topBlock = topMost block
       in goTo (init p) topBlock

    getPenVal :: TreeCursor -> Selector -> Maybe Value
    getPenVal (Struct (StructValue _ fields' _), _) (StringSelector name) = Map.lookup name fields'
    getPenVal _ _ = Nothing

    setPenVal :: TreeCursor -> Selector -> Value -> TreeCursor
    setPenVal (Struct (StructValue ols fields' ids), vs) (StringSelector name) val' =
      (Struct (StructValue ols (Map.insert name val' fields') ids), vs)
    setPenVal _ _ _ = undefined

-- | Apply value to the pending value which is inside the current context.
-- It returns the new updated value.
applyPen :: (MonadError String m, MonadState Context m) => (Path, Value) -> (Path, Value) -> m Value
applyPen (penPath, Pending dps evalf) (depPath, val) =
  let dps' = filter (\(p, _) -> p /= depPath) dps
      evalf' xs = evalf ((depPath, val) : xs)
      penVal' = Pending dps' evalf'
   in do
        modify (\ctx -> ctx {reverseDeps = Map.delete depPath (reverseDeps ctx)})
        if null dps'
          then do
            v <- evalf' []
            -- Once the pending value is evaluated, we should trigger the fillPen for other pending values that depend
            -- on this value.
            checkEvalPen (penPath, v)
            return v
          else return penVal'
applyPen _ _ = throwError "applyPen: impossible"

emptyStruct :: Value
emptyStruct = Struct (StructValue [] Map.empty Set.empty)

instance Show Value where
  show (String s) = s
  show (Int i) = show i
  show (Bool b) = show b
  show Top = "_"
  show Null = "null"
  show (Struct (StructValue ols fds _)) = "{ labels:" ++ show ols ++ ", fields: " ++ show fds ++ "}"
  show (Disjunction dfs djs) = "Disjunction: " ++ show dfs ++ ", " ++ show djs
  show (Bottom msg) = "_|_: " ++ msg
  show Pending {} = "_|_"
  show Unevaluated = "_|_"

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
buildCUEStr' _ Unevaluated = string7 "_|_"

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
