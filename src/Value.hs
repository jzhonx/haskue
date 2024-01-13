{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

module Value where

import           Control.Monad.Except       (MonadError, throwError)
import           Control.Monad.State.Strict (MonadState, get, modify, put)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import           Data.ByteString.Builder    (Builder, char7, integerDec,
                                             string7)
import           Data.Graph                 (SCC (CyclicSCC), graphFromEdges,
                                             reverseTopSort, stronglyConnComp)
import qualified Data.Map.Strict            as Map
import           Data.Maybe                 (fromJust)
import qualified Data.Set                   as Set
import           Debug.Trace
import           Text.Printf                (printf)

-- TODO: IntSelector
data Selector = StringSelector String deriving (Eq, Ord)

instance Show Selector where
  show (StringSelector s) = s

-- | Path is full path to a value.
newtype Path = Path [Selector] deriving (Eq, Ord)

showPath :: Path -> String
showPath (Path sels) = go (reverse sels) ""
  where
    go :: [Selector] -> String -> String
    go [] acc = acc
    go (x : xs) acc
      | acc == "" = go xs (show x)
      | otherwise = go xs (show x ++ "." ++ acc)

instance Show Path where
  show = showPath

pathFromList :: [Selector] -> Path
pathFromList sels = Path (reverse sels)

appendSel :: Selector -> Path -> Path
appendSel sel (Path xs) = Path (sel : xs)

initPath :: Path -> Maybe Path
initPath (Path []) = Nothing
initPath (Path xs) = Just $ Path (tail xs)

lastSel :: Path -> Maybe Selector
lastSel (Path []) = Nothing
lastSel (Path xs) = Just $ head xs

-- -- relPath p base returns the relative path from base to p.
-- -- If base is not a prefix of p, then p is returned.
-- relPath :: Path -> Path -> Path
-- relPath (Path p) (Path base) = Path $ go (reverse p) (reverse base) []
--   where
--     go :: [Selector] -> [Selector] -> [Selector] -> [Selector]
--     go [] _ acc = acc
--     go _ [] acc = acc
--     go (x : xs) (y : ys) acc =
--       if x == y
--         then go xs ys (x : acc)
--         else acc

-- TODO: dedeup
mergePaths :: [(Path, Path)] -> [(Path, Path)] -> [(Path, Path)]
mergePaths p1 p2 = p1 ++ p2

-- | TreeCrumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type TreeCrumb = (Selector, StructValue)

type TreeCursor = (StructValue, [TreeCrumb])

goUp :: TreeCursor -> Maybe TreeCursor
goUp (_, [])           = Nothing
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

-- topTo :: Path -> TreeCursor -> Maybe TreeCursor
-- topTo to cursor = goDown to $ topMost cursor

attach :: StructValue -> TreeCursor -> TreeCursor
attach sv (_, vs) = (sv, vs)

addSubBlock :: Maybe Selector -> StructValue -> TreeCursor -> TreeCursor
addSubBlock Nothing newSv (sv, vs) = (mergeStructValues newSv sv, vs)
addSubBlock (Just (StringSelector sel)) newSv (sv, vs) =
  (sv {structFields = Map.insert sel (Struct newSv) (structFields sv)}, vs)

searchVarUp :: String -> TreeCursor -> Maybe Value
searchVarUp varName = go
  where
    go :: TreeCursor -> Maybe Value
    go (StructValue _ fields _, []) = Map.lookup varName fields
    go cursor@(StructValue _ fields _, _) =
      case Map.lookup varName fields of
        Just v  -> Just v
        Nothing -> goUp cursor >>= go

-- topMost :: TreeCursor -> TreeCursor
-- topMost (v, [])          = (v, [])
-- topMost (_, (_, v) : vs) = topMost (v, vs)

pathFromBlock :: TreeCursor -> Path
pathFromBlock (_, crumbs) = Path . reverse $ go crumbs []
  where
    go :: [TreeCrumb] -> [Selector] -> [Selector]
    go [] acc            = acc
    go ((n, _) : cs) acc = go cs (n : acc)

svFromVal :: Value -> Maybe StructValue
svFromVal (Struct sv) = Just sv
svFromVal _           = Nothing

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
  { -- curBlock is the current block that contains the variables.
    -- A new block will replace the current one when a new block is entered.
    -- A new block is entered when one of the following is encountered:
    -- - The "{" token
    -- - for and let clauses
    ctxCurBlock    :: TreeCursor,
    ctxReverseDeps :: Map.Map Path Path
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
        -- the first element of the tuple is the path to a pending value (could be another pending value).
        -- the second element of the tuple is the reference path.
        pendDepEdges  :: [(Path, Path)],
        -- evaluator is a function that takes a list of values and returns a value.
        -- The order of the values in the list is the same as the order of the paths in deps.
        pendEvaluator :: Evaluator
      }
  | Unevaluated

data StructValue = StructValue
  { structOrderedLabels :: [String],
    structFields        :: Map.Map String Value,
    structIDs           :: Set.Set String
  }
  deriving (Show, Eq)

-- TODO: merge same keys handler
-- two embeded structs can have same keys
mergeStructValues :: StructValue -> StructValue -> StructValue
mergeStructValues (StructValue ols1 fields1 ids1) (StructValue ols2 fields2 ids2) =
  StructValue (ols1 ++ ols2) (Map.union fields1 fields2) (Set.union ids1 ids2)

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

goToBlock :: (MonadError String m) => TreeCursor -> Path -> m TreeCursor
goToBlock block p = do
  topBlock <- propagateBack block
  case goDown p topBlock of
    Just b -> return b
    Nothing ->
      throwError $
        "value block, path: "
          ++ show p
          ++ " is not found"

-- | Go to the block that contains the value.
-- The path should be the full path to the value.
goToValBlock :: (MonadError String m) => TreeCursor -> Path -> m TreeCursor
goToValBlock cursor p = goToBlock cursor (fromJust $ initPath p)

propagateBack :: (MonadError String m) => TreeCursor -> m TreeCursor
propagateBack (sv, cs) = go cs sv
  where
    go :: (MonadError String m) => [TreeCrumb] -> StructValue -> m TreeCursor
    go [] acc = return (acc, [])
    go ((StringSelector sel, parSV) : restCS) acc =
      go restCS (parSV {structFields = Map.insert sel (Struct acc) (structFields parSV)})

locateGetValue :: (MonadError String m) => TreeCursor -> Path -> m Value
locateGetValue block path = goToValBlock block path >>= getVal (fromJust $ lastSel path)
  where
    getVal :: (MonadError String m) => Selector -> TreeCursor -> m Value
    getVal (StringSelector name) (StructValue _ fields _, _) =
      case Map.lookup name fields of
        Nothing -> throwError $ "pending value, name: " ++ show name ++ " is not found"
        Just penVal -> return penVal

locateSetValue :: (MonadError String m) => TreeCursor -> Path -> Value -> m TreeCursor
locateSetValue block path val = goToValBlock block path >>= updateVal (fromJust $ lastSel path) val
  where
    updateVal :: (MonadError String m) => Selector -> Value -> TreeCursor -> m TreeCursor
    updateVal (StringSelector name) newVal (StructValue ols fields ids, vs) =
      return (StructValue ols (Map.insert name newVal fields) ids, vs)

modifyValueInCtx :: (MonadError String m, MonadState Context m) => Path -> Value -> m ()
modifyValueInCtx path val = do
  ctx@(Context block _) <- get
  newBlock <- locateSetValue block path val
  updatedOrig <- goToBlock newBlock (pathFromBlock block)
  put $ ctx {ctxCurBlock = updatedOrig}

-- | Checks whether the given value can be applied to the pending value that depends on the given value. If it can, then
-- apply the value to the pending value.
checkEvalPen ::
  (MonadError String m, MonadState Context m) => (Path, Value) -> m ()
checkEvalPen (valPath, val) = do
  Context curBlock revDeps <- get
  case Map.lookup valPath revDeps of
    Nothing -> return ()
    Just penPath -> do
      penVal <- locateGetValue curBlock penPath
      newPenVal <- applyPen (penPath, penVal) (valPath, val)
      -- update the pending block.
      modifyValueInCtx
        penPath
        ( trace
            ( printf
                "penVal: %s, penPath: %s, val: %s, valPath: %s, newPenVal: %s"
                (show penVal)
                (show penPath)
                (show val)
                (show valPath)
                (show newPenVal)
            )
            newPenVal
        )

-- | Apply value to the pending value which is inside the current context.
-- It returns the new updated value.
applyPen :: (MonadError String m, MonadState Context m) => (Path, Value) -> (Path, Value) -> m Value
applyPen (penPath, Pending deps evalf) (valPath, val) =
  let newDeps = filter (\(_, depPath) -> depPath /= valPath) deps
      newEvalf xs = evalf ((valPath, val) : xs)
   in do
        modify (\ctx -> ctx {ctxReverseDeps = Map.delete valPath (ctxReverseDeps ctx)})
        if null (trace (printf "penPath: %s newDeps: %s" (show penPath) (show newDeps)) newDeps)
          then do
            v <- newEvalf []
            -- Once the pending value is evaluated, we should trigger the fillPen for other pending values that depend
            -- on this value.
            checkEvalPen (penPath, v)
            return v
          else return $ Pending newDeps newEvalf
applyPen _ _ = throwError "applyPen: impossible"

-- lookupVar looks up the variable denoted by the name.
lookupVar :: (MonadError String m, MonadState Context m) => String -> Path -> m Value
lookupVar name path = do
  Context block revDeps <- get
  case searchVarUp name block of
    -- TODO: currently we should only look up the current block.
    Just Unevaluated ->
      let depPath = appendSel (StringSelector name) (fromJust $ initPath path)
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
  show (Pending edges _) = printf "(Pending, edges: %s)" (show edges)
  show Unevaluated = "Unevaluated"

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
