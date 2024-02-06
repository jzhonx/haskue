{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

module Value
  ( Context (..),
    EvalMonad,
    Evaluator,
    Value (..),
    PendingValue (..),
    StructValue (..),
    emptyStruct,
    isValueAtom,
    binFunc,
    unaFunc,
    mkUnevaluated,
    mkPending,
    putValueInCtx,
    getValueFromCtx,
    tryEvalPen,
    lookupVar,
    dot,
    strBld,
    applyPen,
  )
where

import qualified AST
import           Control.Monad.Except       (MonadError, throwError)
import           Control.Monad.State.Strict (MonadState, get, modify, put)
import           Data.ByteString.Builder    (Builder, char7, integerDec,
                                             string7)
import           Data.List                  (intercalate)
import qualified Data.Map.Strict            as Map
import           Data.Maybe                 (fromJust)
import qualified Data.Set                   as Set
import           Debug.Trace
import           Path
import           Text.Printf                (printf)

svFromVal :: Value -> Maybe StructValue
svFromVal (Struct sv) = Just sv
svFromVal _           = Nothing

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

-- | Evaluator is a function that takes a list of tuples values and their paths and returns a value.
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
  | Pending PendingValue

isValueAtom :: Value -> Bool
isValueAtom Top        = True
isValueAtom (String _) = True
isValueAtom (Int _)    = True
isValueAtom (Bool _)   = True
isValueAtom Null       = True
isValueAtom _          = False

data StructValue = StructValue
  { svLabels    :: [String],
    svFields    :: Map.Map String Value,
    svVars      :: Set.Set String,
    svConcretes :: Set.Set String
  }

instance Show StructValue where
  show (StructValue ols fds _ atoms) =
    printf "{labels: %s, fields: %s, atoms: %s }" (show ols) (show fds) (show atoms)

-- | For now we don't compare IDs and Concrete fields.
instance Eq StructValue where
  (==) (StructValue ols1 fields1 _ _) (StructValue ols2 fields2 _ _) =
    ols1 == ols2 && fields1 == fields2

data PendingValue
  = PendingValue
      { -- pvPath is the path to the pending value.
        pvPath      :: Path,
        -- depEdges is a list of paths to the unresolved immediate references.
        -- path should be the full path.
        -- The edges are primarily used to detect cycles.
        -- the first element of the tuple is the path to a pending value.
        -- the second element of the tuple is the path to a value that the pending value depends on.
        pvDeps      :: [(Path, Path)],
        pvArgs      :: [(Path, Value)],
        -- evaluator is a function that takes a list of values and returns a value.
        -- The order of the values in the list is the same as the order of the paths in deps.
        pvEvaluator :: Evaluator,
        pvExpr      :: AST.Expression
      }
  | Unevaluated
      { uePath :: Path,
        ueExpr :: AST.Expression
      }

instance Show PendingValue where
  show (PendingValue p d a _ e) =
    printf "(Pending, path: %s, deps: %s, args: %s, expr: %s)" (show p) prettyDeps (show a) (AST.exprStr e)
    where
      prettyDeps = intercalate ", " $ map (\(p1, p2) -> printf "(%s->%s)" (show p1) (show p2)) d
  show (Unevaluated p e) = printf "(Unevaluated, path: %s, expr: %s)" (show p) (AST.exprStr e)

-- TODO: merge same keys handler
-- two embeded structs can have same keys
-- mergeStructValues :: StructValue -> StructValue -> StructValue
-- mergeStructValues (StructValue ols1 fields1 ids1 atoms1) (StructValue ols2 fields2 ids2 atoms2) =
--   StructValue (ols1 ++ ols2) (Map.union fields1 fields2) (Set.union ids1 ids2) (isAtom1 && isAtom2)

mergeArgs :: [(Path, Value)] -> [(Path, Value)] -> [(Path, Value)]
mergeArgs xs ys = Map.toList $ Map.fromList (xs ++ ys)

-- | The binFunc is used to evaluate a binary function with two arguments.
binFunc :: (MonadError String m, MonadState Context m) => (Value -> Value -> EvalMonad Value) -> Value -> Value -> m Value
binFunc bin (Pending (PendingValue p1 d1 a1 e1 ex1)) (Pending (PendingValue p2 d2 a2 e2 _))
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
            -- TODO: use expr1 for now
            ex1
  | otherwise =
      throwError $
        printf "binFunc: two pending values have different paths, p1: %s, p2: %s" (show p1) (show p2)
binFunc bin v1@(Pending {}) v2 = unaFunc (`bin` v2) v1
binFunc bin v1 v2@(Pending {}) = unaFunc (bin v1) v2
binFunc bin v1 v2 = bin v1 v2

-- | The unaFunc is used to evaluate a unary function.
-- The first argument is the function that takes the value and returns a value.
unaFunc :: (MonadError String m, MonadState Context m) => (Value -> EvalMonad Value) -> Value -> m Value
unaFunc f (Pending (PendingValue p d a e expr)) = return $ Pending $ PendingValue p d a (bindEval e f) expr
unaFunc f v = f v

-- | Binds the evaluator to a function that uses the value as the argument.
bindEval :: Evaluator -> (Value -> EvalMonad Value) -> Evaluator
bindEval evalf f xs = evalf xs >>= f

mkUnevaluated :: Path -> AST.Expression -> Value
mkUnevaluated p e = Pending $ Unevaluated p e

-- | Creates a new simple pending value.
mkPending :: AST.Expression -> Path -> Path -> Value
mkPending expr src dst = Pending $ newPendingValue expr src dst

-- | Creates a new pending value.
newPendingValue :: AST.Expression -> Path -> Path -> PendingValue
newPendingValue expr src dst = PendingValue src [(src, dst)] [] f expr
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
goUp (_, [])           = Nothing
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

searchUpVar :: String -> TreeCursor -> Maybe (Value, TreeCursor)
searchUpVar var = go
  where
    go :: TreeCursor -> Maybe (Value, TreeCursor)
    go cursor@(StructValue _ fields _ _, []) = case Map.lookup var fields of
      Just v  -> Just (v, cursor)
      Nothing -> Nothing
    go cursor@(StructValue _ fields _ _, _) =
      case Map.lookup var fields of
        Just v  -> Just (v, cursor)
        Nothing -> goUp cursor >>= go

-- pathFromBlock :: TreeCursor -> Path
-- pathFromBlock (_, crumbs) = Path . reverse $ go crumbs []
--   where
--     go :: [TreeCrumb] -> [Selector] -> [Selector]
--     go [] acc = acc
--     go ((n, _) : cs) acc = go cs (n : acc)

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
            if isValueAtom newVal
              then Set.insert name (svConcretes sv)
              else svConcretes sv
       in return (sv {svFields = newFields, svConcretes = newConcrSet}, vs)

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
        v          -> tryEvalPen (penPath, v)
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
    go (Pending pv@(PendingValue {})) (valPath, val) =
      let newDeps = filter (\(_, depPath) -> depPath /= valPath) (pvDeps pv)
          newArgs = ((valPath, val) : pvArgs pv)
       in do
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
              then pvEvaluator pv newArgs >>= \v -> go v pair
              else return $ Pending $ pv {pvDeps = newDeps, pvArgs = newArgs}
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
        Just b  -> b
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
dot :: (MonadError String m, MonadState Context m) => AST.Expression -> String -> Path -> Value -> m Value
dot expr field path value = case value of
  Disjunction [x] _ -> lookupStructField x
  _                 -> lookupStructField value
  where
    lookupStructField (Struct (StructValue _ fields _ _)) = case Map.lookup field fields of
      -- The referenced value could be a pending value. Once the pending value is evaluated, the selector should be
      -- populated with the value.
      Just (Pending v) -> depend path v
      Just v -> return v
      -- The "incomplete" expression case.
      Nothing -> return $ mkPending expr path (appendSel (StringSelector field) path)
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
  (Unevaluated p e) ->
    if p == path
      then do
        trace (printf "depend self Cycle detected: path: %s" (show path)) pure ()
        return Top
      else createDepVal e p
  pv@(PendingValue {}) -> createDepVal (pvExpr pv) (pvPath pv)
  where
    checkCycle :: (MonadError String m, MonadState Context m) => (Path, Path) -> m Bool
    checkCycle (src, dst) = do
      Context _ revDeps <- get
      -- we have to reverse the new edge because the graph is reversed.
      return $ depsHasCycle ((dst, src) : Map.toList revDeps)

    createDepVal :: (MonadError String m, MonadState Context m) => AST.Expression -> Path -> m Value
    createDepVal expr depPath = do
      cycleDetected <- checkCycle (path, depPath)
      if cycleDetected
        then do
          trace (printf "depend Cycle detected: path: %s" (show path)) pure ()
          return Top
        else do
          modify (\ctx -> ctx {ctxReverseDeps = Map.insert depPath path (ctxReverseDeps ctx)})
          trace (printf "depend: %s->%s" (show path) (show depPath)) pure ()
          -- TODO: fix the expr
          return $ Pending $ newPendingValue expr path depPath

emptyStruct :: StructValue
emptyStruct = StructValue [] Map.empty Set.empty Set.empty

-- | Show is only used for debugging.
instance Show Value where
  show (String s)            = s
  show (Int i)               = show i
  show (Bool b)              = show b
  show Top                   = "_"
  show Null                  = "null"
  show (Struct sv)           = show sv
  show (Disjunction dfs djs) = "D: " ++ show dfs ++ ", " ++ show djs
  show (Bottom msg)          = "_|_: " ++ msg
  show (Pending v)           = show v

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
  (==) _ _ = False

strBld :: Value -> Builder
strBld = strBldIdent 0

strBldIdent :: Int -> Value -> Builder
strBldIdent _ (String s) = char7 '"' <> string7 s <> char7 '"'
strBldIdent _ (Int i) = integerDec i
strBldIdent _ (Bool b) = if b then string7 "true" else string7 "false"
strBldIdent _ Top = string7 "_"
strBldIdent _ Null = string7 "null"
strBldIdent ident (Struct (StructValue ols fds _ _)) =
  structBld ident (map (\label -> (label, fds Map.! label)) ols)
strBldIdent ident (Disjunction dfs djs) =
  if null dfs
    then buildList djs
    else buildList dfs
  where
    buildList xs = foldl1 (\x y -> x <> string7 " | " <> y) (map (\d -> strBldIdent ident d) xs)
strBldIdent _ (Bottom _) = string7 "_|_"
strBldIdent _ (Pending p) = case p of
  pv@(PendingValue {}) -> AST.exprBld 0 (pvExpr pv)
  (Unevaluated {})     -> string7 "_|_: Unevaluated"

structBld :: Int -> [(String, Value)] -> Builder
structBld ident xs =
  if null xs
    then string7 "{}"
    else
      char7 '{'
        <> char7 '\n'
        <> fieldsBld ident xs
        <> string7 (replicate (ident * 2) ' ')
        <> char7 '}'

fieldsBld :: Int -> [(String, Value)] -> Builder
fieldsBld _ [] = string7 ""
fieldsBld ident (x : xs) =
  f x <> fieldsBld ident xs
  where
    f (label, val) =
      string7 (replicate ((ident + 1) * 2) ' ')
        <> string7 label
        <> string7 ": "
        <> strBldIdent (ident + 1) val
        <> char7 '\n'
