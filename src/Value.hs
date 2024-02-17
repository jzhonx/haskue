{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Value
  ( Context (..),
    EvalMonad,
    Evaluator,
    Value (..),
    PendingValue (..),
    StructValue (..),
    TreeCursor,
    emptyStruct,
    mkUnevaluated,
    mkCycleBegin,
    mkPending,
    putValueInCtx,
    getValueFromCtx,
    strBld,
    isValueConcrete,
    isValuePending,
    bindEval,
    mergeArgs,
    goToScope,
    searchUpVar,
    toExpr,
  )
where

import qualified AST
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (MonadState, get, put)
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

isValuePending :: Value -> Bool
isValuePending (Pending _) = True
isValuePending _ = False

data StructValue = StructValue
  { svLabels :: [String],
    svFields :: Map.Map String Value,
    svVars :: Set.Set String,
    svConcretes :: Set.Set String
  }

instance Show StructValue where
  show (StructValue ols fds _ concretes) =
    printf "{labels: %s, fields: %s, concretes: %s }" (show ols) (show fds) (show concretes)

-- | For now we don't compare IDs and Concrete fields.
instance Eq StructValue where
  (==) (StructValue ols1 fields1 _ _) (StructValue ols2 fields2 _ _) =
    ols1 == ols2 && fields1 == fields2

data PendingValue
  = PendingValue
      { -- pvPath is the path to the pending value.
        pvPath :: Path,
        -- depEdges is a list of paths to the unresolved immediate references.
        -- path should be the full path.
        -- The edges are primarily used to detect cycles.
        -- the first element of the tuple is the path to a pending value.
        -- the second element of the tuple is the path to a value that the pending value depends on.
        pvDeps :: [(Path, Path)],
        pvArgs :: [(Path, Value)],
        -- evaluator is a function that takes a list of values and returns a value.
        -- The order of the values in the list is the same as the order of the paths in deps.
        pvEvaluator :: Evaluator,
        pvExpr :: AST.Expression
      }
  | Unevaluated
      { uePath :: Path,
        ueExpr :: AST.Expression
      }
  | -- CycleBegin is needed because once there is a concrete value unified with the identifier, the identifier is no
    -- longer pending. All dependent values should be updated to reflect the change.
    CycleBegin
      { cbPath :: Path,
        cbExpr :: AST.Expression
      }

instance Show PendingValue where
  show (PendingValue p d a _ e) =
    printf "(Pending, path: %s, deps: %s, args: %s, expr: %s)" (show p) prettyDeps (show a) (AST.exprStr e)
    where
      prettyDeps = intercalate ", " $ map (\(p1, p2) -> printf "(%s->%s)" (show p1) (show p2)) d
  show (Unevaluated p e) = printf "(Unevaluated, path: %s, expr: %s)" (show p) (AST.exprStr e)
  show (CycleBegin p e) = printf "(CycleBegin, begin: %s, expr: %s)" (show p) (AST.exprStr e)

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

mkUnevaluated :: Path -> AST.Expression -> Value
mkUnevaluated p e = Pending $ Unevaluated p e

mkCycleBegin :: Path -> AST.Expression -> Value
mkCycleBegin p e = Pending $ CycleBegin p e

-- | Creates a new simple pending.
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
putValueInCtx :: (MonadError String m, MonadState Context m) => Path -> Value -> m ()
putValueInCtx path val = do
  ctx@(Context block _) <- get
  newBlock <- locateSetValue block path val
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
  (Unevaluated {}) -> string7 "_|_: Unevaluated"
  (CycleBegin {}) -> string7 "_"

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

toExpr :: Value -> Maybe AST.Expression
toExpr Top = Just $ AST.litCons AST.TopLit
toExpr (String s) = Just $ AST.litCons (AST.StringLit (AST.SimpleStringLit s))
toExpr (Int i) = Just $ AST.litCons (AST.IntLit i)
toExpr (Bool b) = Just $ AST.litCons (AST.BoolLit b)
toExpr Null = Just $ AST.litCons AST.NullLit
toExpr (Bottom _) = Just $ AST.litCons AST.BottomLit
toExpr (Struct _) = Nothing
toExpr (Disjunction _ _) = Nothing
toExpr (Pending _) = Nothing
