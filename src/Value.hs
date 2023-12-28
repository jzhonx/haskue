{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

module Value where

import           Control.Monad.Except       (ExceptT, MonadError, runExceptT,
                                             throwError)
import           Control.Monad.State.Strict (MonadState, State, get, put,
                                             runState)
import           Data.ByteString.Builder    (Builder, char7, integerDec,
                                             string7)
import qualified Data.Map.Strict            as Map
import qualified Data.Set                   as Set

-- TODO: IntSelector
data Selector = StringSelector String deriving (Eq, Ord, Show)

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

data Context = Context
  { -- path is the path to the current expression.
    -- the path should be the full path.
    path      :: Path,
    -- curBlock is the current block that contains the variables.
    -- A new block will replace the current one when a new block is entered.
    -- A new block is entered when one of the following is encountered:
    -- - The "{" token
    -- - for and let clauses
    curBlockZ :: Zipper
  }

type EvalMonad a = forall m. (MonadError String m, MonadState Context m) => m a

type Evaluator = [Value] -> EvalMonad Value

type ValueStore = Map.Map Path Value

data Value
  = Top
  | String String
  | Int Integer
  | Bool Bool
  | Struct
      { orderedLabels :: [String],
        fields        :: Map.Map String Value,
        identifiers   :: Set.Set String
      }
  | Disjunction
      { defaults  :: [Value],
        disjuncts :: [Value]
      }
  | Null
  | Bottom String
  | Pending
      { -- dep is a list of paths to the unresolved references.
        -- path should be the full path.
        -- the first element of the tuple is the variable path.
        -- the second element of the tuple is the reference path.
        deps      :: [(Path, Path)],
        -- evaluator is a function that takes a list of values and returns a value.
        -- The order of the values in the list is the same as the order of the paths in deps.
        evaluator :: Evaluator
      }
  | Unevaluated

-- binFunc is used to evaluate a binary function with two arguments.
binFunc :: (MonadError String m, MonadState Context m) => (Value -> Value -> EvalMonad Value) -> Value -> Value -> m Value
binFunc bin v1@(Pending {}) v2@(Pending {}) = unaFunc (\x -> unaFunc (bin x) v2) v1
binFunc bin v1@(Pending {}) v2 = unaFunc (`bin` v2) v1
binFunc bin v1 v2@(Pending {}) = unaFunc (bin v1) v2
binFunc bin v1 v2 = bin v1 v2

-- unaFunc is used to evaluate a unary function.
-- The first argument is the function that takes the evaluated value (inclduing pending) and returns a value.
unaFunc :: (MonadError String m, MonadState Context m) => (Value -> EvalMonad Value) -> Value -> m Value
unaFunc una (Pending d ev) = return $ Pending d (bindEval ev una)
unaFunc una v              = una v

bindEval :: Evaluator -> (Value -> EvalMonad Value) -> Evaluator
bindEval evalf f vs = evalf vs >>= f

instance Show Value where
  show (String s) = s
  show (Int i) = show i
  show (Bool b) = show b
  show Top = "_"
  show Null = "null"
  show (Struct ols fds _) = "{ labels:" ++ show ols ++ ", fields: " ++ show fds ++ "}"
  show (Disjunction dfs djs) = "Disjunction: " ++ show dfs ++ ", " ++ show djs
  show (Bottom msg) = "_|_: " ++ msg
  show Pending {} = "_|_"
  show Unevaluated = "_|_"

instance Eq Value where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) (Struct orderedLabels1 edges1 _) (Struct orderedLabels2 edges2 _) =
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
buildCUEStr' ident (Struct ols fds _) =
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

-- | Crumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type Crumb = (Selector, Value)

type Zipper = (Value, [Crumb])

goUp :: Zipper -> Maybe Zipper
goUp (_, [])           = Nothing
goUp (_, (_, v') : vs) = Just (v', vs)

goTo :: Selector -> Zipper -> Maybe Zipper
goTo n@(StringSelector name) (val@(Struct _ fields' _), vs) = do
  val' <- Map.lookup name fields'
  return (val', (n, val) : vs)
goTo _ (_, _) = Nothing

attach :: Value -> Zipper -> Zipper
attach val (_, vs) = (val, vs)

addSubZipper :: Selector -> Value -> Zipper -> Zipper
addSubZipper sel new (old, vs) = (new, (sel, old) : vs)

searchUp :: String -> Zipper -> Maybe Value
searchUp name (Struct _ fields' _, []) = Map.lookup name fields'
searchUp name z@(Struct _ fields' _, _) =
  case Map.lookup name fields' of
    Just v -> Just v
    Nothing -> do
      z' <- goUp z
      searchUp name z'
searchUp _ _ = Nothing
