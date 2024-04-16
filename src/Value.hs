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
    DelayConstraint (..),
    TreeCursor,
    TreeNode (..),
    TNUnaryOp (..),
    Runtime,
    bindEval,
    delayBinaryOp,
    delayUnaryOp,
    dump,
    emptyStruct,
    exprIO,
    getTemp,
    hasConcreteTemp,
    isValueAtom,
    isValueConcrete,
    isValueConstraint,
    isValuePending,
    isValueStub,
    mergeArgs,
    mkRef,
    mkReference,
    pathFromTC,
    popScope,
    prettyRevDeps,
    pushScope,
    searchUpVar,
    vToE,
    insertTCSV,
    insertTCList,
    insertTCUnaryOp,
    insertTCBinaryOp,
    insertTCLeafValue,
    tcFromSV,
    getValueTCPath,
    putValueTCPath,
    propRootTC,
    goUpTC,
  )
where

import qualified AST
import Control.Monad.Except (MonadError, runExcept, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger
  ( MonadLogger,
    logDebugN,
    runStderrLoggingT,
  )
import Control.Monad.State.Strict
  ( MonadState,
    evalStateT,
    get,
    gets,
    modify,
    put,
  )
import Data.List (intercalate, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust, isNothing)
import qualified Data.Set as Set
import Data.Text (pack)
import Debug.Trace
import Path
import Text.Printf (printf)

svFromVal :: Value -> Maybe StructValue
svFromVal (Struct sv) = Just sv
svFromVal _ = Nothing

dump :: (MonadLogger m) => String -> m ()
dump = logDebugN . pack

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
  | Constraint DelayConstraint
  | -- Stub is used as placeholder inside a struct. It is like Top. The actual value will be guaranteed to be evaluated.
    Stub

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

hasConcreteTemp :: Value -> Bool
hasConcreteTemp (Pending pv) = isValueConcrete (pvTemp pv)
hasConcreteTemp _ = False

getTemp :: (MonadError String m) => Value -> m Value
getTemp (Pending pv) = return $ pvTemp pv
getTemp _ = throwError "getTemp: value is not pending"

isValueStub :: Value -> Bool
isValueStub (Stub {}) = True
isValueStub _ = False

isValueConstraint :: Value -> Bool
isValueConstraint (Constraint _) = True
isValueConstraint _ = False

data StructValue = StructValue
  { -- svLabels is an ordered list of labels, based on the order of insertion in the original struct.
    svLabels :: [String],
    svFields :: Map.Map String Value,
    svVars :: Set.Set String,
    -- svConcretes is a set of labels that are guaranteed to be concrete.
    svConcretes :: Set.Set String
  }

instance Show StructValue where
  show (StructValue ols fds _ concretes) =
    printf
      "SV{ls: %s, fs: %s, cs: %s}"
      (show ols)
      (show (Map.toAscList fds))
      (show (Set.toAscList concretes))

insertSVField :: StructValue -> String -> Value -> StructValue
insertSVField sv label val =
  if Map.member label (svFields sv)
    then sv {svFields = Map.insert label val (svFields sv)}
    else
      let newLabels = svLabels sv ++ [label]
          newFields = Map.insert label val (svFields sv)
          newConcretes = if isValueConcrete val then Set.insert label (svConcretes sv) else svConcretes sv
       in sv {svLabels = newLabels, svFields = newFields, svConcretes = newConcretes}

-- | For now we don't compare IDs and Concrete fields.
instance Eq StructValue where
  (==) (StructValue ols1 fields1 _ _) (StructValue ols2 fields2 _ _) =
    ols1 == ols2 && fields1 == fields2

type Runtime m = (MonadError String m, MonadState Context m, MonadLogger m)

type EvalMonad a = forall m. (Runtime m) => m a

-- | Evaluator is a function that takes a list of tuples values and their paths and returns a value.
type Evaluator = [(Path, Value)] -> EvalMonad Value

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
    -- It should not be Constraint either because we only need to validate the constraint once. Thus referencing a
    -- constraint is not necessary.
    pvTemp :: Value,
    pvExpr :: AST.Expression
  }

instance Show PendingValue where
  show (PendingValue p d a _ t e) =
    printf
      "P{p: %s, deps: %s, args: %s, temp: %s, expr: %s}"
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

-- | Once created, the DelayConstaint can not be simplified to an atom because even though the atom is temporarily bound
-- by the constraint in the pending value, the constraint can be changed.
data DelayConstraint = DelayConstraint
  { dcPath :: Path,
    dcAtom :: Value,
    dcPend :: PendingValue,
    -- dcUnify is needed to avoid the circular dependency.
    dcUnify :: forall m. (Runtime m) => Value -> Value -> m Value
  }

instance Show DelayConstraint where
  show (DelayConstraint p a pv _) =
    printf "DC{p:%s, atom: %s, pend: %s}" (show p) (show a) (show pv)

instance Eq DelayConstraint where
  (==) (DelayConstraint p1 a1 pv1 _) (DelayConstraint p2 a2 pv2 _) = p1 == p2 && a1 == a2 && pv1 == pv2

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
-- The new pending value will inherit the dependencies of the original value, but also have new modified dependencies.
-- Parameters:
--  path is the path to the current expression that contains the selector.
--  expr is the expression that contains the selector.
--  valPath is the path to the referenced value.
--  val is the referenced value.
--  For example,
--  { a: b: x.y, x: y: 42 }
--  Even if the reference is "y", the expr should be "x.y".
mkRef :: (Runtime m) => (Path, AST.Expression) -> (Path, Value) -> m Value
mkRef _ (_, val)
  | isValueAtom val = return val
mkRef (ePath, expr) (origPath, origVal) = case origVal of
  Stub ->
    if origPath == ePath
      then do
        dump $ printf "mkRef: epath: %s, self cycle detected" (show ePath)
        return Top
      else do
        dump $ printf "mkRef: epath: %s, %s is stub" (show ePath) (show origPath)
        refValue Stub
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
        refValue Stub
  _ -> do
    dump $ printf "mkRef: epath: %s, references regular val: %s" (show ePath) (show origVal)
    refValue origVal
  where
    checkCycle :: (Runtime m) => (Path, Path) -> m Bool
    checkCycle (src, dst) = do
      revDeps <- gets ctxReverseDeps
      -- we have to reverse the new edge because the graph is reversed.
      return $ depsHasCycle ((dst, src) : Map.toList revDeps)

    -- refValue creates a pending value that depends on the value of the origPath.
    refValue :: (Runtime m) => Value -> m Value
    refValue orig = do
      modify (\ctx -> ctx {ctxReverseDeps = Map.insert origPath ePath (ctxReverseDeps ctx)})
      -- TODO: fix the expr
      let v = mkReference expr ePath origPath orig
      dump $ printf "mkRef: epath: %s, pending value created: %s" (show ePath) (show v)
      return v

-- | Bind a pending value to a function "f" and generate a new value.
-- For example, { a: b: !x }, or { a: b: x.y.z }.
-- If x is not evaluated or not concrete, the result is pending. For the later case, the expr is the AST of x.y.z.
delayUnaryOp ::
  (Runtime m) => AST.Expression -> (Value -> EvalMonad Value) -> PendingValue -> m Value
delayUnaryOp expr f pv =
  return . Pending $
    pv
      { pvEvaluator = bindEval (pvEvaluator pv) f,
        pvTemp = Stub,
        pvExpr = expr
      }

-- | Bind two pending values to a function "bin" and generate a new value.
-- For example, { a: b: x+y }
-- x and y must have the same path.
-- Or, { a: b: x & y }
-- x and y are not required to be concrete.
delayBinaryOp ::
  (Runtime m) => AST.BinaryOp -> (Value -> Value -> EvalMonad Value) -> PendingValue -> PendingValue -> m Value
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
          Stub
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

-- addBlock :: (Runtime m) => Path -> StructValue -> m ()
-- addBlock path sv = do
--   block <- gets ctxCurBlock
--   goToScope block path >>= \case
--     Nothing -> throw $ printf "addBlock: scope is not found, path: %s" (show path)
--     Just scope -> do
--       let lastSelector = fromJust $ lastSel path
--       modify $ \ctx -> ctx {ctxCurBlock = propagateBack

-- popBlock :: (Runtime m) => m ()
-- popBlock = do
--   ctx@(Context block _) <- get
--   case goUp block of
--     Just newBlock -> put $ ctx {ctxCurBlock = newBlock}
--     Nothing -> put $ ctx {ctxCurBlock = (emptyStruct, [])}

-- searchUpVar :: String -> TreeCursor -> Maybe (Path, Value)
-- searchUpVar var = go
--   where
--     go :: TreeCursor -> Maybe (Path, Value)
--     go (sv, []) = case Map.lookup var (svFields sv) of
--       Just v -> Just (Path [StringSelector var], v)
--       Nothing -> Nothing
--     go cursor@(sv, _) =
--       case Map.lookup var (svFields sv) of
--         Just v -> Just (appendSel (StringSelector var) (pathFromTC cursor), v)
--         Nothing -> goUp cursor >>= go

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
  show (Constraint c) = show c
  show Stub = "S" where

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
  (==) Stub Stub = True
  (==) _ _ = False

exprIO :: (MonadIO m, MonadError String m) => Value -> m AST.Expression
-- context is irrelevant here
exprIO v = runStderrLoggingT $ evalStateT (vToE v) $ Context [] (emptyTreeScope, []) Map.empty

vToE :: (Runtime m) => Value -> m AST.Expression
vToE Top = return $ AST.litCons AST.TopLit
vToE (String s) = return $ AST.litCons (AST.StringLit (AST.SimpleStringLit s))
vToE (Int i) = return $ AST.litCons (AST.IntLit i)
vToE (Bool b) = return $ AST.litCons (AST.BoolLit b)
vToE Null = return $ AST.litCons AST.NullLit
vToE (Bottom _) = return $ AST.litCons AST.BottomLit
vToE (Struct sv) =
  let fields = Map.toList (svFields sv)
   in do
        fieldList <-
          mapM
            ( \(label, val) -> do
                e <- vToE val
                let ln = if Set.member label (svVars sv) then AST.LabelID label else AST.LabelString label
                return (AST.Label . AST.LabelName $ ln, e)
            )
            fields
        return $ AST.litCons (AST.StructLit fieldList)
vToE (Disjunction dfs djs) =
  let valList = if not $ null dfs then dfs else djs
   in do
        es <- mapM vToE valList
        return $ foldr1 (\x y -> AST.ExprBinaryOp AST.Disjunction x y) es
vToE (Pending pv) =
  if not $ isValueStub (pvTemp pv)
    then vToE (pvTemp pv)
    else return $ pvExpr pv
vToE Stub = throwError "vToE: stub value"
vToE (Constraint dc) = do
  dump $ printf "validating constraint: %s" (show dc)
  v <- dcUnify dc (dcAtom dc) (Pending (dcPend dc))
  if isValueAtom v
    then vToE (dcAtom dc)
    else throwError $ printf "vToE: constraint validation failed: %s, unify res: %s" (show dc) (show v)

-- | TreeNode represents a tree structure that contains values.
data TreeNode
  = -- | TreeScope is a struct that contains a value and a map of selectors to TreeNode.
    TNScope TNScope
  | TNList [TreeNode]
  | TNUnaryOp TNUnaryOp
  | TNBinaryOp TNBinaryOp
  | -- | TreeLeaf is a struct that contains a scalar value.
    TNLeaf Value

data TNScope = TreeScope
  { trsValue :: StructValue,
    trsSubs :: Map.Map String TreeNode
  }

data TNUnaryOp = TreeUnaryOp
  { truOp :: forall m. (Runtime m) => Value -> m Value,
    truArg :: TreeNode
  }

data TNBinaryOp = TreeBinaryOp
  { trbOp :: forall m. (Runtime m) => Value -> Value -> m Value,
    trbArgL :: TreeNode,
    trbArgR :: TreeNode
  }

showTreeIdent :: TreeNode -> Int -> String
showTreeIdent t i =
  let nextIdent = 4
      ident = (replicate i ' ')
   in case t of
        TNLeaf v -> printf "Leaf{%s}" (show v)
        TNScope tns ->
          let sv = trsValue tns
              subs = trsSubs tns
              numFieldsStr = show $ length $ svFields sv
              subsStr =
                intercalate "\n" $
                  map
                    ( \(k, v) ->
                        ( printf "%s%s: %s" (ident) (show k) (showTreeIdent v (i + nextIdent))
                        )
                    )
                    (Map.toList subs)
           in if null subs
                then printf "Scope{n: %s, s: []}" numFieldsStr
                else
                  printf "Scope{n: %s, s: %s}" numFieldsStr ("[\n" ++ subsStr ++ "\n]")
        TNList vs ->
          let subsStr = intercalate "\n" $ map (\v -> showTreeIdent v (i + nextIdent)) vs
           in if null vs
                then printf "(List, [])"
                else
                  printf "(List, %s)" ("[\n" ++ subsStr ++ "\n]")
        TNUnaryOp op ->
          let arg = truArg op
              argStr = showTreeIdent arg (i + nextIdent)
           in printf "Unary{%s}" argStr
        TNBinaryOp op ->
          let argL = trbArgL op
              argR = trbArgR op
              argLStr = showTreeIdent argL (i + nextIdent)
              argRStr = showTreeIdent argR (i + nextIdent)
           in printf "BinaryOp{L: %s, R: %s}" argLStr argRStr

showTreeType :: TreeNode -> String
showTreeType t = case t of
  TNLeaf _ -> "Leaf"
  TNScope {} -> "Scope"
  TNList {} -> "List"
  TNUnaryOp {} -> "UnaryOp"
  TNBinaryOp {} -> "BinaryOp"

instance Show TreeNode where
  show tree = showTreeIdent tree 2

emptyTreeScope :: TreeNode
emptyTreeScope = TNScope $ TreeScope {trsValue = emptyStruct, trsSubs = Map.empty}

-- | The StructValue should only have one level of children.
mkTreeScope :: StructValue -> TreeNode
mkTreeScope sv =
  let subs = Map.fromList $ map (\(k, v) -> (k, TNLeaf v)) (Map.toList (svFields sv))
   in TNScope $ TreeScope {trsValue = sv, trsSubs = subs}

mkTreeList :: [Value] -> TreeNode
mkTreeList vs = TNList $ map TNLeaf vs

-- | Get the value of the root of the tree.
valueOfTreeNode :: TreeNode -> Maybe Value
valueOfTreeNode t = case t of
  TNLeaf v -> Just v
  TNScope s -> Just (Struct (trsValue s))
  _ -> Nothing

-- goTreePath :: TreeNode -> Path -> Maybe TreeNode
-- goTreePath t (Path []) = Just t
-- goTreePath t (Path (x : xs)) = do
--   nextSel <- goTreeSel t x
--   goTreePath nextSel (Path xs)

-- | Update the tree node with the given value.
updateTreeNode :: (MonadError String m) => TreeNode -> Value -> m TreeNode
updateTreeNode t v = case v of
  Struct sv -> case t of
    TNScope s -> return $ TNScope $ TreeScope {trsValue = sv, trsSubs = trsSubs s}
    _ -> throwError $ printf "updateTreeNode: cannot set non-struct value to non-TreeScope, value: %s" (show v)
  _ -> case t of
    TNLeaf _ -> return $ TNLeaf v
    _ -> throwError $ printf "updateTreeNode: cannot set non-struct value to non-TreeLeaf, value: %s" (show v)

-- | Insert a sub-tree to the tree node with the given selector.
-- Returns the updated tree node.
insertSubTree :: (MonadError String m) => TreeNode -> Selector -> TreeNode -> m TreeNode
insertSubTree root sel sub = case sel of
  StringSelector s -> case root of
    TNScope scope ->
      let parSV = insertSVField (trsValue scope) s (Struct (trsValue scope))
       in return $ TNScope $ TreeScope {trsValue = parSV, trsSubs = Map.insert s sub (trsSubs scope)}
    _ ->
      throwError $
        printf
          "insertSubTree: cannot insert sub %s to non-TreeScope %s, selector: %s"
          (show sub)
          (show root)
          (show sel)
  ListSelector i -> case root of
    TNList vs -> return $ TNList $ take i vs ++ [sub] ++ drop (i + 1) vs
    _ -> throwError $ printf "insertSubTree: cannot insert sub to non-TreeList, selector: %s" (show sel)
  UnaryOpSelector -> case root of
    TNUnaryOp op -> return $ TNUnaryOp $ TreeUnaryOp {truOp = truOp op, truArg = sub}
    _ -> throwError $ printf "insertSubTree: cannot insert sub to non-TreeUnaryOp, selector: %s" (show sel)
  BinOpSelector dr -> case root of
    TNBinaryOp op -> case dr of
      L -> return $ TNBinaryOp $ TreeBinaryOp {trbOp = trbOp op, trbArgL = sub, trbArgR = (trbArgR op)}
      R -> return $ TNBinaryOp $ TreeBinaryOp {trbOp = trbOp op, trbArgL = (trbArgL op), trbArgR = sub}
    _ -> throwError $ printf "insertSubTree: cannot insert sub to %s, selector: %s" (showTreeType root) (show sel)

-- step down the tree with the given selector.
-- This should only be used by TreeCursor.
goTreeSel :: TreeNode -> Selector -> Maybe TreeNode
goTreeSel t sel = case sel of
  StringSelector s -> case t of
    TNScope scope -> Map.lookup s (trsSubs scope)
    _ -> Nothing
  ListSelector i -> case t of
    TNList vs -> vs !? i
    _ -> Nothing
  UnaryOpSelector -> case t of
    TNUnaryOp op -> Just (truArg op)
    _ -> Nothing
  BinOpSelector dr -> case t of
    TNBinaryOp op -> case dr of
      L -> Just (trbArgL op)
      R -> Just (trbArgR op)
    _ -> Nothing

-- updateTreePathValue :: (MonadError String m) => TreeNode -> Path -> Value -> m TreeNode
-- updateTreePathValue t path v = case goTreePath t path of
--   Just node -> updateTreeNode node v
--   Nothing -> throwError $ printf "updateTreePathValue: path not found: %s" (show path)

-- | TreeCrumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type TreeCrumb = (Selector, TreeNode)

showTreeCrumb :: TreeCrumb -> String
showTreeCrumb (sel, t) = printf "(%s, %s)" (show sel) (showTreeType t)

-- | TreeCursor is a pair of a value and a list of crumbs.
-- For example,
-- {
--   a: {
--     b: {
--       c: 42
--     } // struct_c
--   } // struct_b
-- } // struct_a
-- Suppose the cursor is at the struct that contains the value 42. The cursor is
-- (struct_c, [("b", struct_b), ("a", struct_a)]).
type TreeCursor = (TreeNode, [TreeCrumb])

showTreeCursor :: TreeCursor -> String
showTreeCursor (t, cs) = printf "(%s, [%s])" (showTreeType t) (intercalate ", " (map showTreeCrumb cs))

-- | Go up the tree cursor and return the new cursor.
goUpTC :: TreeCursor -> Maybe TreeCursor
goUpTC (_, []) = Nothing
goUpTC (_, (_, v) : vs) = Just (v, vs)

goDownTCPath :: TreeCursor -> Path -> Maybe TreeCursor
goDownTCPath tc (Path sels) = go (reverse sels) tc
  where
    go :: [Selector] -> TreeCursor -> Maybe TreeCursor
    go [] cursor = Just cursor
    go (x : xs) cursor = do
      nextCur <- goDownTCSel x cursor
      go xs nextCur

-- | Go down the TreeCursor with the given selector and return the new cursor.
goDownTCSel :: Selector -> TreeCursor -> Maybe TreeCursor
goDownTCSel sel (t, vs) = do
  nextTree <- goTreeSel t sel
  return (nextTree, (sel, t) : vs)

-- -- | Go down all the way to the bottom. If no struct exists along the path, a new empty struct will be created.
-- goDownAll :: Path -> TreeCursor -> TreeCursor
-- goDownAll (Path sels) = go (reverse sels)
--   where
--     -- next creates a new cursor by going down one level.
--     next :: Selector -> TreeCursor -> TreeCursor
--     next sel (t, vs) =
--       if Map.member sel (treeSubs t)
--         then (treeSubs t Map.! sel, (sel, t) : vs)
--         else (mkEmptyTree, (sel, t) : vs)
--
--     go :: [Selector] -> TreeCursor -> TreeCursor
--     go [] cursor = cursor
--     go (x : xs) cursor = go xs (next x cursor)

-- -- | Replace the cursor value with the new struct value.
-- attachValToCur :: (MonadError String m) => Value -> TreeCursor -> m TreeCursor
-- attachValToCur
-- attach (Struct sv) (t, vs) =
--   ( t
--       { treeValue = Just (Struct sv),
--         treeSubs = Map.fromList $ map (\s -> (StringSelector s, mkEmptyTree)) (svLabels sv)
--       },
--     vs
--   )
-- attach v (t, vs) = (t {treeValue = Just v}, vs)

-- -- | Search the var upwards in the tree. Returns the path to the value and the value.
-- searchUpVar :: String -> TreeCursor -> Maybe (Path, Value)
-- searchUpVar var = go
--   where
--     go :: TreeCursor -> Maybe (Path, Value)
--     go (sv, []) = case Map.lookup var (svFields sv) of
--       Just v -> Just (Path [StringSelector var], v)
--       Nothing -> Nothing
--     go cursor@(sv, _) =
--       case Map.lookup var (svFields sv) of
--         Just v -> Just (appendSel (StringSelector var) (pathFromTC cursor), v)
--         Nothing -> goUp cursor >>= go

pathFromTC :: TreeCursor -> Path
pathFromTC (_, crumbs) = Path . reverse $ go crumbs []
  where
    go :: [TreeCrumb] -> [Selector] -> [Selector]
    go [] acc = acc
    go ((n, _) : cs) acc = go cs (n : acc)

-- goToBlock :: TreeCursor -> Path -> Maybe TreeCursor
-- goToBlock block p =
--   -- we have to propagate the changes to the parent blocks first.
--   let rootBlock = propRootTC block
--    in goDownTCPath p rootBlock

-- | propUp propagates the changes made to the tip of the block to the parent block.
-- The structure of the tree is not changed.
propUpTC :: (MonadError String m) => TreeCursor -> m TreeCursor
propUpTC (t, []) = return (t, [])
propUpTC (t, (sel, pt) : cs) = case sel of
  StringSelector s -> case t of
    TNScope scope -> insertParScope pt s (Struct (trsValue scope))
    TNList {} -> throwError "unimplemented"
    TNUnaryOp {} -> insertParScope pt s Top -- TODO: Pending
    TNBinaryOp {} -> insertParScope pt s Top -- TODO: Pending
    TNLeaf v -> insertParScope pt s v
  ListSelector i -> case pt of
    TNList vs -> return (TNList $ take i vs ++ [t] ++ drop (i + 1) vs, cs)
    _ -> throwError insertErrMsg
  UnaryOpSelector -> case pt of
    TNUnaryOp op ->
      return (TNUnaryOp $ TreeUnaryOp {truOp = truOp op, truArg = t}, cs)
    _ -> throwError insertErrMsg
  BinOpSelector dr -> case dr of
    L -> case pt of
      TNBinaryOp op ->
        return
          ( TNBinaryOp $ TreeBinaryOp {trbOp = trbOp op, trbArgL = t, trbArgR = trbArgR op},
            cs
          )
      _ -> throwError insertErrMsg
    R -> case pt of
      TNBinaryOp op ->
        return
          ( TNBinaryOp $ TreeBinaryOp {trbOp = trbOp op, trbArgL = trbArgL op, trbArgR = t},
            cs
          )
      _ -> throwError insertErrMsg
  where
    insertParScope :: (MonadError String m) => TreeNode -> String -> Value -> m TreeCursor
    insertParScope par s v = case par of
      TNScope parScope ->
        let newParSV = insertSVField (trsValue parScope) s v
            newParNode = TreeScope {trsValue = newParSV, trsSubs = Map.insert s t (trsSubs parScope)}
         in return (TNScope newParNode, cs)
      _ -> throwError insertErrMsg

    insertErrMsg :: String
    insertErrMsg =
      printf "propUpTC: cannot insert child %s to parent %s, selector: %s" (showTreeType t) (showTreeType pt) (show sel)

-- | propRootTC propagates the changes to the parent blocks until the root block.
-- It returns the root block.
propRootTC :: (MonadError String m) => TreeCursor -> m TreeCursor
propRootTC (t, []) = return (t, [])
propRootTC tc = propUpTC tc >>= propRootTC

getValueTCPath :: TreeCursor -> Path -> Maybe Value
getValueTCPath tc p = case runExcept (propRootTC tc) of
  Left _ -> Nothing
  Right rootTC -> do
    targetTC <- goDownTCPath rootTC p
    valueOfTreeNode $ fst targetTC

-- | Put the value to the tree cursor at the given path.
-- Returns the udpated root tree cursor.
putValueTCPath :: (MonadError String m) => TreeCursor -> Path -> Value -> m TreeCursor
putValueTCPath tc p v = do
  rootTC <- propRootTC tc
  case goDownTCPath rootTC p of
    Nothing -> throwError $ printf "putValueTCPath: path not found: %s" (show p)
    Just ttc -> do
      updated <- updateTreeNode (fst ttc) v
      propRootTC (updated, snd ttc)

-- | Create a new tree cursor from a struct value.
-- It is used to create a new tree cursor from scratch.
tcFromSV :: StructValue -> TreeCursor
tcFromSV sv = (mkTreeScope sv, [])

insertTCSub :: (MonadError String m) => Selector -> TreeNode -> TreeCursor -> m TreeCursor
insertTCSub sel sub (t, cs) = do
  u <- insertSubTree t sel sub
  let leaf = (sub, (sel, u) : cs)
      leafPath = pathFromTC leaf
  rootTC <- (propRootTC leaf)
  let m = goDownTCPath rootTC leafPath
  case ( trace
           ( printf
               "insertTCSub sel: %s, sub:\n%s, leaf: %s, root: %s, rootVal: %s"
               (show sel)
               (show sub)
               (showTreeCursor leaf)
               (show rootTC)
               (show $ fromJust (valueOfTreeNode $ fst rootTC))
           )
           m
       ) of
    Nothing -> throwError $ printf "insertTCSub: path not found: %s" (show leafPath)
    Just ttc -> return ttc

-- | Insert a struct value to the tree and return the new cursor that contains the newly inserted value.
insertTCSV :: (MonadError String m) => Selector -> StructValue -> TreeCursor -> m TreeCursor
insertTCSV sel sv tc = let sub = (mkTreeScope sv) in insertTCSub sel sub tc

insertTCList :: (MonadError String m) => Selector -> [Value] -> TreeCursor -> m TreeCursor
insertTCList sel vs tc = let sub = mkTreeList vs in insertTCSub sel sub tc

insertTCUnaryOp ::
  (MonadError String m) => Selector -> (Value -> EvalMonad Value) -> TreeCursor -> m TreeCursor
insertTCUnaryOp sel f tc =
  let sub = TNUnaryOp $ TreeUnaryOp {truOp = f, truArg = TNLeaf Stub}
   in insertTCSub sel sub tc

insertTCBinaryOp ::
  (MonadError String m) => Selector -> (Value -> Value -> EvalMonad Value) -> TreeCursor -> m TreeCursor
insertTCBinaryOp sel f tc =
  let sub = TNBinaryOp $ TreeBinaryOp {trbOp = f, trbArgL = TNLeaf Stub, trbArgR = TNLeaf Stub}
   in insertTCSub sel sub tc

insertTCLeafValue :: (MonadError String m) => Selector -> Value -> TreeCursor -> m TreeCursor
insertTCLeafValue sel v tc = case v of
  Struct {} -> throwError "insertTCLeafValue: cannot insert struct value to leaf"
  _ -> do
    let sub = TNLeaf v
    insertTCSub sel sub tc

-- -- | Go to the scope block that contains the value.
-- -- The path should be the full path to the value.
-- goToScope :: TreeCursor -> Path -> Maybe TreeCursor
-- goToScope cursor p = goToBlock cursor (fromJust $ initPath p)

-- | Context
data Context = Context
  { ctxScopeStack :: ScopeStack,
    -- curBlock is the current block that contains the variables.
    -- A new block will replace the current one when a new block is entered.
    -- A new block is entered when one of the following is encountered:
    -- - The "{" token
    -- - for and let clauses
    ctxValueStore :: TreeCursor,
    ctxReverseDeps :: Map.Map Path Path
  }

-- putInBlock :: (Runtime m) => TreeCursor -> Path -> Value -> m TreeCursor
-- putInBlock cursor path v = do
--   newBlock <- updateTreeNode (fst cursor) (Path []) v
--   return (newBlock, snd cursor)
--
-- -- | Get the value by the path starting from the given cursor.
-- getFromStore :: TreeCursor -> Path -> Maybe Value
-- getFromStore cursor (Path []) = valueOfTreeNode (fst cursor)
-- getFromStore cursor path = do
--   block <- goToBlock cursor path
--   valueOfTreeNode (fst block)

-- getValueFromCtx :: (MonadState Context m) => Path -> m (Maybe Value)
-- getValueFromCtx path = do
--   tc <- gets ctxValueStore
--   return $ getFromStore block path

-- let rootBlock = propRoot block
--     bottomBlock = goDownAll path topBlock
--     holder = fromJust $ goUp bottomBlock
--     updateVal :: (MonadError String m) => Selector -> Value -> TreeCursor -> m TreeCursor
--     updateVal (StringSelector name) newVal (sv, vs) =
--       let newFields = Map.insert name newVal (svFields sv)
--           newConcrSet =
--             if isValueConcrete newVal
--               then Set.insert name (svConcretes sv)
--               else svConcretes sv
--        in return (sv {svFields = newFields, svConcretes = newConcrSet}, vs)
--  in updateVal (fromJust $ lastSel path) val holder

-- | Put value to the context at the given path. The ctx is updated to the root.
-- However, it does not create a new block.
-- putValueInCtx :: (Runtime m) => Path -> Value -> m ()
-- putValueInCtx path val = do
--   ctx <- get
--   dump $ printf "putValueInCtx: orig block: %s" (show $ ctxValueStore ctx)
--   newBlock <- putInBlock (ctxValueStore ctx) path val
--   dump $ printf "putValueInCtx: path: %s, value: %s" (show path) (show val)
--   put $ ctx {ctxValueStore = propRootTC newBlock}
--   ctx2 <- get
--   dump $ printf "putValueInCtx: new block: %s" (show (ctxValueStore ctx2))
prettyRevDeps :: Map.Map Path Path -> String
prettyRevDeps m =
  let p = intercalate ", " $ map (\(k, v) -> printf "(%s->%s)" (show k) (show v)) (Map.toList m)
   in "[" ++ p ++ "]"

type ScopeStack = [Scope]

data Scope = Scope
  { scopePath :: Path,
    scopeVars :: Set.Set String
  }

pushScope :: (MonadError String m) => Path -> Set.Set String -> ScopeStack -> m ScopeStack
pushScope path vars [] = return [Scope path vars]
pushScope path vars (s : ss) = case relPath (scopePath s) path of
  Just (Path relp) ->
    if length relp == 1
      then return $ Scope path vars : s : ss
      else throwError "pushScope: path is not a child of the current scope"
  Nothing ->
    throwError $
      printf
        "pushScope: path is not a child of the current scope: %s, %s"
        (show path)
        (show (scopePath s))

popScope :: (MonadError String m) => ScopeStack -> m ScopeStack
popScope [] = throwError "popScope: empty stack"
popScope (_ : ss) = return ss

searchUpVar :: String -> ScopeStack -> Maybe Path
searchUpVar var = go
  where
    go :: ScopeStack -> Maybe Path
    go [] = Nothing
    go (s : ss) =
      if Set.member var (scopeVars s)
        then Just (scopePath s)
        else go ss
