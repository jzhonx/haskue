{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Tree
  ( Context (..),
    EvalEnv,
    EvalMonad,
    Runtime,
    TNUnaryOp (..),
    TreeCursor,
    TreeNode (..),
    Value (..),
    TNDisj (..),
    TNLeaf (..),
    TNScope (..),
    TNBinaryOp (..),
    TNLink (..),
    TNConstraint (..),
    TNRefCycle (..),
    Config (..),
    dump,
    leafFromTNConst,
    exprIO,
    finalizeTC,
    goDownTCPath,
    goDownTCSel,
    goUpTC,
    insertTCBinaryOp,
    insertTCDot,
    insertTCLeafValue,
    insertTCLink,
    insertTCList,
    insertTCScope,
    insertTCUnaryOp,
    insertTCDisj,
    leaveCurNode,
    mergeArgs,
    mkTreeLeaf,
    mkTreeDisj,
    mkTreeConstraint,
    pathFromTC,
    prettyRevDeps,
    propRootEvalTC,
    pushNewNode,
    searchTCVar,
    vToE,
    showTreeCursor,
    isValueNode,
    buildASTExpr,
    emptyTNScope,
    refCycleToConstraint,
  )
where

import qualified AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, runExcept, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger
  ( MonadLogger,
    logDebugN,
    runStderrLoggingT,
  )
import Control.Monad.Reader (MonadReader, ask)
import Control.Monad.State.Strict
  ( MonadState,
    evalStateT,
    gets,
    modify,
  )
import Data.ByteString.Builder
  ( Builder,
    char7,
    integerDec,
    string7,
    toLazyByteString,
  )
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.Either (fromRight)
import Data.List (intercalate, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, listToMaybe)
import qualified Data.Set as Set
import Data.Text (pack)
import Path
import Text.Printf (printf)

dump :: (MonadLogger m) => String -> m ()
dump = logDebugN . pack

data Value
  = Top
  | String String
  | Int Integer
  | Bool Bool
  | Null
  | Bottom String

type EvalEnv m = (MonadError String m, MonadLogger m, MonadReader Config m)

type Runtime m = (EvalEnv m, MonadState Context m)

data Config = Config
  { cfUnify :: forall m. (EvalEnv m) => TreeNode -> TreeNode -> m TreeNode
  }

type EvalMonad a = forall m. (EvalEnv m) => m a

-- TODO: merge same keys handler
-- two embeded structs can have same keys
-- mergeStructValues :: StructValue -> StructValue -> StructValue
-- mergeStructValues (StructValue ols1 fields1 ids1 atoms1) (StructValue ols2 fields2 ids2 atoms2) =
--   StructValue (ols1 ++ ols2) (Map.union fields1 fields2) (Set.union ids1 ids2) (isAtom1 && isAtom2)

mergeArgs :: [(Path, Value)] -> [(Path, Value)] -> [(Path, Value)]
mergeArgs xs ys = Map.toList $ Map.fromList (xs ++ ys)

-- | Show is only used for debugging.
instance Show Value where
  show (String s) = s
  show (Int i) = show i
  show (Bool b) = show b
  show Top = "_"
  show Null = "null"
  show (Bottom msg) = "_|_: " ++ msg

instance Eq Value where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) (Bottom _) (Bottom _) = True
  (==) Top Top = True
  (==) Null Null = True
  (==) _ _ = False

exprIO :: (MonadIO m, MonadError String m) => Value -> m AST.Expression
-- context is irrelevant here
exprIO v = runStderrLoggingT $ evalStateT (vToE v) $ Context (TNScope emptyTNScope, []) Map.empty

vToE :: (MonadError String m) => Value -> m AST.Expression
vToE Top = return $ AST.litCons AST.TopLit
vToE (String s) = return $ AST.litCons (AST.StringLit (AST.SimpleStringLit s))
vToE (Int i) = return $ AST.litCons (AST.IntLit i)
vToE (Bool b) = return $ AST.litCons (AST.BoolLit b)
vToE Null = return $ AST.litCons AST.NullLit
vToE (Bottom _) = return $ AST.litCons AST.BottomLit

class ValueNode a where
  isValueNode :: a -> Bool

class BuildASTExpr a where
  buildASTExpr :: a -> AST.Expression

-- | TreeNode represents a tree structure that contains values.
data TreeNode
  = TNRoot TreeNode
  | -- | TreeScope is a struct that contains a value and a map of selectors to TreeNode.
    TNScope TNScope
  | TNList [TreeNode]
  | TNDisj TNDisj
  | TNUnaryOp TNUnaryOp
  | TNBinaryOp TNBinaryOp
  | -- | Unless the target is a Leaf, the TNLink should not be pruned.
    TNLink TNLink
  | -- | TreeLeaf contains an atom value. (could be scalar in the future)
    TNLeaf TNLeaf
  | TNStub
  | TNConstraint TNConstraint
  | TNRefCycle TNRefCycle
  | TNRefCycleVar

instance Eq TreeNode where
  (==) (TNRoot t1) (TNRoot t2) = t1 == t2
  (==) (TNScope s1) (TNScope s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNUnaryOp o1) (TNUnaryOp o2) = o1 == o2
  (==) (TNBinaryOp o1) (TNBinaryOp o2) = o1 == o2
  (==) (TNLink l1) (TNLink l2) = l1 == l2
  (==) (TNLeaf l1) (TNLeaf l2) = l1 == l2
  (==) TNStub TNStub = True
  (==) (TNConstraint c1) (TNConstraint c2) = c1 == c2
  (==) (TNRefCycle f1) (TNRefCycle f2) = f1 == f2
  (==) TNRefCycleVar TNRefCycleVar = True
  (==) _ _ = False

instance ValueNode TreeNode where
  isValueNode n = case n of
    TNLeaf _ -> True
    TNScope _ -> True
    TNList _ -> True
    TNDisj _ -> True
    TNConstraint _ -> True
    TNRefCycle _ -> True
    _ -> False

instance BuildASTExpr TreeNode where
  buildASTExpr n = case n of
    TNLeaf l -> buildASTExpr l
    TNRoot r -> buildASTExpr r
    TNScope s -> buildASTExpr s
    TNList _ -> undefined
    TNDisj d -> buildASTExpr d
    TNLink l -> buildASTExpr l
    TNUnaryOp op -> buildASTExpr op
    TNBinaryOp op -> buildASTExpr op
    TNStub -> AST.litCons AST.BottomLit
    TNConstraint c -> buildASTExpr c
    TNRefCycle f -> buildASTExpr f
    TNRefCycleVar -> AST.litCons AST.TopLit

data TNScope = TreeScope
  { trsOrdLabels :: [String],
    trsVars :: Set.Set String,
    trsConcretes :: Set.Set String,
    trsSubs :: Map.Map String TreeNode
  }

instance Eq TNScope where
  (==) s1 s2 = trsOrdLabels s1 == trsOrdLabels s2 && trsSubs s1 == trsSubs s2

instance BuildASTExpr TNScope where
  buildASTExpr s =
    let processField :: (String, TreeNode) -> (AST.Label, AST.Expression)
        processField (label, sub) =
          ( AST.Label . AST.LabelName $
              if Set.member label (trsVars s)
                then AST.LabelID label
                else AST.LabelString label,
            buildASTExpr sub
          )
     in AST.litCons $ AST.StructLit $ map processField (Map.toList (trsSubs s))

insertScopeNode :: TNScope -> String -> TreeNode -> TNScope
insertScopeNode s label sub =
  if Map.member label (trsSubs s)
    then s {trsSubs = Map.insert label sub (trsSubs s)}
    else
      let newLabels = trsOrdLabels s ++ [label]
          newFields = Map.insert label sub (trsSubs s)
       in -- TODO: concretes
          -- newConcretes = if isValueConcrete val then Set.insert label (svConcretes sv) else svConcretes sv
          s {trsOrdLabels = newLabels, trsSubs = newFields}

data TNUnaryOp = TreeUnaryOp
  { truRep :: String,
    truExpr :: AST.UnaryExpr,
    truOp :: forall m. (EvalEnv m) => TreeNode -> m TreeNode,
    truArg :: TreeNode
  }

instance BuildASTExpr TNUnaryOp where
  buildASTExpr = AST.ExprUnaryExpr . truExpr

instance Eq TNUnaryOp where
  (==) o1 o2 = (truRep o1 == truRep o2) && (truArg o1 == truArg o2)

data TNBinaryOp = TreeBinaryOp
  { trbRep :: String,
    trbExpr :: AST.Expression,
    trbOp :: forall m. (EvalEnv m) => TreeNode -> TreeNode -> m TreeNode,
    trbArgL :: TreeNode,
    trbArgR :: TreeNode
  }

instance BuildASTExpr TNBinaryOp where
  buildASTExpr = trbExpr

instance Eq TNBinaryOp where
  (==) o1 o2 = (trbRep o1 == trbRep o2) && (trbArgL o1 == trbArgL o2) && (trbArgR o1 == trbArgR o2)

data TNLink = TreeLink
  { trlTarget :: Path,
    trlExpr :: Maybe AST.UnaryExpr
  }

instance Eq TNLink where
  (==) l1 l2 = trlTarget l1 == trlTarget l2

instance BuildASTExpr TNLink where
  buildASTExpr l = AST.ExprUnaryExpr $ fromJust $ trlExpr l

data TNLeaf = TreeLeaf
  { trfValue :: Value
  }

instance Eq TNLeaf where
  (==) (TreeLeaf v1) (TreeLeaf v2) = v1 == v2

instance BuildASTExpr TNLeaf where
  buildASTExpr (TreeLeaf v) = fromRight (AST.litCons AST.BottomLit) (runExcept $ vToE v)

mkTreeLeaf :: Value -> TreeNode
mkTreeLeaf v = TNLeaf $ TreeLeaf {trfValue = v}

data TNDisj = TreeDisj
  { trdDefaults :: [TreeNode],
    trdDisjuncts :: [TreeNode]
  }

instance Eq TNDisj where
  (==) (TreeDisj ds1 js1) (TreeDisj ds2 js2) = ds1 == ds2 && js1 == js2

instance BuildASTExpr TNDisj where
  buildASTExpr dj =
    let defaults = map buildASTExpr (trdDefaults dj)
        disjuncts = map buildASTExpr (trdDisjuncts dj)
        list = if null defaults then disjuncts else defaults
     in foldr1 (\x y -> AST.ExprBinaryOp AST.Disjunction x y) list

mkTreeDisj :: [TreeNode] -> [TreeNode] -> TreeNode
mkTreeDisj ds js = TNDisj $ TreeDisj {trdDefaults = ds, trdDisjuncts = js}

data TNConstraint = TreeConstraint
  { trcArgL :: TreeNode,
    trcArgR :: TreeNode
  }

instance Eq TNConstraint where
  (==) (TreeConstraint l1 r1) (TreeConstraint l2 r2) = l1 == l2 && r1 == r2

instance BuildASTExpr TNConstraint where
  buildASTExpr c = AST.ExprBinaryOp AST.Unify (buildASTExpr (trcArgL c)) (buildASTExpr (trcArgR c))

mkTreeConstraint :: TreeNode -> TreeNode -> TreeNode
mkTreeConstraint l r = TNConstraint $ TreeConstraint {trcArgL = l, trcArgR = r}

leafFromTNConst :: TNConstraint -> TreeNode
leafFromTNConst c = case trcArgL c of
  TNLeaf _ -> trcArgL c
  _ -> TNConstraint c

constLeafDir :: TNConstraint -> BinOpDirect
constLeafDir c = case trcArgL c of
  TNLeaf _ -> L
  _ -> R

data TNRefCycle = TreeRefCycle
  { trRcRep :: String,
    trRcForm :: TreeNode
  }

instance Eq TNRefCycle where
  (==) (TreeRefCycle r1 f1) (TreeRefCycle r2 f2) = r1 == r2 && f1 == f2

instance BuildASTExpr TNRefCycle where
  buildASTExpr (TreeRefCycle _ f) = buildASTExpr f

refCycleToConstraint :: (EvalEnv m) => TreeNode -> TNRefCycle -> m TreeNode
refCycleToConstraint leaf rc = do
  form <- evalStateT (replaceRefCycleVar (TNRefCycle rc, [])) (DFSTCState Map.empty [] (Path []))
  dump $
    printf
      "refCycleToConstraint: replaced RefCycleVar with %s, evaluated to form:\n%s"
      (show leaf)
      (show $ fst form)
  return $ mkTreeConstraint leaf (fst form)
  where
    replaceRefCycleVar :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
    replaceRefCycleVar =
      dfsTC
        DFSTCConfig
          { dfsName = "replaceRefCycleVar",
            dfsSkipTNConstraint = False,
            dfsPreTCVisitor = \x -> case fst x of
              -- It is the RefCycleVar node as the input argument.
              TNRefCycle _rc -> replaceRefCycleVar (trRcForm _rc, snd x)
              TNRefCycleVar -> return (leaf, snd x)
              _ -> return x,
            dfsPostTCVisitor = return,
            dfsPropUpTC = propUpEvalTC
          }

-- -- --

tnStrBldr :: Int -> TreeNode -> Builder
tnStrBldr i t = case t of
  TNRoot sub -> content (showTreeType t) i mempty [(string7 $ show StartSelector, sub)]
  TNLeaf leaf -> content (showTreeType t) i (string7 (show $ trfValue leaf)) []
  TNStub -> content (showTreeType t) i mempty []
  TNLink l ->
    let linkMeta =
          mempty
            <> string7 "Target:"
            <> string7 (show $ trlTarget l)
     in content (showTreeType t) i (linkMeta) []
  TNScope s ->
    let ordLabels =
          string7 "ordLabels: "
            <> char7 '['
            <> foldl (\b l -> b <> string7 l <> char7 ' ') mempty (trsOrdLabels s)
            <> char7 ']'
        fields = map (\k -> (string7 k, (trsSubs s) Map.! k)) (trsOrdLabels s)
     in content (showTreeType t) i ordLabels fields
  TNList vs ->
    let fields = map (\(j, v) -> (integerDec j, v)) (zip [0 ..] vs)
     in content (showTreeType t) i mempty fields
  TNUnaryOp op -> content (showTreeType t) i (string7 $ truRep op) [(string7 (show UnaryOpSelector), truArg op)]
  TNBinaryOp op ->
    content
      (showTreeType t)
      i
      (string7 $ trbRep op)
      [(string7 (show L), trbArgL op), (string7 (show R), trbArgR op)]
  TNDisj d ->
    let dfFields = map (\(j, v) -> (string7 (show $ DisjDefaultSelector j), v)) (zip [0 ..] (trdDefaults d))
        djFields = map (\(j, v) -> (string7 (show $ DisjDisjunctSelector j), v)) (zip [0 ..] (trdDisjuncts d))
     in content (showTreeType t) i mempty (dfFields ++ djFields)
  TNConstraint c ->
    content
      (showTreeType t)
      i
      (string7 (show $ constLeafDir c))
      [(string7 (show L), trcArgL c), (string7 (show R), trcArgR c)]
  TNRefCycle f -> content (showTreeType t) i (string7 $ trRcRep f) [(string7 "Form", trRcForm f)]
  TNRefCycleVar -> content (showTreeType t) i mempty []
  where
    content :: String -> Int -> Builder -> [(Builder, TreeNode)] -> Builder
    content typ j meta fields =
      char7 '('
        <> string7 typ
        <> (char7 ' ' <> meta)
        <> if null fields
          then char7 ')'
          else
            char7 '\n'
              <> foldl
                ( \b (label, sub) ->
                    b
                      <> string7 (replicate (j + 1) ' ')
                      <> char7 '('
                      <> label
                      <> char7 ' '
                      <> tnStrBldr (j + 2) sub
                      <> char7 ')'
                      <> char7 '\n'
                )
                mempty
                fields
              <> string7 (replicate j ' ')
              <> char7 ')'

showTreeIdent :: TreeNode -> Int -> String
showTreeIdent t i = LBS.unpack $ toLazyByteString $ tnStrBldr i t

showTreeType :: TreeNode -> String
showTreeType t = case t of
  TNRoot _ -> "Root"
  TNLeaf _ -> "Leaf"
  TNScope {} -> "Scope"
  TNList {} -> "List"
  TNUnaryOp {} -> "UnaryOp"
  TNBinaryOp {} -> "BinaryOp"
  TNLink {} -> "Link"
  TNDisj {} -> "Disj"
  TNStub -> "Stub"
  TNConstraint {} -> "Const"
  TNRefCycle {} -> "RefCycle"
  TNRefCycleVar -> "RefCycleVar"

instance Show TreeNode where
  show tree = showTreeIdent tree 0

emptyTNScope :: TNScope
emptyTNScope =
  TreeScope
    { trsOrdLabels = [],
      trsVars = Set.empty,
      trsConcretes = Set.empty,
      trsSubs = Map.empty
    }

mkTreeList :: [Value] -> TreeNode
mkTreeList vs = TNList $ map mkTreeLeaf vs

-- | Insert a sub-tree to the tree node with the given selector.
-- Returns the updated parent tree node that contains the newly inserted sub-tree.
insertSubTree ::
  (EvalEnv m) => TreeNode -> Selector -> TreeNode -> m TreeNode
insertSubTree parent sel sub = case sel of
  StartSelector -> case parent of
    TNRoot _ -> return $ TNRoot sub
    _ ->
      throwError $
        printf
          "insertSubTree: cannot insert sub (%s) with selector StartSelector to parent (%s)"
          (showTreeType sub)
          (showTreeType parent)
  StringSelector s -> case parent of
    TNScope parScope -> return $ TNScope $ parScope {trsSubs = Map.insert s sub (trsSubs parScope)}
    _ ->
      throwError $
        printf
          "insertSubTree: cannot insert sub %s to non-TreeScope %s, selector: %s"
          (show sub)
          (show parent)
          (show sel)
  ListSelector i -> case parent of
    TNList vs -> return $ TNList $ take i vs ++ [sub] ++ drop (i + 1) vs
    _ -> throwError $ printf "insertSubTree: cannot insert sub to non-TreeList, selector: %s" (show sel)
  UnaryOpSelector -> case parent of
    TNUnaryOp op -> return $ TNUnaryOp $ op {truArg = sub}
    _ -> throwError $ printf "insertSubTree: cannot insert sub to non-TreeUnaryOp, selector: %s" (show sel)
  BinOpSelector dr -> case parent of
    TNBinaryOp op -> case dr of
      L -> return $ TNBinaryOp $ op {trbArgL = sub}
      R -> return $ TNBinaryOp $ op {trbArgR = sub}
    _ -> throwError $ printf "insertSubTree: cannot insert sub to %s, selector: %s" (showTreeType parent) (show sel)
  DisjDefaultSelector i -> case parent of
    TNDisj d -> return $ TNDisj $ d {trdDefaults = take i (trdDefaults d) ++ [sub] ++ drop (i + 1) (trdDefaults d)}
    _ -> throwError $ printf "insertSubTree: cannot insert sub to %s, selector: %s" (showTreeType parent) (show sel)
  DisjDisjunctSelector i -> case parent of
    TNDisj d -> return $ TNDisj $ d {trdDisjuncts = take i (trdDisjuncts d) ++ [sub] ++ drop (i + 1) (trdDisjuncts d)}
    _ -> throwError $ printf "insertSubTree: cannot insert sub to %s, selector: %s" (showTreeType parent) (show sel)
  ParentSelector -> throwError "insertSubTree: cannot insert sub with ParentSelector"

-- step down the tree with the given selector.
-- This should only be used by TreeCursor.
goTreeSel :: Selector -> TreeNode -> Maybe TreeNode
goTreeSel sel t = case sel of
  StartSelector -> case t of
    TNRoot sub -> Just sub
    _ -> Nothing
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
    TNConstraint c -> case dr of
      L -> Just (trcArgL c)
      R -> Just (trcArgR c)
    _ -> Nothing
  DisjDefaultSelector i -> case t of
    TNDisj d -> trdDefaults d !? i
    _ -> Nothing
  DisjDisjunctSelector i -> case t of
    TNDisj d -> trdDisjuncts d !? i
    _ -> Nothing
  ParentSelector -> Nothing

-- | TreeCrumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type TreeCrumb = (Selector, TreeNode)

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
showTreeCursor tc = LBS.unpack $ toLazyByteString $ prettyBldr tc
  where
    prettyBldr :: TreeCursor -> Builder
    prettyBldr (t, cs) =
      string7 "-- ():\n"
        <> string7 (show t)
        <> char7 '\n'
        <> foldl
          ( \b (sel, n) ->
              b
                <> string7 "-- "
                <> string7 (show sel)
                <> char7 ':'
                <> char7 '\n'
                <> string7 (show n)
                <> char7 '\n'
          )
          mempty
          cs

-- | Go up the tree cursor and return the new cursor.
goUpTC :: TreeCursor -> Maybe TreeCursor
goUpTC (_, []) = Nothing
goUpTC (_, (_, v) : vs) = Just (v, vs)

goDownTCPath :: Path -> TreeCursor -> Maybe TreeCursor
goDownTCPath (Path sels) tc = go (reverse sels) tc
  where
    go :: [Selector] -> TreeCursor -> Maybe TreeCursor
    go [] cursor = Just cursor
    go (x : xs) cursor = do
      nextCur <- goDownTCSel x cursor
      go xs nextCur

-- goDownTCPathErr :: (MonadError String m) => Path -> String -> TreeCursor -> m TreeCursor
-- goDownTCPathErr p msg tc = case goDownTCPath p tc of
--   Just c -> return c
--   Nothing -> throwError msg

-- | Go down the TreeCursor with the given selector and return the new cursor.
-- It handles the case when the current node is a disjunction node.
goDownTCSel :: Selector -> TreeCursor -> Maybe TreeCursor
goDownTCSel sel cursor = case go sel cursor of
  Just c -> Just c
  Nothing -> case fst cursor of
    TNDisj d -> case sel of
      StringSelector _ ->
        if length (trdDefaults d) == 1
          then goDownTCSel (DisjDefaultSelector 0) cursor >>= go sel
          else Nothing
      _ -> Nothing
    _ -> Nothing
  where
    go :: Selector -> TreeCursor -> Maybe TreeCursor
    go s (tree, vs) = do
      nextTree <- goTreeSel s tree
      return (nextTree, (s, tree) : vs)

goDownTCSelErr :: (MonadError String m) => Selector -> String -> TreeCursor -> m TreeCursor
goDownTCSelErr sel msg tc = case goDownTCSel sel tc of
  Just c -> return c
  Nothing -> throwError msg

pathFromTC :: TreeCursor -> Path
pathFromTC (_, crumbs) = Path . reverse $ go crumbs []
  where
    go :: [TreeCrumb] -> [Selector] -> [Selector]
    go [] acc = acc
    go ((n, _) : cs) acc = go cs (n : acc)

-- | propUp propagates the changes made to the tip of the block to the parent block.
-- The structure of the tree is not changed.
propUpTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
propUpTC (t, []) = return (t, [])
propUpTC (sub, (sel, parT) : cs) = case sel of
  StartSelector ->
    if length cs > 0
      then throwError "StartSelector is not the first selector in the path"
      else case parT of
        TNRoot _ -> return (TNRoot sub, [])
        _ -> throwError "propUpTC: root is not TNRoot"
  StringSelector s -> do
    case sub of
      TNRoot _ -> throwError "propUpTC: cannot propagate to root"
      TNList {} -> throwError "unimplemented"
      _ -> updateParScope parT s sub
  ListSelector i -> case parT of
    TNList vs -> return (TNList $ take i vs ++ [sub] ++ drop (i + 1) vs, cs)
    _ -> throwError insertErrMsg
  UnaryOpSelector -> case parT of
    TNUnaryOp op -> return (TNUnaryOp $ op {truArg = sub}, cs)
    _ -> throwError insertErrMsg
  BinOpSelector dr -> case dr of
    L -> case parT of
      TNBinaryOp op -> return (TNBinaryOp $ op {trbArgL = sub}, cs)
      TNConstraint c -> return (TNConstraint $ c {trcArgL = sub}, cs)
      _ -> throwError insertErrMsg
    R -> case parT of
      TNBinaryOp op -> return (TNBinaryOp $ op {trbArgR = sub}, cs)
      TNConstraint c -> return (TNConstraint $ c {trcArgR = sub}, cs)
      _ -> throwError insertErrMsg
  DisjDefaultSelector i -> case parT of
    TNDisj d ->
      return
        (TNDisj $ d {trdDefaults = take i (trdDefaults d) ++ [sub] ++ drop (i + 1) (trdDefaults d)}, cs)
    _ -> throwError insertErrMsg
  DisjDisjunctSelector i -> case parT of
    TNDisj d ->
      return
        (TNDisj $ d {trdDisjuncts = take i (trdDisjuncts d) ++ [sub] ++ drop (i + 1) (trdDisjuncts d)}, cs)
    _ -> throwError insertErrMsg
  ParentSelector -> throwError "propUpTC: ParentSelector is not allowed"
  where
    updateParScope :: (MonadError String m) => TreeNode -> String -> TreeNode -> m TreeCursor
    updateParScope par label newSub = case par of
      TNScope parScope -> case newSub of
        TNLeaf (TreeLeaf (Bottom _)) -> return (newSub, cs)
        _ -> let newParNode = insertScopeNode parScope label newSub in return (TNScope newParNode, cs)
      _ -> throwError insertErrMsg

    -- TODO: insertParList

    insertErrMsg :: String
    insertErrMsg =
      printf
        "propUpTC: cannot insert child %s to parent %s, selector: %s, child:\n%s\nparent:\n%s"
        (showTreeType sub)
        (showTreeType parT)
        (show sel)
        (show sub)
        (show parT)

evalPendingTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
evalPendingTC tc = do
  node <- case fst tc of
    TNUnaryOp op -> truOp op (truArg op)
    TNBinaryOp op -> trbOp op (trbArgL op) (trbArgR op)
    TNConstraint c -> do
      Config {cfUnify = unify} <- ask
      unify (trcArgL c) (trcArgR c)
    _ -> return $ fst tc
  return (node, snd tc)

-- | propUp propagates the changes made to the tip of the block to the parent block.
-- The structure of the tree is not changed.
propUpEvalTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
propUpEvalTC tc = evalPendingTC tc >>= propUpTC

-- | Propagates the changes to the parent blocks until the top block.
-- It returns the root block.
propRootEvalTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
propRootEvalTC (t, []) = return (t, [])
propRootEvalTC tc = propUpEvalTC tc >>= propRootEvalTC

-- propRootTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
-- propRootTC (t, []) = return (t, [])
-- propRootTC tc = propUpTC False tc >>= propRootTC

-- -- | Go from the current cursor to the root and then go down to the path.
-- goEvalTCPathErr :: (EvalEnv m) => Path -> TreeCursor -> m TreeCursor
-- goEvalTCPathErr p tc = do
--   tarTCMaybe <- goTCPathMaybe p True tc
--   maybe (throwError errMsg) return tarTCMaybe
--   where
--     errMsg :: String
--     errMsg = printf "goEvalTCPathErr: path %s not found" (show p)
--
-- goNoEvalTCPathErr :: (EvalEnv m) => Path -> TreeCursor -> m TreeCursor
-- goNoEvalTCPathErr p tc = do
--   tarTCMaybe <- goTCPathMaybe p False tc
--   maybe (throwError errMsg) return tarTCMaybe
--   where
--     errMsg :: String
--     errMsg =
--       printf
--         "goNoEvalTCPathErr: path %s not found, rel: %s, cursor:\n%s"
--         (show p)
--         (show $ relPath (pathFromTC tc) p)
--         (showTreeCursor tc)
--
-- goTCPathMaybe :: (EvalEnv m) => Path -> Bool -> TreeCursor -> m (Maybe TreeCursor)
-- goTCPathMaybe p eval tc = go relSels tc
--   where
--     relSels :: [Selector]
--     relSels = reverse $ getPath $ relPath (pathFromTC tc) p
--
--     go :: (EvalEnv m) => [Selector] -> TreeCursor -> m (Maybe TreeCursor)
--     go [] cursor = return $ Just cursor
--     go (x : xs) cursor = case x of
--       ParentSelector -> propUpTC eval cursor >>= go xs
--       _ -> case goDownTCSel x cursor of
--         Nothing -> return Nothing
--         Just c -> go xs c

-- | Search the tree cursor up to the root and return the tree cursor that points to the variable.
searchTCVar :: String -> TreeCursor -> Maybe TreeCursor
searchTCVar var tc = case fst tc of
  TNScope scope -> case Map.lookup var (trsSubs scope) of
    Just node -> Just (node, (StringSelector var, fst tc) : snd tc)
    Nothing -> goUpTC tc >>= searchTCVar var
  _ -> goUpTC tc >>= searchTCVar var

-- | Search the tree cursor up to the root and return the tree cursor that points to the path.
searchTCPath :: Path -> TreeCursor -> Maybe TreeCursor
searchTCPath p tc = do
  fstSel <- headSel p
  s <- case fstSel of
    StringSelector s -> return s
    _ -> Nothing
  base <- searchTCVar s tc
  tailP <- tailPath p
  goDownTCPath tailP base

-- followLinkTC :: (EvalEnv m) => TreeCursor -> m (Maybe TreeCursor)
-- followLinkTC = go Set.empty
--   where
--     go :: (EvalEnv m) => Set.Set Path -> TreeCursor -> m (Maybe TreeCursor)
--     go visited cursor =
--       let tcPath = pathFromTC cursor
--        in if Set.member tcPath visited
--             then do
--               dump $ printf "followLinkTC: link cycle detected: %s" (show tcPath)
--               return $ Just (TNLeaf $ TreeLeaf Top, snd cursor)
--             else case fst cursor of
--               TNLink link -> do
--                 case searchTCPath (trlTarget link) cursor of
--                   Nothing -> return Nothing
--                   Just tarTC -> go (Set.insert tcPath visited) tarTC
--               _ -> return $ Just cursor

-- | Insert the tree node to the tree cursor with the given selector and returns the new cursor that focuses on the
-- newly inserted value.
insertTCSub :: (EvalEnv m) => Selector -> TreeNode -> TreeCursor -> m TreeCursor
insertTCSub sel sub tc@(par, cs) =
  let errMsg :: String
      errMsg =
        printf
          "insertTCSub: cannot insert sub to %s with selector %s"
          (showTreeType par)
          (show sel)
      scopeInsert :: (EvalEnv m) => (EvalMonad TreeCursor) -> (String -> TNScope -> EvalMonad TreeCursor) -> m TreeCursor
      scopeInsert defaultAct scopeAct = case (sel, par) of
        (StringSelector s, TNScope parScope) -> scopeAct s parScope
        _ -> defaultAct
   in scopeInsert (updateTCSub sel sub tc) $
        \s parScope -> maybe
          (updateTCSub sel sub tc)
          ( \extSub -> do
              Config {cfUnify = unify} <- ask
              let newSub =
                    TNBinaryOp $
                      TreeBinaryOp
                        { trbRep = show AST.Unify,
                          trbExpr = AST.ExprBinaryOp AST.Unify (buildASTExpr extSub) (buildASTExpr sub),
                          trbOp = unify,
                          trbArgL = extSub,
                          trbArgR = sub
                        }
              -- newParent = TNScope $ parScope {trsSubs = Map.insert s newSub (trsSubs parScope)}
              upar <- insertSubTree par sel newSub
              dump $ printf "insertTCSub: parent:\n%s" (show upar)
              maybe (throwError errMsg) return $ goDownTCSel sel (upar, cs) >>= goDownTCSel (BinOpSelector R)
          )
          $ do
            Map.lookup s (trsSubs parScope) >>= \case
              TNStub -> Nothing
              snode -> Just snode

-- | Update the tree node to the tree cursor with the given selector and returns the new cursor that focuses on the
-- updated value.
updateTCSub :: (EvalEnv m) => Selector -> TreeNode -> TreeCursor -> m TreeCursor
updateTCSub sel sub (par, cs) =
  let errMsg :: String
      errMsg =
        printf
          "updateTCSub: cannot insert sub to %s with selector %s"
          (showTreeType par)
          (show sel)
   in do
        u <- insertSubTree par sel sub
        dump $ printf "updateTCSub: parent:\n%s" (show u)
        goDownTCSelErr sel errMsg (u, cs)

-- | Insert a list of labels the tree and return the new cursor that contains the newly inserted value.
insertTCScope :: (EvalEnv m) => Selector -> [String] -> Set.Set String -> TreeCursor -> m TreeCursor
insertTCScope sel labels vars tc =
  let sub =
        TNScope $
          TreeScope
            { trsOrdLabels = labels,
              trsVars = vars,
              trsConcretes = Set.empty,
              trsSubs = Map.fromList [(l, TNStub) | l <- labels]
            }
   in insertTCSub sel sub tc

insertTCList :: (EvalEnv m) => Selector -> [Value] -> TreeCursor -> m TreeCursor
insertTCList sel vs tc = let sub = mkTreeList vs in insertTCSub sel sub tc

-- | Insert a unary operator that works for scalar values.
insertTCUnaryOp ::
  (EvalEnv m) => Selector -> String -> AST.UnaryExpr -> (TreeNode -> EvalMonad TreeNode) -> TreeCursor -> m TreeCursor
insertTCUnaryOp sel rep ue f tc =
  let newSubGen :: TreeNode -> (TreeNode -> EvalMonad TreeNode) -> TreeNode
      newSubGen n op =
        TNUnaryOp $
          TreeUnaryOp
            { truOp = op,
              truArg = n,
              truRep = rep,
              truExpr = ue
            }
      work :: (EvalEnv m) => TreeNode -> m TreeNode
      work n = case isValueNode n of
        -- Notice it only works for value nodes.
        True -> f n
        _ -> return $ newSubGen n work
      sub = newSubGen TNStub work
   in insertTCSub sel sub tc

-- | Insert a binary operator that works for scalar values.
insertTCBinaryOp ::
  (EvalEnv m) =>
  Selector ->
  String ->
  AST.Expression ->
  (TreeNode -> TreeNode -> EvalMonad TreeNode) ->
  (TreeNode -> TreeNode -> Bool) ->
  TreeCursor ->
  m TreeCursor
insertTCBinaryOp sel rep e f cond tc =
  let newSubGen :: TreeNode -> TreeNode -> (TreeNode -> TreeNode -> EvalMonad TreeNode) -> TreeNode
      newSubGen n1 n2 op =
        TNBinaryOp $
          TreeBinaryOp
            { trbOp = op,
              trbArgL = n1,
              trbArgR = n2,
              trbRep = rep,
              trbExpr = e
            }
      work :: (EvalEnv m) => TreeNode -> TreeNode -> m TreeNode
      work n1 n2 =
        if cond n1 n2
          then f n1 n2
          else return $ newSubGen n1 n2 work
      sub = newSubGen TNStub TNStub work
   in insertTCSub sel sub tc

insertTCDisj ::
  (EvalEnv m) => Selector -> AST.Expression -> (TreeNode -> TreeNode -> EvalMonad TreeNode) -> TreeCursor -> m TreeCursor
insertTCDisj sel e f tc =
  let newSubGen :: TreeNode -> TreeNode -> (TreeNode -> TreeNode -> EvalMonad TreeNode) -> TreeNode
      newSubGen n1 n2 op =
        TNBinaryOp $
          TreeBinaryOp
            { trbOp = op,
              trbArgL = n1,
              trbArgR = n2,
              trbRep = show AST.Disjunction,
              trbExpr = e
            }
      work :: (EvalEnv m) => TreeNode -> TreeNode -> m TreeNode
      work n1 n2 = case map isValueNode [n1, n2] of
        [True, True] ->
          f n1 n2
        -- TODO
        -- TNDisj d -> case map (mapM scalarOf) [(trdDefaults d), (trdDisjuncts d)] of
        --   [Just vs1, Just vs2] -> return $ TNDisj $ d
        --   _ -> throwError "insertTCDisj: invalid disjunction values"
        -- _ -> return $ newSubGen n1 n2 work
        _ -> return $ newSubGen n1 n2 work
      sub = newSubGen TNStub TNStub work
   in insertTCSub sel sub tc

insertTCDot ::
  (EvalEnv m) => Selector -> Selector -> AST.UnaryExpr -> TreeCursor -> m TreeCursor
insertTCDot sel dotSel ue tc = do
  curSub <- goDownTCSelErr sel "insertTCDot: cannot get sub cursor" tc
  let tree = fst curSub
  newSub <- case tree of
    TNLink link -> return $ TNLink $ link {trlTarget = appendSel dotSel (trlTarget link), trlExpr = Just ue}
    _ -> throwError $ printf "insertTCDot: cannot insert link to non-link node:\n%s" (show tree)
  updateTCSub sel newSub tc

insertTCLeafValue :: (EvalEnv m) => Selector -> Value -> TreeCursor -> m TreeCursor
insertTCLeafValue sel v tc = let sub = mkTreeLeaf v in do insertTCSub sel sub tc

insertTCLink :: (EvalEnv m) => Selector -> String -> TreeCursor -> m TreeCursor
insertTCLink sel var tc =
  let subPath = appendSel sel (pathFromTC tc)
      tarSel = StringSelector var
      tarPath = Path [tarSel]
   in let sub = TNLink $ TreeLink {trlTarget = tarPath, trlExpr = Nothing}
       in do
            dump $ printf "insertTCLink: link to %s, path: %s" (show tarPath) (show subPath)
            u <- insertTCSub sel sub tc
            return u

-- in if
--      | tarSel == sel -> do
--          dump $ printf "insertTCLink: link to itself, path: %s" (show subPath)
--          insertTCSub sel (mkTreeLeaf Top) tc
--      -- \| isPrefix tarPath subPath -> do
--      --     dump $ printf "insertTCLink: structural cycle, %s is prefix of %s" (show tarPath) (show subPath)
--      --     insertTCSub sel (mkTreeLeaf $ Bottom "structural cycle") tc
--      | otherwise ->
--          let sub = TNLink $ TreeLink {trlTarget = tarPath, trlExpr = Nothing}
--           in do
--                dump $ printf "insertTCLink: link to %s, path: %s" (show tarPath) (show subPath)
--                u <- insertTCSub sel sub tc
--                return u

-- -- try to detect if the new link forms a cycle.
-- followLinkTC u >>= \case
--   Just (TNLeaf (TreeLeaf Top), _) -> insertTCLeafValue sel Top tc
--   _ -> return u

-- insertTCRefCycle :: (EvalEnv m) => Path -> TreeCursor -> m TreeCursor
-- insertTCRefCycle ref tc =
--   evalStateT (replaceLinks tc) (DFSTCState Map.empty)
--   where
--     replaceLinks :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
--     replaceLinks =
--       dfsTC
--         DFSTCConfig
--           { dfsName = "replaceLinks",
--             dfsPreTCVisitor = \x -> case fst x of
--               TNLink link ->
--                 if trlTarget link == ref
--                   then return (TNStub, snd x)
--                   else return x
--               _ -> return x,
--             dfsPropUpTC = propUpTC False
--           }

-- | finalizeTC evaluates the tree pointed by the cursor by traversing the tree and evaluating all nodes.
finalizeTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
finalizeTC tc = do
  dump $ printf "start resolving links for tree: ----\n%s" (show $ fst tc)
  u <- evalStateT (resolveLinksTC tc) (DFSTCState Map.empty [] (Path []))
  dump $ printf "start finalizing for tree: ----\n%s" (show $ fst u)
  evalStateT (finalizeWalkTC u) (DFSTCState Map.empty [] (Path []))

data DFSTCState = DFSTCState
  { dfsMarks :: Map.Map Path Int,
    dfsRefCyclePathStack :: [Path],
    dfsRoute :: Path
  }

data DFSTCConfig = DFSTCConfig
  { dfsName :: String,
    dfsSkipTNConstraint :: Bool,
    dfsPreTCVisitor :: forall m. (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor,
    dfsPostTCVisitor :: forall m. (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor,
    dfsPropUpTC :: forall m. (EvalEnv m) => TreeCursor -> m TreeCursor
  }

dfsTC :: (EvalEnv m, MonadState DFSTCState m) => DFSTCConfig -> TreeCursor -> m TreeCursor
dfsTC dfsConf tc =
  do
    marks <- gets dfsMarks
    case Map.lookup path marks of
      Just 2 -> return tc
      Just 1 -> throwError $ printf "%s: visiting node %s should not be visited again" header (show path)
      _ -> do
        route <- gets dfsRoute
        dump $
          printf
            "%s: node (%s) route: %s, tc_path: %s enter:\n%s"
            header
            (showTreeType $ fst tc)
            (show route)
            (show path)
            (show $ fst tc)
        prex <- dfsPreTCVisitor dfsConf tc
        modify $ \fs -> fs {dfsMarks = Map.insert path 1 (dfsMarks fs)}
        x <- visit prex
        modify $ \fs -> fs {dfsMarks = Map.insert path 2 (dfsMarks fs)}
        postx <- dfsPostTCVisitor dfsConf x
        dump $
          printf
            "%s: node (%s), route: %s, tc_path: %s, leaves with node:\n%s"
            header
            (showTreeType $ fst postx)
            (show route)
            (show path)
            (show $ fst postx)
        return postx
  where
    header :: String
    header = dfsName dfsConf
    path = pathFromTC tc

    dfs :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
    dfs = dfsTC dfsConf

    levelUp :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
    levelUp x = do
      u <- dfsPropUpTC dfsConf x
      modify $ \fs -> fs {dfsRoute = fromJust $ initPath (dfsRoute fs)}
      return u

    getSubTC :: (EvalEnv m, MonadState DFSTCState m) => Selector -> TreeCursor -> m TreeCursor
    getSubTC sel cursor = do
      u <-
        goDownTCSelErr
          sel
          ( printf
              "%s: cannot get sub cursor with selector %s, path: %s, cursor:\n%s"
              header
              (show sel)
              (show $ pathFromTC cursor)
              (showTreeCursor cursor)
          )
          cursor
      modify $ \fs -> fs {dfsRoute = appendSel sel (dfsRoute fs)}
      return u

    visit :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
    visit x = do
      u <- case fst x of
        TNLeaf _ -> return x
        TNRoot _ -> getSubTC StartSelector x >>= dfs >>= levelUp
        TNScope scope ->
          let goSub :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> String -> m TreeCursor
              goSub acc k = case fst acc of
                TNLeaf (TreeLeaf (Bottom _)) -> return acc
                _ -> getSubTC (StringSelector k) acc >>= dfs >>= levelUp
           in foldM goSub x (Map.keys (trsSubs scope))
        TNList _ -> throwError $ printf "%s: TNList is not implemented" header
        TNUnaryOp _ -> pure x >>= getSubTC UnaryOpSelector >>= dfs >>= levelUp
        TNBinaryOp _ ->
          pure x
            >>= getSubTC (BinOpSelector L)
            >>= dfs
            >>= levelUp
            >>= getSubTC (BinOpSelector R)
            >>= dfs
            >>= levelUp
        TNDisj d ->
          let goSub :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> Selector -> m TreeCursor
              goSub acc sel = pure acc >>= getSubTC sel >>= dfs >>= levelUp
           in do
                utc <- foldM goSub x (map DisjDefaultSelector [0 .. length (trdDefaults d) - 1])
                foldM goSub utc (map DisjDisjunctSelector [0 .. length (trdDisjuncts d) - 1])
        TNConstraint _ ->
          if dfsSkipTNConstraint dfsConf
            then return x
            else do
              do
                pure x
                >>= getSubTC (BinOpSelector L)
                >>= dfs
                >>= levelUp
                >>= getSubTC (BinOpSelector R)
                >>= dfs
                >>= levelUp
        TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
        TNLink _ -> return x
        -- Do not visit the node if it is a reference cycle.
        TNRefCycle _ -> return x
        TNRefCycleVar -> return x
      evalPendingTC u

resolveLinksTC :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
resolveLinksTC =
  dfsTC
    DFSTCConfig
      { dfsName = "resolveLinksTC",
        dfsSkipTNConstraint = True,
        dfsPreTCVisitor = followLinkTC,
        dfsPostTCVisitor = \x -> do
          stack <- gets dfsRefCyclePathStack
          case listToMaybe stack of
            Nothing -> return x
            Just p ->
              if p == pathFromTC x
                then do
                  modify $ \fs -> fs {dfsRefCyclePathStack = drop 1 stack}
                  return (TNRefCycle $ TreeRefCycle {trRcForm = fst x, trRcRep = show $ fromJust $ lastSel p}, snd x)
                else return x,
        dfsPropUpTC = propUpEvalTC
      }

followLinkTC :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
followLinkTC tc = case fst tc of
  TNLink link ->
    let tarPath = trlTarget link
     in do
          case searchTCPath tarPath tc of
            Nothing -> do
              dump $ printf "followLinkTC: link target not found: %s" (show tarPath)
              return tc
            Just tar -> do
              dump $
                printf
                  "followLinkTC: link discovers path: %s, tree:\n%s"
                  (show $ pathFromTC tar)
                  (show $ fst tar)
              let tarAbsPath = canonicalizePath $ pathFromTC tar
                  selfAbsPath = canonicalizePath $ pathFromTC tc
              if tarAbsPath == selfAbsPath
                then do
                  dump $
                    printf
                      "followLinkTC: reference cycle detected: %s == %s"
                      (show $ pathFromTC tc)
                      (show $ pathFromTC tar)
                  modify $ \fs -> fs {dfsRefCyclePathStack = tarAbsPath : dfsRefCyclePathStack fs}
                  return (TNRefCycleVar, snd tc)
                else
                  let node = fst tar
                      newTC = (node, snd tc)
                   in do
                        dump $
                          printf
                            "followLinkTC: link %s resolves to node:\n%s"
                            (show $ pathFromTC tar)
                            (show node)
                        case node of
                          TNLink _ -> do
                            dump $ printf "followLinkTC: link %s resolves to another link" (show tarPath)
                            followLinkTC newTC
                          TNConstraint c -> do
                            dump $ printf "followLinkTC: link %s visits constraint" (show tarPath)
                            return (leafFromTNConst c, snd tc)
                          TNRefCycle _ -> do
                            dump $ printf "followLinkTC: link %s resolves to reference cycle" (show tarPath)
                            -- We should keep the input link because if a scope containing the link got copied to
                            -- another place, the link could be resolved due to another concrete value could be assigned
                            -- to the target of the link.
                            return tc
                          _ -> return newTC
  _ -> return tc

finalizeWalkTC :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
finalizeWalkTC tc =
  dfsTC
    DFSTCConfig
      { dfsName = "finalizeWalkTC",
        dfsSkipTNConstraint = False,
        dfsPreTCVisitor = followLinkTC,
        dfsPostTCVisitor = return,
        dfsPropUpTC = propUpEvalTC
      }
    tc

-- | Context
data Context = Context
  { -- curBlock is the current block that contains the variables.
    -- A new block will replace the current one when a new block is entered.
    -- A new block is entered when one of the following is encountered:
    -- - The "{" token
    -- - for and let clauses
    ctxEvalTree :: TreeCursor,
    ctxReverseDeps :: Map.Map Path Path
  }

prettyRevDeps :: Map.Map Path [Path] -> String
prettyRevDeps m =
  let p = intercalate ", " $ map (\(k, v) -> printf "(%s->%s)" (show k) (show v)) (Map.toList m)
   in "[" ++ p ++ "]"

pushNewNode :: (Runtime m) => (TreeCursor -> m TreeCursor) -> m ()
pushNewNode f = do
  tc <- gets ctxEvalTree >>= f
  modify $ \ctx -> ctx {ctxEvalTree = tc}

-- | Write the value to the parent block and return the value.
leaveCurNode :: (Runtime m) => Selector -> String -> m ()
leaveCurNode sel msg = do
  tc <- gets ctxEvalTree
  parTC <- go tc
  modify $ \ctx -> ctx {ctxEvalTree = parTC}
  dump $ printf "leaveCurNode: %s path: %s, parent treenode is:\n%s" msg (show $ pathFromTC tc) (show (fst parTC))
  where
    go :: (EvalEnv m) => TreeCursor -> m TreeCursor
    go tc@(_, []) = return tc
    go tc@(_, (s, _) : _) = do
      parTC <- propUpEvalTC tc
      if s == sel
        then return parTC
        else go parTC
