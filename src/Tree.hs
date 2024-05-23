{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Tree
  ( Context (..),
    EvalEnv,
    EvalMonad,
    Evaluator,
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
    dump,
    exprIO,
    finalizeTC,
    -- getValueTCPath,
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
    pathFromTC,
    prettyRevDeps,
    propTopTC,
    pushNewNode,
    -- putValueTCPath,
    searchTCVar,
    -- tcFromSV,
    vToE,
    -- valueOfTreeNode,
    showTreeCursor,
    isValueNode,
    buildASTExpr,
    emptyTNScope,
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
import Control.Monad.State.Strict
  ( MonadState,
    evalStateT,
    get,
    gets,
    modify,
    put,
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
import Data.Maybe (fromJust, isJust, isNothing)
import qualified Data.Set as Set
import Data.Text (pack)
import Debug.Trace
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
  | -- Stub is used as placeholder inside a struct. It is like Top. The actual value will be guaranteed to be evaluated.
    Stub

type EvalEnv m = (MonadError String m, MonadLogger m)

type Runtime m = (EvalEnv m, MonadState Context m)

type EvalMonad a = forall m. (EvalEnv m) => m a

-- | Evaluator is a function that takes a list of tuples values and their paths and returns a value.
type Evaluator = [(Path, Value)] -> EvalMonad Value

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
  show Stub = "S_" where

instance Eq Value where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) (Bottom _) (Bottom _) = True
  (==) Top Top = True
  (==) Null Null = True
  (==) Stub Stub = True
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
vToE Stub = throwError "vToE: stub value"

class ValueNode a where
  isValueNode :: a -> Bool
  isScalar :: a -> Bool
  scalarOf :: a -> Maybe Value

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
  | --  | Unless the target is a Leaf, the TNLink should not be pruned.
    TNLink TNLink
  | -- | TreeLeaf contains an atom value. (could be scalar in the future)
    TNLeaf TNLeaf

instance Eq TreeNode where
  (==) (TNLeaf l1) (TNLeaf l2) = l1 == l2
  (==) (TNRoot t1) (TNRoot t2) = t1 == t2
  (==) (TNScope s1) (TNScope s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNLink l1) (TNLink l2) = l1 == l2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNUnaryOp o1) (TNUnaryOp o2) = o1 == o2
  (==) (TNBinaryOp o1) (TNBinaryOp o2) = o1 == o2
  (==) _ _ = False

instance ValueNode TreeNode where
  isValueNode n = case n of
    TNLeaf _ -> True
    TNScope _ -> True
    TNList _ -> True
    TNDisj _ -> True
    _ -> False
  isScalar n = case n of
    TNLeaf _ -> True
    _ -> False
  scalarOf n = case n of
    TNLeaf l -> Just (trfValue l)
    _ -> Nothing

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

data TNScope = TreeScope
  { 
    trsOrdLabels :: [String],
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
    trlExpr :: AST.Expression,
    -- | The final value of the target path.
    -- It should only be set when in the final evaluating.
    trlFinal :: Maybe Value
  }

instance Eq TNLink where
  (==) l1 l2 = trlTarget l1 == trlTarget l2

instance BuildASTExpr TNLink where
  buildASTExpr = trlExpr

data TNLeaf = TreeLeaf
  { trfValue :: Value
  }

instance Eq TNLeaf where
  (==) (TreeLeaf v1) (TreeLeaf v2) = v1 == v2

instance BuildASTExpr TNLeaf where
  buildASTExpr (TreeLeaf v) = fromRight (AST.litCons AST.BottomLit) (runExcept $ vToE v)

data TNDisj = TreeDisj
  { -- trdValue :: DisjValue,
    trdDefaults :: [TreeNode],
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

mkTreeLeaf :: Value -> TreeNode
mkTreeLeaf v = TNLeaf $ TreeLeaf {trfValue = v}

-- valueOfTreeNode :: TreeNode -> Maybe Value
-- valueOfTreeNode t = case t of
--   TNRoot sub -> case sub of
--     TNRoot _ -> Nothing
--     _ -> valueOfTreeNode sub
--   TNScope s -> Just (Struct (trsValue s))
--   TNList _ -> Nothing
--   TNUnaryOp _ -> Nothing
--   TNBinaryOp _ -> Nothing
--   TNLink link -> trlFinal link
--   TNLeaf leaf -> Just (trfValue leaf)
--   TNDisj d -> Just (Disjunction (trdValue d))

tnStrBldr :: Int -> TreeNode -> Builder
tnStrBldr i t = case t of
  TNRoot sub -> content (showTreeType t) i mempty [(string7 $ show StartSelector, sub)]
  TNLeaf leaf -> content (showTreeType t) i (string7 (show $ trfValue leaf)) []
  TNLink l -> content (showTreeType t) i (string7 (show $ trlTarget l)) []
  TNScope s ->
    let 
      ordLabels = 
        string7 "ordLabels: "
          <> char7 '['
          <> foldl (\b l -> b <> string7 l <> char7 ' ') mempty (trsOrdLabels s)
          <> char7 ']'
      fields = map (\(k, v) -> (string7 k, v)) (Map.toList (trsSubs s))
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

-- | The StructValue should only have one level of children.
mkTreeScope :: [String] -> TreeNode
mkTreeScope labels =
  let subs = Map.fromList $ map (\k -> (k, mkTreeLeaf Stub)) labels
   in TNScope $
        emptyTNScope
          { trsOrdLabels = labels,
            trsSubs = subs
          }

mkTreeList :: [Value] -> TreeNode
mkTreeList vs = TNList $ map mkTreeLeaf vs

-- -- | Update the tree node with the given value.
-- updateTreeNode :: (MonadError String m) => TreeNode -> Value -> m TreeNode
-- updateTreeNode t v = case v of
--   Struct sv -> case t of
--     TNScope s -> return $ TNScope $ TreeScope {trsValue = sv, trsSubs = trsSubs s}
--     _ -> throwError $ printf "updateTreeNode: cannot set non-struct value to non-TreeScope, value: %s" (show v)
--   _ -> case t of
--     TNLeaf _ -> return $ mkTreeLeaf v
--     _ -> throwError $ printf "updateTreeNode: cannot set non-struct value to non-TreeLeaf, value: %s" (show v)

-- | Insert a sub-tree to the tree node with the given selector.
-- Returns the updated tree node that contains the newly inserted sub-tree.
insertSubTree :: (MonadError String m) => TreeNode -> Selector -> TreeNode -> m TreeNode
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
    TNScope parScope -> if Map.member s (trsSubs parScope)
      then return $ TNScope $ parScope {trsSubs = Map.insert s sub (trsSubs parScope)}
      else return $ TNScope $ parScope {
        trsOrdLabels = trsOrdLabels parScope ++ [s], trsSubs = Map.insert s sub (trsSubs parScope)}
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

-- step down the tree with the given selector.
-- This should only be used by TreeCursor.
goTreeSel :: TreeNode -> Selector -> Maybe TreeNode
goTreeSel t sel = case sel of
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
    _ -> Nothing
  DisjDefaultSelector i -> case t of
    TNDisj d -> trdDefaults d !? i
    _ -> Nothing
  DisjDisjunctSelector i -> case t of
    TNDisj d -> trdDisjuncts d !? i
    _ -> Nothing

-- updateTreePathValue :: (MonadError String m) => TreeNode -> Path -> Value -> m TreeNode
-- updateTreePathValue t path v = case goTreePath t path of
--   Just node -> updateTreeNode node v
--   Nothing -> throwError $ printf "updateTreePathValue: path not found: %s" (show path)

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
      string7 (show t)
        <> char7 '\n'
        <> foldl
          ( \b (sel, n) ->
              b
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
propUpTC (sub, (sel, parT) : cs) =
  let -- first resolve the sub tree to a value if possible.
      newSubM :: (EvalEnv m) => m TreeNode
      newSubM = case sub of
        TNUnaryOp op -> truOp op (truArg op)
        TNBinaryOp op -> trbOp op (trbArgL op) (trbArgR op)
        _ -> return sub
   in case sel of
        StartSelector ->
          if length cs > 0
            then throwError "StartSelector is not the first selector in the path"
            else case parT of
              TNRoot _ -> newSubM >>= \u -> return (TNRoot u, [])
              _ -> throwError "propUpTC: root is not TNRoot"
        StringSelector s -> do
          u <- newSubM
          case u of
            TNRoot _ -> throwError "propUpTC: cannot propagate to root"
            TNList {} -> throwError "unimplemented"
            _ -> updateParScope parT s u
        ListSelector i -> case parT of
          TNList vs -> newSubM >>= \u -> return (TNList $ take i vs ++ [u] ++ drop (i + 1) vs, cs)
          _ -> throwError insertErrMsg
        UnaryOpSelector -> case parT of
          TNUnaryOp op -> newSubM >>= \u -> return (TNUnaryOp $ op {truArg = u}, cs)
          _ -> throwError insertErrMsg
        BinOpSelector dr -> case dr of
          L -> case parT of
            TNBinaryOp op -> newSubM >>= \u -> return (TNBinaryOp $ op {trbArgL = u}, cs)
            _ -> throwError insertErrMsg
          R -> case parT of
            TNBinaryOp op -> newSubM >>= \u -> return (TNBinaryOp $ op {trbArgR = u}, cs)
            _ -> throwError insertErrMsg
        DisjDefaultSelector i -> case parT of
          TNDisj d -> newSubM >>= \u -> return (TNDisj $ d {trdDefaults = take i (trdDefaults d) ++ [u] ++ drop (i + 1) (trdDefaults d)}, cs)
          _ -> throwError insertErrMsg
        DisjDisjunctSelector i -> case parT of
          TNDisj d -> newSubM >>= \u -> return (TNDisj $ d {trdDisjuncts = take i (trdDisjuncts d) ++ [u] ++ drop (i + 1) (trdDisjuncts d)}, cs)
          _ -> throwError insertErrMsg
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
      printf "propUpTC: cannot insert child %s to parent %s, selector: %s" (showTreeType sub) (showTreeType parT) (show sel)

-- | propTopTC propagates the changes to the parent blocks until the top block.
-- It returns the root block.
propTopTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
propTopTC (t, []) = return (t, [])
propTopTC tc = propUpTC tc >>= propTopTC

-- | Search the tree cursor up to the root and return the tree cursor that points to the variable.
searchTCVar :: String -> TreeCursor -> Maybe TreeCursor
searchTCVar var tc = case fst tc of
  TNScope scope -> case Map.lookup var (trsSubs scope) of
    Just node -> Just (node, (StringSelector var, fst tc) : snd tc)
    Nothing -> goUpTC tc >>= searchTCVar var
  _ -> goUpTC tc >>= searchTCVar var

-- getValueTCPath :: TreeCursor -> Path -> Maybe Value
-- getValueTCPath tc p = do
--   targetTC <- goDownTCPath tc p
--   valueOfTreeNode $ fst targetTC

-- -- | Put the value to the tree cursor at the given path.
-- -- Returns the udpated root tree cursor.
-- putValueTCPath :: (EvalEnv m) => TreeCursor -> Path -> Value -> m TreeCursor
-- putValueTCPath tc p v = do
--   rootTC <- propTopTC tc
--   case goDownTCPath rootTC p of
--     Nothing -> throwError $ printf "putValueTCPath: path not found: %s" (show p)
--     Just ttc -> do
--       updated <- updateTreeNode (fst ttc) v
--       propTopTC (updated, snd ttc)

-- -- | Create a new tree cursor from a struct value.
-- -- It is used to create a new tree cursor from scratch.
-- kcFromSV :: StructValue -> TreeCursor
-- tcFromSV sv = (TNRoot $ mkTreeScope sv, [])

-- | Follow the link in the tree cursor and returns the updated tree cursor.
followLinkTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
followLinkTC tc =
  let tcPath = pathFromTC tc
   in do
        tar <- go tc
        r <- propTopTC tar
        case goDownTCPath r tcPath of
          Nothing -> throwError $ printf "followLinkTC: path not found: %s" (show tcPath)
          Just ttc -> return (fst tar, snd ttc)
  where
    go :: (EvalEnv m) => TreeCursor -> m TreeCursor
    go cursor = case fst cursor of
      TNLink link -> case trlFinal link of
        Just {} -> return cursor
        Nothing -> do
          rootTC <- propTopTC cursor
          tarTC <- case goDownTCPath rootTC (trlTarget link) of
            Nothing -> throwError $ printf "followLinkTC: TNLink value can not be got for %s" (show (trlTarget link))
            Just tarTC -> return tarTC
          go tarTC
      _ -> return cursor

-- | Insert the tree node to the tree cursor with the given selector.
insertTCSub :: (EvalEnv m) => Selector -> TreeNode -> TreeCursor -> m TreeCursor
insertTCSub sel sub (par, cs) = do
  u <- insertSubTree par sel sub
  return (sub, (sel, u) : cs)

-- | Insert a list of labels the tree and return the new cursor that contains the newly inserted value.
insertTCScope :: (EvalEnv m) => Selector -> [String] -> Set.Set String -> TreeCursor -> m TreeCursor
insertTCScope sel labels vars tc =
  let sub =
        TNScope $
          TreeScope
            { trsOrdLabels = labels,
              trsVars = vars,
              trsConcretes = Set.empty,
              trsSubs = Map.fromList [(l, mkTreeLeaf Stub) | l <- labels]
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
      sub = newSubGen (mkTreeLeaf Stub) work
   in insertTCSub sel sub tc

-- | Insert a binary operator that works for scalar values.
insertTCBinaryOp ::
  (EvalEnv m) => Selector -> String -> AST.Expression -> (TreeNode -> TreeNode -> EvalMonad TreeNode) -> TreeCursor -> m TreeCursor
insertTCBinaryOp sel rep e f tc =
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
      work n1 n2 = case map isValueNode [n1, n2] of
        [True, True] -> f n1 n2
        _ -> return $ newSubGen n1 n2 work
      sub = newSubGen (mkTreeLeaf Stub) (mkTreeLeaf Stub) work
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
      sub = newSubGen (mkTreeLeaf Stub) (mkTreeLeaf Stub) work
   in insertTCSub sel sub tc

insertTCDot ::
  (EvalEnv m) => Selector -> Selector -> AST.UnaryExpr -> TreeCursor -> m TreeCursor
insertTCDot sel dotSel ue tc =
  let newSubGen :: TreeNode -> (TreeNode -> EvalMonad TreeNode) -> TreeNode
      newSubGen n op =
        TNUnaryOp $
          TreeUnaryOp
            { truOp = op,
              truArg = n,
              truRep = printf "\"dot %s\"" (show dotSel),
              truExpr = ue
            }
      errMsgGen :: TreeNode -> String
      errMsgGen n =
        printf
          "dot operator can not be used for %s, tc:\n%s"
          (showTreeType n)
          (showTreeCursor tc)
      dot :: (EvalEnv m) => TreeNode -> m TreeNode
      dot n = case n of
        TNScope {} -> case goTreeSel n dotSel of
          Just sub -> return sub
          -- incomplete case
          Nothing -> return $ newSubGen n dot
        TNDisj d ->
          if length (trdDefaults d) == 1
            then dot (trdDefaults d !! 0)
            else return $ newSubGen n dot
        TNLink {} -> return $ newSubGen n dot
        -- The unary operand could be a pending unary operator.
        TNUnaryOp {} -> return $ newSubGen n dot
        -- The unary operand could be a pending binary operator.
        TNBinaryOp {} -> return $ newSubGen n dot
        _ -> throwError $ errMsgGen n
      curSub = fromJust $ goDownTCSel sel tc
      newSub = newSubGen (fst curSub) dot
   in insertTCSub sel newSub tc

insertTCLeafValue :: (EvalEnv m) => Selector -> Value -> TreeCursor -> m TreeCursor
insertTCLeafValue sel v tc = let sub = mkTreeLeaf v in do insertTCSub sel sub tc

insertTCLink :: (EvalEnv m) => Selector -> Path -> TreeCursor -> m TreeCursor
insertTCLink sel tarPath tc = let sub = TNLink $ TreeLink {trlTarget = tarPath, trlFinal = Nothing} in insertTCSub sel sub tc

-- | finalizeTC evaluates the tree pointed by the cursor by traversing the tree and evaluating all nodes.
finalizeTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
finalizeTC tc@(tree, _) =
  let getSubTC :: (EvalEnv m) => Selector -> TreeCursor -> m TreeCursor
      getSubTC sel cursor = case goDownTCSel sel cursor of
        Just nextTC -> return nextTC
        Nothing ->
          throwError $
            printf
              "finalizeTC: can not get sub cursor with selector %s, cursor:\n%s"
              (show sel)
              (showTreeCursor cursor)
   in do
        dump $ printf "finalizeTC: node (%s) enter:\n%s" (showTreeType $ fst tc) (show $ fst tc)
        u <- case tree of
          TNLeaf _ -> return tc
          TNRoot _ -> getSubTC StartSelector tc >>= finalizeTC >>= propUpTC
          TNScope scope ->
            let goSub :: (EvalEnv m) => TreeCursor -> String -> m TreeCursor
                goSub acc k = getSubTC (StringSelector k) acc >>= finalizeTC >>= propUpTC
             in foldM goSub tc (Map.keys (trsSubs scope))
          TNList _ -> throwError "finalizeTC: TNList is not supported"
          TNUnaryOp _ -> getSubTC UnaryOpSelector tc >>= finalizeTC >>= propUpTC
          TNBinaryOp _ ->
            getSubTC (BinOpSelector L) tc
              >>= finalizeTC
              >>= propUpTC
              >>= getSubTC (BinOpSelector R)
              >>= finalizeTC
              >>= propUpTC
          TNLink {} -> do
            u <- followLinkTC tc
            dump $ printf "finalizeTC: TNLink:\n%s" (showTreeCursor u)
            return u
          TNDisj d ->
            let goSub :: (EvalEnv m) => TreeCursor -> Selector -> m TreeCursor
                goSub acc sel = getSubTC sel acc >>= finalizeTC >>= propUpTC
             in do
                  utc <- foldM goSub tc (map DisjDefaultSelector [0 .. length (trdDefaults d) - 1])
                  foldM goSub utc (map DisjDisjunctSelector [0 .. length (trdDisjuncts d) - 1])

        dump $ printf "finalizeTC: node (%s) leaves:\n%s" (showTreeType $ fst u) (show $ fst u)
        return u

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

prettyRevDeps :: Map.Map Path Path -> String
prettyRevDeps m =
  let p = intercalate ", " $ map (\(k, v) -> printf "(%s->%s)" (show k) (show v)) (Map.toList m)
   in "[" ++ p ++ "]"

pushNewNode :: (Runtime m) => (TreeCursor -> m TreeCursor) -> m ()
pushNewNode f = do
  tc <- gets ctxEvalTree >>= f
  modify $ \ctx -> ctx {ctxEvalTree = tc}

-- | Write the value to the parent block and return the value.
leaveCurNode :: (Runtime m) => m ()
leaveCurNode = do
  tc <- gets ctxEvalTree
  parTC <- propUpTC tc
  modify $ \ctx -> ctx {ctxEvalTree = parTC}
  dump $ printf "leaveCurNode: path: %s, parent treenode is:\n%s" (show $ pathFromTC tc) (show (fst parTC))
