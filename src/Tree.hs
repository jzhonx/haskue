{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module Tree (
  EvalEnv,
  EvalMonad,
  TNUnaryOp (..),
  TreeCursor,
  Tree (..),
  Value (..),
  TNDisj (..),
  TNRoot (..),
  TNScalar (..),
  TreeNode (..),
  TNScope (..),
  TNBinaryOp (..),
  TNLink (..),
  TNConstraint (..),
  TNRefCycle (..),
  Config (..),
  dump,
  mkTree,
  goDownTCPath,
  goDownTCSel,
  goUpTC,
  insertTCBinaryOp,
  insertTCDot,
  insertTCLeafValue,
  insertTCVarLink,
  -- insertTCList,
  insertTCScope,
  insertTCUnaryOp,
  insertTCDisj,
  mergeArgs,
  mkTreeLeaf,
  mkTreeDisj,
  mkTNConstraint,
  pathFromTC,
  propRootEvalTC,
  searchTCVar,
  vToE,
  showTreeCursor,
  isValueNode,
  isValueAtom,
  isValueConcrete,
  buildASTExpr,
  emptyTNScope,
  -- substRefCycleVar,
  updateTNConstraintCnstr,
  updateTNConstraintAtom,
  mkTNUnaryOp,
  mkTNBinaryOp,
  evalTC,
  mkSubTC,
  -- propUpEvalTC,
  emptyEvalState,
  propUpTCSel,
  substLinkTC,
  mkTNBinaryOpDir,
  isTreeBottom,
  getScalarValue,
  setOrigNodesTC,
  substTreeNode,
)
where

import qualified AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, catchError, runExcept, throwError)
import Control.Monad.Logger (
  MonadLogger,
  logDebugN,
 )
import Control.Monad.Reader (MonadReader, ask, asks, local)
import Control.Monad.State.Strict (
  MonadState,
  gets,
  modify,
 )
import Control.Monad.Trans.Class (MonadTrans, lift)
import Data.ByteString.Builder (
  Builder,
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

data EvalState = EvalState
  { esSubstScopeStack :: [Path]
  }

emptyEvalState :: EvalState
emptyEvalState = EvalState{esSubstScopeStack = []}

type EvalEnv m = (MonadError String m, MonadLogger m, MonadReader Config m, MonadState EvalState m)

data Config = Config
  { cfUnify :: forall m. (EvalEnv m) => Tree -> Tree -> TreeCursor -> m TreeCursor
  , cfCreateCnstr :: Bool
  }

type EvalMonad a = forall m. (EvalEnv m) => m a

newtype EnvMaybe m a = EnvMaybe {runEnvMaybe :: m (Maybe a)}

instance (Monad m) => Functor (EnvMaybe m) where
  fmap f (EnvMaybe ma) = EnvMaybe $ do
    a <- ma
    return $ fmap f a

instance (Monad m) => Applicative (EnvMaybe m) where
  pure = EnvMaybe . return . Just
  (EnvMaybe mf) <*> (EnvMaybe ma) = EnvMaybe $ do
    f <- mf
    a <- ma
    return $ f <*> a

instance (Monad m) => Monad (EnvMaybe m) where
  return = pure
  (>>=) :: EnvMaybe m a -> (a -> EnvMaybe m b) -> EnvMaybe m b
  (EnvMaybe ma) >>= f = EnvMaybe $ do
    am <- ma
    case am of
      Nothing -> return Nothing
      Just a -> runEnvMaybe $ f a

instance MonadTrans EnvMaybe where
  lift :: (Monad m) => m a -> EnvMaybe m a
  lift = EnvMaybe . fmap Just

newEvalEnvMaybe :: (EvalEnv m) => Maybe a -> EnvMaybe m a
newEvalEnvMaybe = EnvMaybe . return

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

-- exprIO :: (MonadIO m, MonadError String m) => Value -> m AST.Expression
-- context is irrelevant here
-- exprIO v = runStderrLoggingT $ evalStateT (vToE v) $ Context (TNScope emptyTNScope, [])

vToE :: (MonadError String m) => Value -> m AST.Expression
vToE Top = return $ AST.litCons AST.TopLit
vToE (String s) = return $ AST.litCons (AST.StringLit (AST.SimpleStringLit s))
vToE (Int i) = return $ AST.litCons (AST.IntLit i)
vToE (Bool b) = return $ AST.litCons (AST.BoolLit b)
vToE Null = return $ AST.litCons AST.NullLit
vToE (Bottom _) = return $ AST.litCons AST.BottomLit

class ValueNode a where
  isValueNode :: a -> Bool
  isValueAtom :: a -> Bool
  isValueConcrete :: a -> Bool
  getScalarValue :: a -> Maybe Value

class BuildASTExpr a where
  buildASTExpr :: a -> AST.Expression

data Tree = Tree
  { treeNode :: TreeNode
  , treeOrig :: Maybe Tree
  }

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

tnStrBldr :: Int -> Tree -> Builder
tnStrBldr i t = case treeNode t of
  TNRoot sub -> content t i mempty [(string7 $ show StartSelector, (trRtSub sub))]
  TNScalar leaf -> content t i (string7 (show $ trscValue leaf)) []
  TNStub -> content t i mempty []
  TNLink _ -> content t i mempty []
  TNScope s ->
    let ordLabels =
          string7 "ordLabels:"
            <> char7 '['
            <> string7 (intercalate ", " (trsOrdLabels s))
            <> char7 ']'
        fields = map (\k -> (string7 k, (trsSubs s) Map.! k)) (trsOrdLabels s)
     in content t i ordLabels fields
  TNList vs ->
    let fields = map (\(j, v) -> (integerDec j, v)) (zip [0 ..] (trLstSubs vs))
     in content t i mempty fields
  TNUnaryOp op -> content t i mempty [(string7 (show UnaryOpSelector), truArg op)]
  TNBinaryOp op ->
    content t i mempty [(string7 (show L), trbArgL op), (string7 (show R), trbArgR op)]
  TNDisj d ->
    let dfField = maybe [] (\v -> [(string7 (show $ DisjDefaultSelector), v)]) (trdDefault d)
        djFields = map (\(j, v) -> (string7 (show $ DisjDisjunctSelector j), v)) (zip [0 ..] (trdDisjuncts d))
     in content t i mempty (dfField ++ djFields)
  TNConstraint c ->
    content
      t
      i
      mempty
      [ (string7 "Atom", (mkTree (TNScalar $ trCnAtom c) Nothing))
      , (string7 "Cond", trCnCnstr c)
      ]
  TNRefCycle _ -> undefined
  -- TNRefCycle f ->
  --   content
  --     t
  --     i
  --     ((string7 $ show $ trlTarget . trRcOrigLink $ f) <> string7 " Orig:" <> string7 (showTreeType $ trRcOrigNode f))
  --     [(string7 "Form", trRcForm f)]
  TNRefCycleVar -> content t i mempty []
 where
  content :: Tree -> Int -> Builder -> [(Builder, Tree)] -> Builder
  content tree j meta fields =
    char7 '('
      <> string7 (showTreeSymbol tree)
      <> char7 ' '
      <> string7 "O:"
      <> (if isNothing (treeOrig tree) then string7 "N" else string7 "J")
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

showTreeIdent :: Tree -> Int -> String
showTreeIdent t i = LBS.unpack $ toLazyByteString $ tnStrBldr i t

showTreeType :: Tree -> String
showTreeType t = case treeNode t of
  TNRoot _ -> "Root"
  TNScalar _ -> "Leaf"
  TNScope{} -> "Scope"
  TNList{} -> "List"
  TNUnaryOp{} -> "UnaryOp"
  TNBinaryOp{} -> "BinaryOp"
  TNLink{} -> "Link"
  TNDisj{} -> "Disj"
  TNStub -> "Stub"
  TNConstraint{} -> "Cnstr"
  TNRefCycle{} -> "RefCycle"
  TNRefCycleVar -> "RefCycleVar"

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNRoot _ -> "()"
  TNScalar _ -> "v"
  TNScope{} -> "{}"
  TNList{} -> "[]"
  TNUnaryOp o -> show $ truRep o
  TNBinaryOp o -> show $ trbRep o
  TNLink l -> printf "-> %s" (show $ trlTarget l)
  TNDisj{} -> "dj"
  TNStub -> "Stub"
  TNConstraint{} -> "Cnstr"
  TNRefCycle{} -> "RefCycle"
  TNRefCycleVar -> "RefCycleVar"

instance Show Tree where
  show tree = showTreeIdent tree 0

instance BuildASTExpr Tree where
  buildASTExpr t = case treeNode t of
    TNRoot r -> buildASTExpr r
    TNScope s -> buildASTExpr s
    TNList l -> buildASTExpr l
    TNDisj d -> buildASTExpr d
    TNUnaryOp op -> if isJust (treeOrig t) then buildASTExpr (fromJust $ treeOrig t) else buildASTExpr op
    TNBinaryOp op -> if isJust (treeOrig t) then buildASTExpr (fromJust $ treeOrig t) else buildASTExpr op
    TNLink l -> buildASTExpr l
    TNScalar s -> buildASTExpr s
    TNStub -> AST.litCons AST.BottomLit
    TNConstraint _ -> buildASTExpr (fromJust $ treeOrig t)
    TNRefCycle f -> buildASTExpr f
    TNRefCycleVar -> AST.litCons AST.TopLit

mkTree :: TreeNode -> Maybe Tree -> Tree
mkTree n m = Tree n m

substTreeNode :: TreeNode -> Tree -> Tree
substTreeNode n t = t{treeNode = n}

-- | Tree represents a tree structure that contains values.
data TreeNode
  = TNRoot TNRoot
  | -- | TreeScope is a struct that contains a value and a map of selectors to Tree.
    TNScope TNScope
  | TNList TNList
  | TNDisj TNDisj
  | TNUnaryOp TNUnaryOp
  | TNBinaryOp TNBinaryOp
  | -- | Unless the target is a scalar, the TNLink should not be pruned.
    TNLink TNLink
  | -- | TNScalar contains an atom value. (could be scalar in the future)
    TNScalar TNScalar
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
  (==) (TNScalar l1) (TNScalar l2) = l1 == l2
  (==) TNStub TNStub = True
  (==) (TNConstraint c1) (TNConstraint c2) = c1 == c2
  (==) (TNRefCycle f1) (TNRefCycle f2) = f1 == f2
  (==) TNRefCycleVar TNRefCycleVar = True
  (==) _ _ = False

instance ValueNode TreeNode where
  isValueNode n = case n of
    TNScalar _ -> True
    TNScope _ -> True
    TNList _ -> True
    TNDisj _ -> True
    TNConstraint _ -> True
    TNRefCycle _ -> True
    TNRefCycleVar -> False
    TNRoot _ -> False
    TNLink _ -> False
    TNUnaryOp _ -> False
    TNBinaryOp _ -> False
    TNStub -> False
  isValueAtom n = case n of
    TNScalar l -> case trscValue l of
      Top -> False
      Bottom _ -> False
      _ -> True
    _ -> False
  isValueConcrete n = case n of
    TNScope scope -> isScopeConcrete scope
    _ -> isValueAtom n
  getScalarValue n = case n of
    TNScalar s -> Just (trscValue s)
    TNConstraint c -> Just (trscValue $ trCnAtom c)
    _ -> Nothing

-- getOrigNode n = case n of
--   TNRoot r -> trRtOrig r
--   TNScope s ->
--     maybe
--       Nothing
--       (\a -> Just (TNScope $ s{trsSubs = a}))
--       (mapM getOrigNode (trsSubs s))
--   TNList l -> maybe Nothing (\a -> Just (TNList $ l{trLstSubs = a})) (mapM getOrigNode (trLstSubs l))
--   TNDisj d -> trdOrig d
--   TNUnaryOp op -> maybe Nothing (\a -> Just (TNUnaryOp $ op{truArg = a})) (getOrigNode (truArg op))
--   TNBinaryOp op ->
--     maybe
--       Nothing
--       (\(l, r) -> Just (TNBinaryOp $ op{trbArgL = l, trbArgR = r}))
--       (mapM getOrigNode (trbArgL op, trbArgR op))
--   TNLink _ -> Just n
--   TNScalar s -> trscOrig s
--   TNStub -> Nothing
--   TNConstraint c -> Just (trcOrigNode c)
--   TNRefCycle _ -> Nothing
--   TNRefCycleVar -> Nothing
-- setOrigNode n o =
--   if isJust (getOrigNode n)
--     then n
--     else case n of
--       TNRoot r -> TNRoot $ r{trRtOrig = Just o}
--       TNDisj d -> TNDisj $ d{trdOrig = Just o}
--       TNScalar s -> TNScalar $ s{trscOrig = Just o}
--       TNConstraint c -> TNConstraint $ c{trcOrigNode = o}
--       TNScope _ -> n
--       TNList _ -> n
--       TNStub -> n
--       TNLink _ -> n
--       TNUnaryOp _ -> n
--       TNBinaryOp _ -> n
--       TNRefCycle _ -> n
--       TNRefCycleVar -> n

-- instance BuildASTExpr TreeNode where
--   buildASTExpr n = case n of
--     TNScalar l -> buildASTExpr l
--     TNRoot r -> buildASTExpr r
--     TNScope s -> buildASTExpr s
--     TNList _ -> undefined
--     TNDisj d -> buildASTExpr d
--     TNLink l -> buildASTExpr l
--     TNUnaryOp op -> buildASTExpr op
--     TNBinaryOp op -> buildASTExpr op
--     TNStub -> AST.litCons AST.BottomLit
--     TNConstraint c -> buildASTExpr
--     TNRefCycle f -> buildASTExpr f
--     TNRefCycleVar -> AST.litCons AST.TopLit

-- mapTreeLeafNode :: (Tree -> Tree) -> Tree -> Tree
-- mapTreeLeafNode f n = case n of
--   TNRoot t -> TNRoot $ t{trRtSub = f (trRtSub t)}
--   TNScope s -> TNScope $ s{trsSubs = Map.map f (trsSubs s)}
--   TNList ts -> TNList $ ts{trLstSubs = map f (trLstSubs ts)}
--   TNDisj d -> TNDisj $ d{trdDefaults = map f (trdDefaults d), trdDisjuncts = map f (trdDisjuncts d)}
--   TNUnaryOp op -> TNUnaryOp $ op{truArg = f (truArg op)}
--   TNBinaryOp op -> TNBinaryOp $ op{trbArgL = f (trbArgL op), trbArgR = f (trbArgR op)}
--   TNLink _ -> f n
--   TNScalar _ -> f n
--   TNStub -> f n
--   TNConstraint _ -> f n
--   TNRefCycle _ -> f n
--   TNRefCycleVar -> f TNRefCycleVar

-- foldPostTree :: (Tree -> a -> a) -> a -> Tree -> a
-- foldPostTree f acc n = case n of
--   TNRoot sub ->
--     let nacc = foldPostTree f acc (trRtSub sub)
--      in f n nacc
--   TNScope s ->
--     let nacc = foldr (flip (foldPostTree f)) acc (Map.elems (trsSubs s))
--      in f n nacc
--   TNList ts ->
--     let nacc = foldr (flip (foldPostTree f)) acc (trLstSubs ts)
--      in f n nacc
--   TNDisj d ->
--     let nacc = foldr (flip (foldPostTree f)) acc (trdDefaults d ++ trdDisjuncts d)
--      in f n nacc
--   TNUnaryOp op ->
--     let nacc = foldPostTree f acc (truArg op)
--      in f n nacc
--   TNBinaryOp op ->
--     let racc = foldPostTree f acc (trbArgR op)
--         lacc = foldPostTree f racc (trbArgL op)
--      in f n lacc
--   TNConstraint c ->
--     let lacc = foldPostTree f acc (TNScalar $ trcAtom c)
--         oacc = foldPostTree f lacc (trcCnstr c)
--      in f n oacc
--   TNRefCycle rc ->
--     let nacc = foldPostTree f acc (trRcForm rc)
--      in f n nacc
--   TNLink _ -> f n acc
--   TNScalar _ -> f n acc
--   TNStub -> f n acc
--   TNRefCycleVar -> f n acc

data TNRoot = TreeRoot
  { trRtSub :: Tree
  }

instance Eq TNRoot where
  (==) r1 r2 = trRtSub r1 == trRtSub r2

instance BuildASTExpr TNRoot where
  buildASTExpr r = buildASTExpr (trRtSub r)

data TNList = TreeList
  { trLstSubs :: [Tree]
  }

instance Eq TNList where
  (==) l1 l2 = trLstSubs l1 == trLstSubs l2

instance BuildASTExpr TNList where
  buildASTExpr l = undefined

data TNScope = TreeScope
  { trsOrdLabels :: [String]
  , trsVars :: Set.Set String
  , trsSubs :: Map.Map String Tree
  }

instance Eq TNScope where
  (==) s1 s2 = trsOrdLabels s1 == trsOrdLabels s2 && trsSubs s1 == trsSubs s2

instance BuildASTExpr TNScope where
  buildASTExpr s =
    let processField :: (String, Tree) -> (AST.Label, AST.Expression)
        processField (label, sub) =
          ( AST.Label . AST.LabelName $
              if Set.member label (trsVars s)
                then AST.LabelID label
                else AST.LabelString label
          , buildASTExpr sub
          )
     in AST.litCons $ AST.StructLit $ map processField (Map.toList (trsSubs s))

insertScopeNode :: TNScope -> String -> Tree -> TNScope
insertScopeNode s label sub =
  if Map.member label (trsSubs s)
    then s{trsSubs = Map.insert label sub (trsSubs s)}
    else
      let newLabels = trsOrdLabels s ++ [label]
          newFields = Map.insert label sub (trsSubs s)
       in s{trsOrdLabels = newLabels, trsSubs = newFields}

isScopeConcrete :: TNScope -> Bool
isScopeConcrete s = foldl (\acc (Tree{treeNode = x}) -> acc && isValueConcrete x) True (Map.elems (trsSubs s))

data TNUnaryOp = TreeUnaryOp
  { truRep :: AST.UnaryOp
  , truOp :: forall m. (EvalEnv m) => Tree -> TreeCursor -> m TreeCursor
  , truArg :: Tree
  }

instance BuildASTExpr TNUnaryOp where
  buildASTExpr op =
    let e = buildASTExpr (truArg op)
     in case e of
          (AST.ExprUnaryExpr ue) -> AST.ExprUnaryExpr $ AST.UnaryExprUnaryOp (truRep op) ue
          _ -> AST.litCons AST.BottomLit

instance Eq TNUnaryOp where
  (==) o1 o2 = (truRep o1 == truRep o2) && (truArg o1 == truArg o2)

mkTNUnaryOp :: AST.UnaryOp -> (Tree -> TreeCursor -> EvalMonad TreeCursor) -> Tree -> TNUnaryOp
mkTNUnaryOp rep op n =
  TreeUnaryOp
    { truOp = op
    , truArg = n
    , truRep = rep
    }

data TNBinaryOp = TreeBinaryOp
  { trbRep :: AST.BinaryOp
  , trbOp :: forall m. (EvalEnv m) => Tree -> Tree -> TreeCursor -> m TreeCursor
  , trbArgL :: Tree
  , trbArgR :: Tree
  }

instance BuildASTExpr TNBinaryOp where
  buildASTExpr op = AST.ExprBinaryOp (trbRep op) (buildASTExpr (trbArgL op)) (buildASTExpr (trbArgR op))

instance Eq TNBinaryOp where
  (==) o1 o2 = (trbRep o1 == trbRep o2) && (trbArgL o1 == trbArgL o2) && (trbArgR o1 == trbArgR o2)

mkTNBinaryOp ::
  AST.BinaryOp -> (Tree -> Tree -> TreeCursor -> EvalMonad TreeCursor) -> Tree -> Tree -> TNBinaryOp
mkTNBinaryOp rep op n1 n2 =
  TreeBinaryOp
    { trbOp = op
    , trbArgL = n1
    , trbArgR = n2
    , trbRep = rep
    }

mkTNBinaryOpDir ::
  AST.BinaryOp ->
  (Tree -> Tree -> TreeCursor -> EvalMonad TreeCursor) ->
  (BinOpDirect, Tree) ->
  (BinOpDirect, Tree) ->
  TNBinaryOp
mkTNBinaryOpDir rep op (d1, t1) (_, t2) =
  case d1 of
    L -> mkTNBinaryOp rep op t1 t2
    R -> mkTNBinaryOp rep op t2 t1

data TNLink = TreeLink
  { trlTarget :: Path
  , trlExpr :: AST.UnaryExpr
  }

instance Eq TNLink where
  (==) l1 l2 = trlTarget l1 == trlTarget l2

instance BuildASTExpr TNLink where
  buildASTExpr l = AST.ExprUnaryExpr $ trlExpr l

{- | Substitute the link node with the referenced node.
link should be the node that is currently being evaluated.
1. Find the target TC in the original tree.
2. Define the scope, which is the path of the target node.
3. Evaluate links that are outside the scope.
-}
substLinkTC :: (EvalEnv m) => TNLink -> TreeCursor -> m TreeCursor
substLinkTC link tc = do
  dump $ printf "substLinkTC: link (%s), path: %s starts" (show $ trlTarget link) (show $ pathFromTC tc)
  dump $ printf "substLinkTC, tc:\n%s" (showTreeCursor tc)
  res <- runEnvMaybe $ do
    tarTC <- EnvMaybe (followLink link tc)
    lift $
      dump $
        printf
          "substLinkTC: link (%s) target is found in the eval tree, tree: %s"
          (show $ trlTarget link)
          (show $ (fst tarTC))
    case treeNode (fst tarTC) of
      -- The link leads to a cycle head, which does not have the original node.
      TNRefCycleVar -> return tarTC
      _ -> do
        origTarTree <- newEvalEnvMaybe $ treeOrig (fst tarTC)
        return (origTarTree, snd tarTC)
  case res of
    Nothing -> do
      dump $ printf "substLinkTC: original target of the link (%s) is not found" (show $ trlTarget link)
      return tc
    Just tarOTC -> do
      dump $
        printf
          "substLinkTC: link (%s) target is found, path: %s, tree node:\n%s"
          (show $ trlTarget link)
          (show $ pathFromTC tarOTC)
          (show $ fst tarOTC)
      substTC <- evalOutScopeLinkTC (pathFromTC tarOTC) tarOTC
      dump $ printf "substLinkTC: link (%s) target is evaluated to:\n%s" (show $ trlTarget link) (show $ fst substTC)
      return substTC
 where
  -- substitute out-scope links with evaluated nodes.
  evalOutScopeLinkTC :: (EvalEnv m) => Path -> TreeCursor -> m TreeCursor
  evalOutScopeLinkTC p = traverseTC $ \x -> case treeNode (fst x) of
    -- Use the first var to determine if the link is in the scope. Then search the whole path.
    -- This handles the x.a case correctly.
    TNLink l -> do
      varPathMaybe <- runEnvMaybe $ do
        fstSel <- newEvalEnvMaybe $ headSel p
        -- If the variable is outside of the scope, then no matter what the following selectors are, the link is
        -- outside of the scope.
        varTC <- EnvMaybe $ searchTCVar fstSel x
        _ <- EnvMaybe $ searchTCPath (trlTarget l) x
        return $ pathFromTC varTC

      case varPathMaybe of
        Nothing -> return x
        Just varPath ->
          -- If the first selector of the link references the scope or nodes outside the scope, then evaluate the
          -- link.
          if p == varPath || (not $ isPrefix p varPath)
            then evalTC x
            else return x
    _ -> return x

data TNScalar = TreeScalar
  { trscValue :: Value
  }

instance Show TNScalar where
  show (TreeScalar v) = show v

instance Eq TNScalar where
  (==) (TreeScalar v1) (TreeScalar v2) = v1 == v2

instance BuildASTExpr TNScalar where
  buildASTExpr (TreeScalar v) = fromRight (AST.litCons AST.BottomLit) (runExcept $ vToE v)

mkTreeLeaf :: Value -> Maybe Tree -> Tree
mkTreeLeaf v = mkTree (TNScalar $ TreeScalar{trscValue = v})

isTreeBottom :: Tree -> Bool
isTreeBottom Tree{treeNode = TNScalar s} = case trscValue s of
  Bottom _ -> True
  _ -> False
isTreeBottom _ = False

data TNDisj = TreeDisj
  { trdDefault :: Maybe Tree
  , trdDisjuncts :: [Tree]
  }

instance Eq TNDisj where
  (==) (TreeDisj ds1 js1) (TreeDisj ds2 js2) = ds1 == ds2 && js1 == js2

instance BuildASTExpr TNDisj where
  buildASTExpr dj =
    if isJust (trdDefault dj)
      then buildASTExpr $ fromJust (trdDefault dj)
      else foldr1 (\x y -> AST.ExprBinaryOp AST.Disjunction x y) (map buildASTExpr (trdDisjuncts dj))

-- let def = buildASTExpr (trdDefault dj)
--     disjuncts = map buildASTExpr (trdDisjuncts dj)
--     list = if isNothing def then disjuncts else def
--  in foldr1 (\x y -> AST.ExprBinaryOp AST.Disjunction x y) list

mkTreeDisj :: Maybe Tree -> [Tree] -> Maybe Tree -> Tree
mkTreeDisj m js = mkTree (TNDisj $ TreeDisj{trdDefault = m, trdDisjuncts = js})

-- TNConstraint does not need to implement the BuildASTExpr.
data TNConstraint = TreeConstraint
  { trCnAtom :: TNScalar
  , trCnOrigAtom :: TNScalar
  -- ^ trCnOrigNode is the original atom value that was unified with other expression. Notice that the atom value can be
  -- changed by binary operations.
  , trCnCnstr :: Tree
  , trCnUnify :: forall m. (EvalEnv m) => Tree -> Tree -> TreeCursor -> m TreeCursor
  }

instance Eq TNConstraint where
  (==) (TreeConstraint a1 o1 c1 _) (TreeConstraint a2 o2 c2 _) =
    a1 == a2 && c1 == c2 && o1 == o2

mkTNConstraint :: TNScalar -> Tree -> (Tree -> Tree -> TreeCursor -> EvalMonad TreeCursor) -> TNConstraint
mkTNConstraint atom cnstr unify =
  TreeConstraint
    { trCnAtom = atom
    , trCnOrigAtom = atom
    , trCnCnstr = cnstr
    , trCnUnify = unify
    }

updateTNConstraintCnstr ::
  (BinOpDirect, Tree) ->
  (Tree -> Tree -> TreeCursor -> EvalMonad TreeCursor) ->
  TNConstraint ->
  TNConstraint
updateTNConstraintCnstr (d, t) unify c =
  let newBinOp =
        if d == L
          then TNBinaryOp $ TreeBinaryOp{trbRep = AST.Unify, trbOp = unify, trbArgL = t, trbArgR = trCnCnstr c}
          else TNBinaryOp $ TreeBinaryOp{trbRep = AST.Unify, trbOp = unify, trbArgL = trCnCnstr c, trbArgR = t}
   in c{trCnCnstr = mkTree newBinOp Nothing}

updateTNConstraintAtom :: TNScalar -> TNConstraint -> TNConstraint
updateTNConstraintAtom atom c = c{trCnAtom = atom}

data TNRefCycle = TreeRefCycle
  { trRcPath :: Path
  , trRcOrigExpr :: AST.Expression
  -- ^ trRcOrigNode is the original node that later is replaced by trRcForm.
  , trRcForm :: Tree
  , trRcOrig :: Maybe Tree
  }

instance Eq TNRefCycle where
  (==) (TreeRefCycle p1 _ f1 _) (TreeRefCycle p2 _ f2 _) = p1 == p2 && f1 == f2

instance BuildASTExpr TNRefCycle where
  buildASTExpr rc = trRcOrigExpr rc

-- evalRefCycle :: (EvalEnv m) => TNRefCycle -> m Tree
-- evalRefCycle rc =
--   return $
--     if hasRefCycleVar (trRcForm rc)
--       then TNRefCycle rc
--       else trRcForm rc
--   where
--     hasRefCycleVar :: Tree -> Bool
--     hasRefCycleVar n = foldPostTree (\x acc -> acc || x == TNRefCycleVar) False n
--
-- mkTNRefCycle :: Path -> AST.Expression -> Tree -> TNRefCycle

-- substRefCycleVar :: (EvalEnv m) => Tree -> TNRefCycle -> m Tree
-- substRefCycleVar t rc =
--   let form =
--         mapTreeLeafNode
--           ( \case
--               TNRefCycleVar -> t
--               x -> x
--           )
--           (trRcForm rc)
--    in do
--         dump $
--           printf
--             "substRefCycleVar: replaced RefCycleVar with %s, evaluated to form:\n%s"
--             (show t)
--             (show form)
--         return form

-- -- --

emptyTNScope :: TNScope
emptyTNScope =
  TreeScope
    { trsOrdLabels = []
    , trsVars = Set.empty
    , trsSubs = Map.empty
    }

-- mkTreeList :: [Value] -> Tree
-- mkTreeList vs = TNList $ TreeList{trLstSubs = map mkTreeLeaf vs}

{- | Insert a sub-tree to the tree node with the given selector.
Returns the updated parent tree node that contains the newly inserted sub-tree.
-}
insertSubTree ::
  (EvalEnv m) => Tree -> Selector -> Tree -> m Tree
insertSubTree parent sel sub =
  let parentNode = treeNode parent
   in case sel of
        StartSelector -> case parentNode of
          TNRoot t -> returnTree $ TNRoot $ t{trRtSub = sub}
          _ ->
            throwError errMsg
        StringSelector s -> case parentNode of
          TNScope parScope -> returnTree $ TNScope $ parScope{trsSubs = Map.insert s sub (trsSubs parScope)}
          _ ->
            throwError errMsg
        ListSelector i -> case parentNode of
          TNList vs -> returnTree $ TNList $ vs{trLstSubs = take i (trLstSubs vs) ++ [sub] ++ drop (i + 1) (trLstSubs vs)}
          _ -> throwError errMsg
        UnaryOpSelector -> case parentNode of
          TNUnaryOp op -> returnTree $ TNUnaryOp $ op{truArg = sub}
          _ -> throwError errMsg
        BinOpSelector dr -> case parentNode of
          TNBinaryOp op -> case dr of
            L -> returnTree $ TNBinaryOp $ op{trbArgL = sub}
            R -> returnTree $ TNBinaryOp $ op{trbArgR = sub}
          _ -> throwError errMsg
        DisjDefaultSelector -> case parentNode of
          TNDisj d -> returnTree $ TNDisj $ d{trdDefault = (trdDefault d)}
          _ -> throwError errMsg
        DisjDisjunctSelector i -> case parentNode of
          TNDisj d -> returnTree $ TNDisj $ d{trdDisjuncts = take i (trdDisjuncts d) ++ [sub] ++ drop (i + 1) (trdDisjuncts d)}
          _ -> throwError errMsg
        ParentSelector -> throwError "insertSubTree: cannot insert sub with ParentSelector"
 where
  errMsg :: String
  errMsg =
    printf
      "insertSubTree: cannot insert sub to %s, selector: %s, sub:\n%s\nparent:\n%s"
      (showTreeType parent)
      (show sel)
      (show sub)
      (show parent)

  returnTree :: (EvalEnv m) => TreeNode -> m Tree
  returnTree x = return (mkTree x (treeOrig parent))

-- step down the tree with the given selector.
-- This should only be used by TreeCursor.
goTreeSel :: Selector -> Tree -> Maybe Tree
goTreeSel sel t =
  let node = treeNode t
   in case sel of
        StartSelector -> case node of
          TNRoot sub -> Just (trRtSub sub)
          _ -> Nothing
        StringSelector s -> case node of
          TNScope scope -> Map.lookup s (trsSubs scope)
          _ -> Nothing
        ListSelector i -> case node of
          TNList vs -> (trLstSubs vs) !? i
          _ -> Nothing
        UnaryOpSelector -> case node of
          TNUnaryOp op -> Just (truArg op)
          _ -> Nothing
        BinOpSelector dr -> case node of
          TNBinaryOp op -> case dr of
            L -> Just (trbArgL op)
            R -> Just (trbArgR op)
          _ -> Nothing
        DisjDefaultSelector -> case node of
          TNDisj d -> trdDefault d
          _ -> Nothing
        DisjDisjunctSelector i -> case node of
          TNDisj d -> trdDisjuncts d !? i
          _ -> Nothing
        ParentSelector -> Nothing

-- | TreeCrumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type TreeCrumb = (Selector, Tree)

{- | TreeCursor is a pair of a value and a list of crumbs.
For example,
{
a: {
  b: {
    c: 42
  } // struct_c
} // struct_b
} // struct_a
Suppose the cursor is at the struct that contains the value 42. The cursor is
(struct_c, [("b", struct_b), ("a", struct_a)]).
-}
type TreeCursor = (Tree, [TreeCrumb])

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

mkSubTC :: Selector -> Tree -> TreeCursor -> TreeCursor
mkSubTC sel node tc = (node, (sel, fst tc) : snd tc)

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

goDownTCPathErr :: (MonadError String m) => Path -> String -> TreeCursor -> m TreeCursor
goDownTCPathErr p msg tc = case goDownTCPath p tc of
  Just c -> return c
  Nothing -> throwError msg

{- | Go down the TreeCursor with the given selector and return the new cursor.
It handles the case when the current node is a disjunction node.
-}
goDownTCSel :: Selector -> TreeCursor -> Maybe TreeCursor
goDownTCSel sel cursor = case go sel cursor of
  Just c -> Just c
  Nothing -> case treeNode (fst cursor) of
    TNDisj d -> case sel of
      StringSelector _ ->
        if isJust (trdDefault d)
          then goDownTCSel (DisjDefaultSelector) cursor >>= go sel
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

{- | propUp propagates the changes made to the tip of the block to the parent block.
The structure of the tree is not changed.
-}
propUpTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
propUpTC (t, []) = return (t, [])
propUpTC (subT, (sel, parT) : cs) = case sel of
  StartSelector ->
    if length cs > 0
      then throwError "StartSelector is not the first selector in the path"
      else case parNode of
        TNRoot t -> return (substTreeNode (TNRoot t{trRtSub = subT}) parT, [])
        _ -> throwError "propUpTC: root is not TNRoot"
  StringSelector s -> do
    case treeNode subT of
      TNRoot _ -> throwError "propUpTC: cannot propagate to root"
      TNList{} -> throwError "unimplemented"
      _ -> updateParScope parT s subT
  ListSelector i -> case parNode of
    TNList vs ->
      let subs = trLstSubs vs
          l = TNList $ vs{trLstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return (substTreeNode l parT, cs)
    _ -> throwError insertErrMsg
  UnaryOpSelector -> case parNode of
    TNUnaryOp op -> return (substTreeNode (TNUnaryOp $ op{truArg = subT}) parT, cs)
    _ -> throwError insertErrMsg
  BinOpSelector dr -> case dr of
    L -> case parNode of
      TNBinaryOp op -> return (substTreeNode (TNBinaryOp $ op{trbArgL = subT}) parT, cs)
      _ -> throwError insertErrMsg
    R -> case parNode of
      TNBinaryOp op -> return (substTreeNode (TNBinaryOp $ op{trbArgR = subT}) parT, cs)
      _ -> throwError insertErrMsg
  DisjDefaultSelector -> case parNode of
    TNDisj d ->
      return
        (substTreeNode (TNDisj $ d{trdDefault = (trdDefault d)}) parT, cs)
    _ -> throwError insertErrMsg
  DisjDisjunctSelector i -> case parNode of
    TNDisj d ->
      return
        ( substTreeNode (TNDisj $ d{trdDisjuncts = take i (trdDisjuncts d) ++ [subT] ++ drop (i + 1) (trdDisjuncts d)}) parT
        , cs
        )
    _ -> throwError insertErrMsg
  ParentSelector -> throwError "propUpTC: ParentSelector is not allowed"
 where
  parNode = treeNode parT
  updateParScope :: (MonadError String m) => Tree -> String -> Tree -> m TreeCursor
  updateParScope par label newSub = case treeNode par of
    TNScope parScope ->
      if isTreeBottom newSub
        then return (newSub, cs)
        else let newParNode = insertScopeNode parScope label newSub in return (substTreeNode (TNScope newParNode) parT, cs)
    _ -> throwError insertErrMsg

  -- TODO: insertParList

  insertErrMsg :: String
  insertErrMsg =
    printf
      "propUpTC: cannot insert child %s to parent %s, selector: %s, child:\n%s\nparent:\n%s"
      (showTreeType subT)
      (showTreeType parT)
      (show sel)
      (show subT)
      (show parT)

propUpTCSel :: (EvalEnv m) => Selector -> TreeCursor -> m TreeCursor
propUpTCSel _ (t, []) = return (t, [])
propUpTCSel sel tc@(_, (s, _) : _) =
  if s == sel
    then propUpTC tc
    else propUpTC tc >>= propUpTCSel sel

traverseSubNodes :: (EvalEnv m) => (TreeCursor -> EvalMonad TreeCursor) -> TreeCursor -> m TreeCursor
traverseSubNodes f tc = case treeNode (fst tc) of
  TNRoot _ -> getSubTC StartSelector tc >>= f >>= levelUp StartSelector
  TNScope scope ->
    let
      goSub :: (EvalEnv m) => TreeCursor -> String -> m TreeCursor
      goSub acc k =
        if isTreeBottom (fst acc)
          then return acc
          else getSubTC (StringSelector k) acc >>= f >>= levelUp (StringSelector k)
     in
      foldM goSub tc (Map.keys (trsSubs scope))
  TNDisj d ->
    let
      goSub :: (EvalEnv m) => TreeCursor -> Selector -> m TreeCursor
      goSub acc sel = getSubTC sel acc >>= f >>= levelUp sel
     in
      do
        utc <- maybe (return tc) (\_ -> goSub tc DisjDefaultSelector) (trdDefault d)
        foldM goSub utc (map DisjDisjunctSelector [0 .. length (trdDisjuncts d) - 1])
  TNUnaryOp _ -> getSubTC UnaryOpSelector tc >>= f >>= levelUp UnaryOpSelector
  TNBinaryOp _ ->
    getSubTC (BinOpSelector L) tc
      >>= f
      >>= levelUp (BinOpSelector L)
      >>= getSubTC (BinOpSelector R)
      >>= f
      >>= levelUp (BinOpSelector R)
  TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
  TNList _ -> throwError $ printf "%s: TNList is not implemented" header
  TNScalar _ -> return tc
  TNConstraint _ -> return tc
  TNRefCycle _ -> return tc
  TNRefCycleVar -> return tc
  TNLink _ -> return tc
 where
  header = "traverseSubNodes"

  levelUp :: (EvalEnv m) => Selector -> TreeCursor -> m TreeCursor
  levelUp = propUpTCSel

  getSubTC :: (EvalEnv m) => Selector -> TreeCursor -> m TreeCursor
  getSubTC sel cursor = do
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

{- | Traverse the leaves of the tree cursor in the following order
1. Traverse the current node.
2. Traverse the sub-tree with the selector.
-}
traverseTC :: (EvalEnv m) => (TreeCursor -> EvalMonad TreeCursor) -> TreeCursor -> m TreeCursor
traverseTC f tc = case treeNode n of
  TNRoot _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNScope _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNDisj _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNUnaryOp _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNBinaryOp _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
  TNList _ -> throwError $ printf "%s: TNList is not implemented" header
  TNScalar _ -> f tc
  TNConstraint _ -> f tc
  TNRefCycle _ -> f tc
  TNRefCycleVar -> f tc
  TNLink _ -> f tc
 where
  n = fst tc
  header = "traverseTC"

setOrigNodesTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
setOrigNodesTC = traverseTC f
 where
  f :: (EvalEnv m) => TreeCursor -> m TreeCursor
  f tc =
    let cur = fst tc
        updated = if isNothing (treeOrig cur) then cur{treeOrig = Just cur} else cur
     in return (updated, snd tc)

evalTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
evalTC tc = case treeNode (fst tc) of
  TNUnaryOp op -> truOp op (truArg op) tc
  TNBinaryOp op -> trbOp op (trbArgL op) (trbArgR op) tc
  TNConstraint c ->
    let
      origAtom = mkTree (TNScalar $ trCnOrigAtom c) Nothing
      op = mkTree (TNBinaryOp $ mkTNBinaryOp AST.Unify (trCnUnify c) origAtom (trCnCnstr c)) Nothing
      unifyTC = (op, snd tc)
     in
      do
        dump $ printf "evalTC: constraint unify tc:\n%s" (showTreeCursor unifyTC)
        x <- evalTC unifyTC
        let v = case treeNode (fst x) of
              TNDisj dj -> if isJust (trdDefault dj) then fromJust (trdDefault dj) else fst x
              _ -> fst x
        if v == origAtom
          then return (origAtom, snd tc)
          else throwError $ printf "evalTC: constraint not satisfied, %s != %s" (show v) (show origAtom)
  TNLink l -> do
    dump $ printf "evalTC: evaluate link %s" (show $ trlTarget l)
    res <- followLink l tc
    case res of
      Nothing -> return tc
      Just tarTC -> do
        u <- evalTC tarTC
        return (fst u, snd tc)
  TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
  TNList _ -> throwError $ printf "%s: TNList is not implemented" header
  TNRefCycle _ -> return tc
  TNRefCycleVar -> return tc
  TNScalar _ -> return tc
  TNScope _ -> traverseSubNodes evalTC tc
  TNDisj _ -> traverseSubNodes evalTC tc
  TNRoot _ -> traverseSubNodes evalTC tc
 where
  header :: String
  header = "evalTC"

-- TODO: Update the substituted tree cursor.
followLink :: (EvalEnv m) => TNLink -> TreeCursor -> m (Maybe TreeCursor)
followLink link tc = do
  res <- searchTCPath (trlTarget link) tc
  case res of
    Nothing -> return Nothing
    Just tarTC ->
      let tarAbsPath = canonicalizePath $ pathFromTC tarTC
       in if
            | tarAbsPath == selfAbsPath -> do
                dump $
                  printf
                    "%s: reference cycle detected: %s == %s."
                    header
                    (show $ pathFromTC tc)
                    (show $ pathFromTC tarTC)
                return $ Just (mkTree TNRefCycleVar Nothing, snd tc)
            | isPrefix tarAbsPath selfAbsPath -> throwError "structural cycle detected"
            | otherwise ->
                let tarNode = fst tarTC
                    substTC = (tarNode, snd tc)
                 in case treeNode tarNode of
                      TNLink newLink -> do
                        dump $ printf "%s: substitutes to another link. go to %s" header (show $ trlTarget newLink)
                        followLink newLink substTC
                      TNConstraint c -> do
                        dump $ printf "%s: substitutes to the atom value of the constraint" header
                        return $ Just (mkTree (TNScalar $ trCnAtom c) Nothing, snd tc)
                      -- TNRefCycle rc -> do
                      --   dump $ printf "%s substitutes to reference cycle. go to tree %s" header (showTreeType $ trRcOrigNode rc)
                      --   followLink (trRcOrigNode rc, snd tc)
                      _ -> do
                        dump $ printf "%s: resolves to tree node:\n%s" header (show tarNode)
                        return $ Just substTC
 where
  header :: String
  header = printf "followLink, link %s, path: %s" (show $ trlTarget link) (show $ pathFromTC tc)
  selfAbsPath = canonicalizePath $ pathFromTC tc

-- evalTNBinOpOrDelay :: (EvalEnv m) => (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> TreeCursor -> m TreeCursor

-- -- | Evaluate the node in the tree cursor.
-- evalTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
-- evalTC tc = case n of
--   TNScalar _ -> return tc
--   TNRoot _ -> pure tc >>= getSubTC StartSelector >>= evalTC >>= levelUp
--   TNScope scope ->
--     let goSub :: (EvalEnv m) => TreeCursor -> String -> m TreeCursor
--         goSub acc k = case fst acc of
--           TNScalar (TreeScalar (Bottom _)) -> return acc
--           _ -> getSubTC (StringSelector k) acc >>= evalTC >>= levelUp
--      in foldM goSub tc (Map.keys (trsSubs scope))
--   TNDisj d ->
--     let goSub :: (EvalEnv m) => TreeCursor -> Selector -> m TreeCursor
--         goSub acc sel = pure acc >>= getSubTC sel >>= evalTC >>= levelUp
--      in do
--           utc <- foldM goSub tc (map DisjDefaultSelector [0 .. length (trdDefaults d) - 1])
--           foldM goSub utc (map DisjDisjunctSelector [0 .. length (trdDisjuncts d) - 1])
--   TNUnaryOp op -> truOp op (truArg op) tc
--   TNBinaryOp op -> trbOp op (trbArgL op) (trbArgR op) tc
--   TNConstraint c ->
--     let atom = TNScalar $ trcAtom c
--      in do
--           cnstr <- evalTC (trcCnstr c, snd tc)
--           if fst cnstr == atom
--             then return (atom, snd tc)
--             else
--               throwError $
--                 printf "%s: constraint not satisfied, %s != %s" header (show cnstr) (show atom)
--   TNRefCycle _ -> return tc
--   -- node <- evalRefCycle f
--   -- return (node, snd tc)
--   TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
--   TNList _ -> throwError $ printf "%s: TNList is not implemented" header
--   TNRefCycleVar -> return tc
--   TNLink _ -> return tc
--   where
--     n = fst tc
--     header = "evalTC"
--
--     levelUp :: (EvalEnv m) => TreeCursor -> m TreeCursor
--     levelUp = propUpTC
--
--     getSubTC :: (EvalEnv m) => Selector -> TreeCursor -> m TreeCursor
--     getSubTC sel cursor = do
--       goDownTCSelErr
--         sel
--         ( printf
--             "%s: cannot get sub cursor with selector %s, path: %s, cursor:\n%s"
--             header
--             (show sel)
--             (show $ pathFromTC cursor)
--             (showTreeCursor cursor)
--         )
--         cursor

{- | propUp propagates the changes made to the tip of the block to the parent block.
The structure of the tree is not changed.
-}
propUpEvalTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
propUpEvalTC tc = evalTC tc >>= propUpTC

{- | Propagates the changes to the parent blocks until the top block.
It returns the root block.
-}
propRootEvalTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
propRootEvalTC (t, []) = return (t, [])
propRootEvalTC tc = propUpEvalTC tc >>= propRootEvalTC

-- propRootTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
-- propRootTC (t, []) = return (t, [])
-- propRootTC tc = propUpTC False tc >>= propRootTC

-- | Go from the current cursor to the root and then go down to the path.
goTCPathErr :: (EvalEnv m) => Path -> TreeCursor -> m TreeCursor
goTCPathErr p tc = go relSels tc
 where
  errMsg :: String
  errMsg = printf "goEvalTCPathErr: path %s not found" (show p)

  -- TODO: canonicalize path
  relSels :: [Selector]
  relSels = reverse $ getPath $ relPath (pathFromTC tc) p

  go :: (EvalEnv m) => [Selector] -> TreeCursor -> m TreeCursor
  go [] cursor = return cursor
  go (x : xs) cursor = case x of
    ParentSelector -> propUpTC cursor >>= go xs
    -- evalTC here is wasteful. TODO: evalTC once
    _ -> pure cursor >>= evalTC >>= goDownTCSelErr x errMsg >>= go xs

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
-- goTCPathMaybe :: (EvalEnv m) => Path -> TreeCursor -> m (Maybe TreeCursor)
-- goTCPathMaybe p tc = go relSels tc
--   where

{- | Search the tree cursor up to the root and return the tree cursor that points to the variable.
The cursor will also be propagated to the parent block.
-}
searchTCVar :: (EvalEnv m) => Selector -> TreeCursor -> m (Maybe TreeCursor)
searchTCVar sel@(StringSelector var) tc = case treeNode (fst tc) of
  TNScope scope -> case Map.lookup var (trsSubs scope) of
    Just node -> return $ Just (node, (StringSelector var, fst tc) : snd tc)
    Nothing -> propUpTC tc >>= searchTCVar sel
  _ -> propUpTC tc >>= searchTCVar sel
searchTCVar _ _ = return Nothing

-- | Search the tree cursor up to the root and return the tree cursor that points to the path.
searchTCPath :: (EvalEnv m) => Path -> TreeCursor -> m (Maybe TreeCursor)
searchTCPath p tc = runEnvMaybe $ do
  fstSel <- newEvalEnvMaybe $ headSel p
  base <- EnvMaybe $ searchTCVar fstSel tc
  tailP <- newEvalEnvMaybe $ tailPath p
  -- TODO: what if the base contains unevaluated nodes?
  newEvalEnvMaybe $ goDownTCPath tailP base

-- followLinkTC :: (EvalEnv m) => TreeCursor -> m (Maybe TreeCursor)
-- followLinkTC = go Set.empty
--   where
--     go :: (EvalEnv m) => Set.Set Path -> TreeCursor -> m (Maybe TreeCursor)
--     go visited cursor =
--       let tcPath = pathFromTC cursor
--        in if Set.member tcPath visited
--             then do
--               dump $ printf "followLinkTC: link cycle detected: %s" (show tcPath)
--               return $ Just (TNScalar $ TreeScalar Top, snd cursor)
--             else case fst cursor of
--               TNLink link -> do
--                 case searchTCPath (trlTarget link) cursor of
--                   Nothing -> return Nothing
--                   Just tarTC -> go (Set.insert tcPath visited) tarTC
--               _ -> return $ Just cursor

{- | Insert the tree node to the tree cursor with the given selector and returns the new cursor that focuses on the
newly inserted value (move down).
-}
insertTCSub :: (EvalEnv m) => Selector -> Tree -> TreeCursor -> m TreeCursor
insertTCSub sel sub tc@(par, cs) =
  scopeInsert (updateTCSub sel sub tc) $
    \s parScope ->
      maybe
        (updateTCSub sel sub tc)
        ( \extSub -> do
            Config{cfUnify = unify} <- ask
            let newSub =
                  mkTree
                    ( TNBinaryOp $
                        TreeBinaryOp
                          { trbRep = AST.Unify
                          , trbOp = unify
                          , trbArgL = extSub
                          , trbArgR = sub
                          }
                    )
                    Nothing -- It is still expanding the expressions.
            upar <- insertSubTree par sel newSub
            maybe (throwError errMsg) return $ goDownTCSel sel (upar, cs) >>= goDownTCSel (BinOpSelector R)
        )
        $ Map.lookup s (trsSubs parScope) >>= \case
          Tree{treeNode = TNStub} -> Nothing
          stree -> Just stree
 where
  errMsg :: String
  errMsg =
    printf
      "insertTCSub: cannot insert sub to %s with selector %s, sub:\n%s"
      (showTreeType par)
      (show sel)
      (show sub)
  scopeInsert :: (EvalEnv m) => (EvalMonad TreeCursor) -> (String -> TNScope -> EvalMonad TreeCursor) -> m TreeCursor
  scopeInsert defaultAct scopeAct = case (sel, par) of
    (StringSelector s, Tree{treeNode = TNScope parScope}) -> scopeAct s parScope
    _ -> defaultAct

{- | Update the tree node to the tree cursor with the given selector and returns the new cursor that focuses on the
updated value.
-}
updateTCSub :: (EvalEnv m) => Selector -> Tree -> TreeCursor -> m TreeCursor
updateTCSub sel sub tc@(par, cs) =
  let errMsg :: String
      errMsg =
        printf
          "updateTCSub: cannot insert sub. selector %s, par type: %s, sub:\n%s"
          (show sel)
          (showTreeType par)
          (show sub)
   in do
        u <- insertSubTree par sel sub
        -- dump $ printf "updateTCSub: sel: %s, tc:\n%s \nparent node:\n%s" (show sel) (showTreeCursor tc) (show u)
        goDownTCSelErr sel errMsg (u, cs)

-- | Insert a list of labels the tree and return the new cursor that contains the newly inserted value.
insertTCScope :: (EvalEnv m) => Selector -> [String] -> Set.Set String -> TreeCursor -> m TreeCursor
insertTCScope sel labels vars tc =
  let sub =
        mkTree
          ( TNScope $
              TreeScope
                { trsOrdLabels = labels
                , trsVars = vars
                , trsSubs = Map.fromList [(l, mkTree TNStub Nothing) | l <- labels]
                }
          )
          Nothing
   in insertTCSub sel sub tc

-- insertTCList :: (EvalEnv m) => Selector -> [Value] -> TreeCursor -> m TreeCursor
-- insertTCList sel vs tc = let sub = mkTreeList vs in insertTCSub sel sub tc

-- | Insert a unary operator that works for scalar values.
insertTCUnaryOp ::
  (EvalEnv m) => Selector -> AST.UnaryOp -> (Tree -> TreeCursor -> EvalMonad TreeCursor) -> TreeCursor -> m TreeCursor
insertTCUnaryOp sel rep f tc =
  let sub = mkTree (TNUnaryOp $ mkTNUnaryOp rep f (mkTree TNStub Nothing)) Nothing
   in insertTCSub sel sub tc

-- | Insert a binary operator that works for scalar values.
insertTCBinaryOp ::
  (EvalEnv m) =>
  Selector ->
  AST.BinaryOp ->
  (Tree -> Tree -> TreeCursor -> EvalMonad TreeCursor) ->
  TreeCursor ->
  m TreeCursor
insertTCBinaryOp sel rep f tc =
  let sub = mkTree (TNBinaryOp $ mkTNBinaryOp rep f (mkTree TNStub Nothing) (mkTree TNStub Nothing)) Nothing
   in insertTCSub sel sub tc

insertTCDisj ::
  (EvalEnv m) => Selector -> (Tree -> Tree -> TreeCursor -> EvalMonad TreeCursor) -> TreeCursor -> m TreeCursor
insertTCDisj sel f tc =
  let sub = mkTree (TNBinaryOp $ mkTNBinaryOp AST.Disjunction f (mkTree TNStub Nothing) (mkTree TNStub Nothing)) Nothing
   in insertTCSub sel sub tc

insertTCDot ::
  (EvalEnv m) => Selector -> Selector -> AST.UnaryExpr -> TreeCursor -> m TreeCursor
insertTCDot sel dotSel ue tc = do
  curSub <- goDownTCSelErr sel "insertTCDot: cannot get sub cursor" tc
  let tree = fst curSub
  newSub <- case treeNode tree of
    TNLink link -> return $ mkTree (TNLink $ link{trlTarget = appendSel dotSel (trlTarget link), trlExpr = ue}) Nothing
    _ -> throwError $ printf "insertTCDot: cannot insert link to non-link node:\n%s" (show tree)
  updateTCSub sel newSub tc

insertTCLeafValue :: (EvalEnv m) => Selector -> Value -> TreeCursor -> m TreeCursor
insertTCLeafValue sel v tc =
  let sub = mkTreeLeaf v Nothing
   in do insertTCSub sel sub tc

insertTCVarLink :: (EvalEnv m) => Selector -> String -> AST.UnaryExpr -> TreeCursor -> m TreeCursor
insertTCVarLink sel var e tc =
  let subPath = appendSel sel (pathFromTC tc)
      tarSel = StringSelector var
      tarPath = Path [tarSel]
   in let sub = mkTree (TNLink $ TreeLink{trlTarget = tarPath, trlExpr = e}) Nothing
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
--   Just (TNScalar (TreeScalar Top), _) -> insertTCLeafValue sel Top tc
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

-- -- | finalizeTC evaluates the tree pointed by the cursor by traversing the tree and evaluating all nodes.
-- finalizeTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
-- finalizeTC tc = do
--   dump $ printf "start resolving links for tree: ----\n%s" (show $ fst tc)
--   u <- evalStateT (resolveLinksTC tc) (DFSTCState Map.empty [] (Path []))
--   dump $ printf "start finalizing for tree: ----\n%s" (show $ fst u)
--   evalStateT (finalizeWalkTC u) (DFSTCState Map.empty [] (Path []))

-- data DFSTCState = DFSTCState
--   { dfsMarks :: Map.Map Path Int
--   , dfsRefCyclePathStack :: [(Path, TNLink)]
--   -- ^ (abs target_path, original TNLink)
--   , dfsRoute :: Path
--   }
--
-- data DFSTCConfig = DFSTCConfig
--   { dfsName :: String
--   , dfsSkipTNConstraint :: Bool
--   , dfsPreTCVisitor :: forall m. (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
--   , dfsPostTCVisitor :: forall m. (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> TreeCursor -> m TreeCursor
--   , dfsPropUpTC :: forall m. (EvalEnv m) => TreeCursor -> m TreeCursor
--   }

-- dfsTC :: (EvalEnv m) => DFSTCConfig -> TreeCursor -> m TreeCursor
-- dfsTC dfsConf tc =
--   do
--     dump $
--       printf
--         "%s: node (%s) tc_path: %s enter:\n%s"
--         header
--         (showTreeType $ fst tc)
--         (show path)
--         (show $ fst tc)
--     prex <- dfsPreTCVisitor dfsConf tc
--     modify $ \fs -> fs {dfsMarks = Map.insert path 1 (dfsMarks fs)}
--     x <- visit prex
--     modify $ \fs -> fs {dfsMarks = Map.insert path 2 (dfsMarks fs)}
--     postx <- dfsPostTCVisitor dfsConf tc x
--     dump $
--       printf
--         "%s: node (%s), tc_path: %s, leaves with node:\n%s"
--         header
--         (showTreeType $ fst postx)
--         (show path)
--         (show $ fst postx)
--     return postx
--   where
--     header :: String
--     header = dfsName dfsConf
--     path = pathFromTC tc
--
--     dfs :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
--     dfs = dfsTC dfsConf
--
--     levelUp :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
--     levelUp x = do
--       u <- dfsPropUpTC dfsConf x
--       modify $ \fs -> fs {dfsRoute = fromJust $ initPath (dfsRoute fs)}
--       return u
--
--     getSubTC :: (EvalEnv m, MonadState DFSTCState m) => Selector -> TreeCursor -> m TreeCursor
--     getSubTC sel cursor = do
--       u <-
--         goDownTCSelErr
--           sel
--           ( printf
--               "%s: cannot get sub cursor with selector %s, path: %s, cursor:\n%s"
--               header
--               (show sel)
--               (show $ pathFromTC cursor)
--               (showTreeCursor cursor)
--           )
--           cursor
--       modify $ \fs -> fs {dfsRoute = appendSel sel (dfsRoute fs)}
--       return u
--
--     visit :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
--     visit x = do
--       u <- case fst x of
--         TNScalar _ -> return x
--         TNRoot _ -> getSubTC StartSelector x >>= dfs >>= levelUp
--         TNScope scope ->
--           let goSub :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> String -> m TreeCursor
--               goSub acc k = case fst acc of
--                 TNScalar (TreeScalar (Bottom _)) -> return acc
--                 _ -> getSubTC (StringSelector k) acc >>= dfs >>= levelUp
--            in foldM goSub x (Map.keys (trsSubs scope))
--         TNList _ -> throwError $ printf "%s: TNList is not implemented" header
--         TNUnaryOp _ -> pure x >>= getSubTC UnaryOpSelector >>= dfs >>= levelUp
--         TNBinaryOp _ ->
--           pure x
--             >>= getSubTC (BinOpSelector L)
--             >>= dfs
--             >>= levelUp
--             >>= getSubTC (BinOpSelector R)
--             >>= dfs
--             >>= levelUp
--         TNDisj d ->
--           let goSub :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> Selector -> m TreeCursor
--               goSub acc sel = pure acc >>= getSubTC sel >>= dfs >>= levelUp
--            in do
--                 utc <- foldM goSub x (map DisjDefaultSelector [0 .. length (trdDefaults d) - 1])
--                 foldM goSub utc (map DisjDisjunctSelector [0 .. length (trdDisjuncts d) - 1])
--         TNConstraint _ ->
--           if dfsSkipTNConstraint dfsConf
--             then return x
--             else do
--               do
--                 pure x
--                 >>= getSubTC (BinOpSelector L)
--                 >>= dfs
--                 >>= levelUp
--                 >>= getSubTC (BinOpSelector R)
--                 >>= dfs
--                 >>= levelUp
--         TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
--         TNLink _ -> return x
--         -- Do not visit the node if it is a reference cycle.
--         TNRefCycle _ -> return x
--         TNRefCycleVar -> return x
--       evalTC u

-- resolveLinksTC :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
-- resolveLinksTC =
--   dfsTC
--     DFSTCConfig
--       { dfsName = "resolveLinksTC",
--         dfsSkipTNConstraint = True,
--         dfsPreTCVisitor = substituteLinkTC,
--         dfsPostTCVisitor = \origTC x -> do
--           stack <- gets dfsRefCyclePathStack
--           case listToMaybe stack of
--             Nothing -> return x
--             Just (absTarPath, link) ->
--               if absTarPath == pathFromTC x
--                 then do
--                   modify $ \fs -> fs {dfsRefCyclePathStack = drop 1 stack}
--                   return
--                     ( TNRefCycle $ TreeRefCycle {trRcForm = fst x, trRcOrigLink = link, trRcOrigNode = fst origTC},
--                       snd x
--                     )
--                 else return x,
--         dfsPropUpTC = propUpEvalTC
--       }

-- substOrig :: (EvalEnv m) => TreeCursor -> TreeCursor
-- substOrig = evalTC (
--   \x -> case fst x of
--     TNLink link -> replaceLink (pathFromTC tc) link x
--     _ -> undefined
-- )

{- |
param: tc is the cursor of the link node of the original tree that contains links.
1. Search the all children of the tree pointed by the cursor.
 a. If the child is a link and it is outside the tree's scope, then resolve the link.
 b. If not, keep the link.
-}

-- followLink :: (EvalEnv m) => Path -> TNLink -> TreeCursor -> m TreeCursor
-- followLink scoPath link otc =
--   case searchTCPath (trlTarget link) otc of
--     Nothing -> return otc
--     Just tarTC ->
--       if isPrefix scoAbsPath (canonicalizePath $ pathFromTC tarTC)
--         -- The link is inside the tree. Do not replace it.
--         then return otc
--         -- The link is outside the tree. Resolve it.
--         else do
--           u <- evalTC tarTC
--           return (fst u, snd otc)
--  where
--   scoAbsPath = canonicalizePath scoPath

-- tarPath = trlTarget link
-- tarTCMaybe :: (EvalEnv m) => m (Maybe TreeCursor)
-- tarTCMaybe = searchTCPath tarPath otc

-- follow :: (EvalEnv m) => Path -> Path -> TreeCursor -> m TreeCursor
-- follow scoAbsPath tarAbsPath tarTC =

-- substLinkTC :: (EvalEnv m) => TreeCursor -> m TreeCursor
-- substLinkTC tc = case fst tc of
--   TNLink link ->
--     let tarPath = trlTarget link
--         header :: String
--         header = printf "substLinkTC: cur: %s, link: %s," (show $ pathFromTC tc) (show tarPath)
--      in do
--           case searchTCPath tarPath tc of
--             Nothing -> do
--               dump $ printf "%s: link target not found" header
--               return tc
--             Just tar -> do
--               dump $
--                 printf
--                   "%s discovers path: %s, tree node:\n%s"
--                   header
--                   (show $ pathFromTC tar)
--                   (show $ fst tar)
--               let tarAbsPath = canonicalizePath $ pathFromTC tar
--                   selfAbsPath = canonicalizePath $ pathFromTC tc
--               if tarAbsPath == selfAbsPath
--                 then do
--                   dump $
--                     printf
--                       "%s reference cycle detected: %s == %s. Add path %s to stack"
--                       header
--                       (show $ pathFromTC tc)
--                       (show $ pathFromTC tar)
--                       (show $ trlTarget link)
--                   return (TNRefCycleVar, snd tc)
--                 else
--                   let node = fst tar
--                       newTC = (node, snd tc)
--                    in case node of
--                         TNLink newLink -> do
--                           dump $ printf "%s substitutes to another link. go to %s" header (show $ trlTarget newLink)
--                           substLinkTC newTC
--                         TNConstraint c -> do
--                           dump $ printf "%s substitutes to the atom value of the constraint" header
--                           return (TNScalar $ trcAtom c, snd tc)
--                         TNRefCycle rc -> do
--                           dump $ printf "%s substitutes to reference cycle. go to tree %s" header (showTreeType $ trRcOrigNode rc)
--                           substLinkTC (trRcOrigNode rc, snd tc)
--                         _ -> do
--                           dump $ printf "%s resolves to tree node:\n%s" header (show node)
--                           return newTC
--   _ -> return tc

-- finalizeWalkTC :: (EvalEnv m, MonadState DFSTCState m) => TreeCursor -> m TreeCursor
-- finalizeWalkTC tc =
--   dfsTC
--     DFSTCConfig
--       { dfsName = "finalizeWalkTC",
--         dfsSkipTNConstraint = False,
--         dfsPreTCVisitor = substituteLinkTC,
--         dfsPostTCVisitor = \_ x -> return x,
--         dfsPropUpTC = propUpEvalTC
--       }
--     tc

{- | Context
data Context = Context
{ -- curBlock is the current block that contains the variables.
A new block will replace the current one when a new block is entered.
A new block is entered when one of the following is encountered:
- The "{" token
- for and let clauses
ctxEvalTree :: TreeCursor
}
-}

-- prettyRevDeps :: Map.Map Path [Path] -> String
-- prettyRevDeps m =
--   let p = intercalate ", " $ map (\(k, v) -> printf "(%s->%s)" (show k) (show v)) (Map.toList m)
--    in "[" ++ p ++ "]"

-- pushNewNode :: (Runtime m) => (TreeCursor -> m TreeCursor) -> m ()
-- pushNewNode f = do
--   tc <- gets ctxEvalTree >>= f
--   modify $ \ctx -> ctx {ctxEvalTree = tc}
--
-- -- | Write the value to the parent block and return the value.
-- leaveCurNode :: (Runtime m) => Selector -> String -> m ()
-- leaveCurNode sel msg = do
--   tc <- gets ctxEvalTree
--   parTC <- go tc
--   modify $ \ctx -> ctx {ctxEvalTree = parTC}
--   dump $ printf "leaveCurNode: %s path: %s, parent treenode is:\n%s" msg (show $ pathFromTC tc) (show (fst parTC))
--   where
--     go :: (EvalEnv m) => TreeCursor -> m TreeCursor
--     go tc@(_, []) = return tc
--     go tc@(_, (s, _) : _) = do
--       parTC <- propUpEvalTC tc
--       if s == sel
--         then return parTC
--         else go parTC
