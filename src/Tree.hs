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
  Atom (..),
  TNDisj (..),
  TNRoot (..),
  TNAtom (..),
  TreeNode (..),
  TNScope (..),
  TNBinaryOp (..),
  TNLink (..),
  TNBounds (..),
  TNConstraint (..),
  Config (..),
  Bound (..),
  dump,
  mkTree,
  goDownTCPath,
  goDownTCSel,
  goUpTC,
  insertTCBinaryOp,
  insertTCDot,
  insertTCAtom,
  insertTCVarLink,
  insertTCScope,
  insertTCUnaryOp,
  insertTCDisj,
  insertTCBound,
  mkTreeAtom,
  mkTreeDisj,
  mkTNConstraint,
  pathFromTC,
  propRootEvalTC,
  searchTCVar,
  showTreeCursor,
  isValueNode,
  isValueAtom,
  isValueConcrete,
  buildASTExpr,
  emptyTNScope,
  updateTNConstraintCnstr,
  updateTNConstraintAtom,
  mkTNUnaryOp,
  mkTNBinaryOp,
  evalTC,
  mkSubTC,
  propUpTCSel,
  substLinkTC,
  mkTNBinaryOpDir,
  mkTNBounds,
  isTreeBottom,
  getScalarValue,
  setOrigNodesTC,
  substTreeNode,
  bdOpRep,
  aToLiteral,
)
where

import qualified AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Logger (
  MonadLogger,
  logDebugN,
 )
import Control.Monad.Reader (MonadReader, ask)
import Control.Monad.Trans.Class (MonadTrans, lift)
import Data.ByteString.Builder (
  Builder,
  char7,
  integerDec,
  string7,
  toLazyByteString,
 )
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.List (intercalate, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust, isNothing)
import qualified Data.Set as Set
import Data.Text (pack)
import Path
import Text.Printf (printf)

dump :: (MonadLogger m) => String -> m ()
dump = logDebugN . pack

type EvalEnv m = (MonadError String m, MonadLogger m, MonadReader Config m)

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

-- TODO: move top out of Atom.
data Atom
  = Top
  | String String
  | Int Integer
  | Bool Bool
  | Null
  | Bottom String
  deriving (Ord)

-- | Show is only used for debugging.
instance Show Atom where
  show (String s) = s
  show (Int i) = show i
  show (Bool b) = show b
  show Top = "_"
  show Null = "null"
  show (Bottom msg) = "_|_: " ++ msg

instance Eq Atom where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) (Bottom _) (Bottom _) = True
  (==) Top Top = True
  (==) Null Null = True
  (==) _ _ = False

instance BuildASTExpr Atom where
  buildASTExpr = AST.litCons . aToLiteral

aToLiteral :: Atom -> AST.Literal
aToLiteral a = case a of
  Top -> AST.TopLit
  String s -> AST.StringLit $ AST.SimpleStringLit ((show AST.DoubleQuote) ++ s ++ (show AST.DoubleQuote))
  Int i -> AST.IntLit i
  Bool b -> AST.BoolLit b
  Null -> AST.NullLit
  Bottom _ -> AST.BottomLit

class ValueNode a where
  isValueNode :: a -> Bool
  isValueAtom :: a -> Bool
  isValueConcrete :: a -> Bool
  getScalarValue :: a -> Maybe Atom

class BuildASTExpr a where
  buildASTExpr :: a -> AST.Expression

class TreeRepBuilder a where
  repTree :: Int -> a -> Builder

data Tree = Tree
  { treeNode :: TreeNode
  , treeOrig :: Maybe Tree
  }

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

instance TreeRepBuilder Tree where
  repTree i t = tnStrBldr i t

tnStrBldr :: Int -> Tree -> Builder
tnStrBldr i t = case treeNode t of
  TNRoot sub -> content t i mempty [(string7 $ show StartSelector, (trRtSub sub))]
  TNAtom leaf -> content t i (string7 (show $ trAmAtom leaf)) emptyTreeFields
  TNStub -> content t i mempty emptyTreeFields
  TNLink _ -> content t i mempty emptyTreeFields
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
      [ (string7 "Atom", (mkTree (TNAtom $ trCnAtom c) Nothing))
      , (string7 "Cond", trCnCnstr c)
      ]
  TNBounds b -> content t i mempty (map (\(j, v) -> (integerDec j, v)) (zip [0 ..] (trBdList b)))
  TNRefCycleVar -> content t i mempty emptyTreeFields
 where
  emptyTreeFields :: [(Builder, Tree)]
  emptyTreeFields = []
  content :: (TreeRepBuilder a) => Tree -> Int -> Builder -> [(Builder, a)] -> Builder
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
                    <> repTree (j + 2) sub
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
  TNAtom _ -> "Leaf"
  TNBounds _ -> "Bounds"
  TNScope{} -> "Scope"
  TNList{} -> "List"
  TNUnaryOp{} -> "UnaryOp"
  TNBinaryOp{} -> "BinaryOp"
  TNLink{} -> "Link"
  TNDisj{} -> "Disj"
  TNStub -> "Stub"
  TNConstraint{} -> "Cnstr"
  TNRefCycleVar -> "RefCycleVar"

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNRoot _ -> "()"
  TNAtom _ -> "v"
  TNBounds _ -> "b"
  TNScope{} -> "{}"
  TNList{} -> "[]"
  TNUnaryOp o -> show $ truRep o
  TNBinaryOp o -> show $ trbRep o
  TNLink l -> printf "-> %s" (show $ trlTarget l)
  TNDisj{} -> "dj"
  TNStub -> "Stub"
  TNConstraint{} -> "Cnstr"
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
    TNAtom s -> buildASTExpr s
    TNBounds b -> buildASTExpr b
    TNStub -> AST.litCons AST.BottomLit
    TNConstraint _ -> buildASTExpr (fromJust $ treeOrig t)
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
  | -- | TNAtom contains an atom value.
    TNAtom TNAtom
  | TNBounds TNBounds
  | TNStub
  | TNConstraint TNConstraint
  | TNRefCycleVar

instance Eq TreeNode where
  (==) (TNRoot t1) (TNRoot t2) = t1 == t2
  (==) (TNScope s1) (TNScope s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNUnaryOp o1) (TNUnaryOp o2) = o1 == o2
  (==) (TNBinaryOp o1) (TNBinaryOp o2) = o1 == o2
  (==) (TNLink l1) (TNLink l2) = l1 == l2
  (==) (TNAtom l1) (TNAtom l2) = l1 == l2
  (==) TNStub TNStub = True
  (==) (TNConstraint c1) (TNConstraint c2) = c1 == c2
  (==) TNRefCycleVar TNRefCycleVar = True
  (==) (TNDisj dj1) n2@(TNAtom _) =
    if isNothing (trdDefault dj1)
      then False
      else treeNode (fromJust $ trdDefault dj1) == n2
  (==) (TNAtom a1) (TNDisj dj2) = (==) (TNDisj dj2) (TNAtom a1)
  (==) _ _ = False

instance ValueNode TreeNode where
  isValueNode n = case n of
    TNAtom _ -> True
    TNBounds _ -> False
    TNScope _ -> True
    TNList _ -> True
    TNDisj _ -> True
    TNConstraint _ -> True
    TNRefCycleVar -> False
    TNRoot _ -> False
    TNLink _ -> False
    TNUnaryOp _ -> False
    TNBinaryOp _ -> False
    TNStub -> False
  isValueAtom n = case n of
    TNAtom l -> case trAmAtom l of
      Top -> False
      Bottom _ -> False
      _ -> True
    _ -> False
  isValueConcrete n = case n of
    TNScope scope -> isScopeConcrete scope
    _ -> isValueAtom n
  getScalarValue n = case n of
    TNAtom s -> Just (trAmAtom s)
    TNConstraint c -> Just (trAmAtom $ trCnAtom c)
    _ -> Nothing

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
     in AST.litCons $ AST.StructLit $ map processField [(l, trsSubs s Map.! l) | l <- trsOrdLabels s]

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

data TNAtom = TreeAtom
  { trAmAtom :: Atom
  }

instance Show TNAtom where
  show (TreeAtom v) = show v

instance Eq TNAtom where
  (==) (TreeAtom v1) (TreeAtom v2) = v1 == v2

instance BuildASTExpr TNAtom where
  buildASTExpr (TreeAtom v) = buildASTExpr v

mkTreeAtom :: Atom -> Maybe Tree -> Tree
mkTreeAtom v = mkTree (TNAtom $ TreeAtom{trAmAtom = v})

isTreeBottom :: Tree -> Bool
isTreeBottom Tree{treeNode = TNAtom s} = case trAmAtom s of
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

mkTreeDisj :: Maybe Tree -> [Tree] -> Maybe Tree -> Tree
mkTreeDisj m js = mkTree (TNDisj $ TreeDisj{trdDefault = m, trdDisjuncts = js})

-- TNConstraint does not need to implement the BuildASTExpr.
data TNConstraint = TreeConstraint
  { trCnAtom :: TNAtom
  , trCnOrigAtom :: TNAtom
  -- ^ trCnOrigNode is the original atom value that was unified with other expression. Notice that the atom value can be
  -- changed by binary operations.
  , trCnCnstr :: Tree
  , trCnUnify :: forall m. (EvalEnv m) => Tree -> Tree -> TreeCursor -> m TreeCursor
  }

instance Eq TNConstraint where
  (==) (TreeConstraint a1 o1 c1 _) (TreeConstraint a2 o2 c2 _) =
    a1 == a2 && c1 == c2 && o1 == o2

mkTNConstraint :: TNAtom -> Tree -> (Tree -> Tree -> TreeCursor -> EvalMonad TreeCursor) -> TNConstraint
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

updateTNConstraintAtom :: TNAtom -> TNConstraint -> TNConstraint
updateTNConstraintAtom atom c = c{trCnAtom = atom}

data Bound
  = BdNE Atom
  | BdLT Integer
  | BdLE Integer
  | BdGT Integer
  | BdGE Integer
  | BdReMatch String
  | BdReNotMatch String
  | BdInt
  | BdString
  deriving (Eq, Ord)

bdOpRep :: Bound -> String
bdOpRep b = case b of
  BdNE _ -> show AST.NE
  BdLT _ -> show AST.LT
  BdLE _ -> show AST.LE
  BdGT _ -> show AST.GT
  BdGE _ -> show AST.GE
  BdReMatch _ -> show AST.ReMatch
  BdReNotMatch _ -> show AST.ReNotMatch
  BdInt -> "int"
  BdString -> "string"

instance Show Bound where
  show b = AST.exprStr $ buildASTExpr b

instance TreeRepBuilder Bound where
  repTree _ b = char7 '(' <> string7 (show b) <> char7 ')'

instance BuildASTExpr Bound where
  buildASTExpr b = buildBoundASTExpr b

buildBoundASTExpr :: Bound -> AST.Expression
buildBoundASTExpr b = case b of
  BdNE a -> litOp AST.NE (aToLiteral a)
  BdLT v -> intOp AST.LT v
  BdLE v -> intOp AST.LE v
  BdGT v -> intOp AST.GT v
  BdGE v -> intOp AST.GE v
  BdReMatch s -> litOp AST.ReMatch (AST.StringLit $ AST.SimpleStringLit s)
  BdReNotMatch s -> litOp AST.ReNotMatch (AST.StringLit $ AST.SimpleStringLit s)
  BdInt -> AST.idCons "int"
  BdString -> AST.idCons "string"
 where
  litOp :: AST.RelOp -> AST.Literal -> AST.Expression
  litOp op l =
    AST.ExprUnaryExpr $
      AST.UnaryExprUnaryOp
        (AST.UnaRelOp op)
        (AST.UnaryExprPrimaryExpr . AST.PrimExprOperand . AST.OpLiteral $ l)

  intOp :: AST.RelOp -> Integer -> AST.Expression
  intOp op i =
    AST.ExprUnaryExpr $
      AST.UnaryExprUnaryOp
        (AST.UnaRelOp op)
        (AST.UnaryExprPrimaryExpr . AST.PrimExprOperand . AST.OpLiteral . AST.IntLit $ i)

data TNBounds = TreeBounds
  { trBdList :: [Bound]
  }
  deriving (Eq)

instance BuildASTExpr TNBounds where
  buildASTExpr b = foldr1 (\x y -> AST.ExprBinaryOp AST.Unify x y) (map buildASTExpr (trBdList b))

mkTNBounds :: [Bound] -> Maybe Tree -> Tree
mkTNBounds bs = mkTree (TNBounds $ TreeBounds{trBdList = bs})

-- -- --

emptyTNScope :: TNScope
emptyTNScope =
  TreeScope
    { trsOrdLabels = []
    , trsVars = Set.empty
    , trsSubs = Map.empty
    }

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
          -- TNBounds b ->
          --   let
          --     l = trBdList b
          --     origBound = l !! i
          --    in
          --     returnTree $ TNBounds $ b{trBdList = take i l ++ [origBound{bdEp = sub}] ++ drop (i + 1) l}
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
          -- TNBounds b -> do
          --   l <- (trBdList b) !? i
          --   return (bdEp l)
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
    -- TNBounds b ->
    --   let
    --     l = trBdList b
    --     origBound = l !! i
    --     nl = TNBounds $ b{trBdList = take i l ++ [origBound{bdEp = subT}] ++ drop (i + 1) l}
    --    in
    --     return (substTreeNode nl parT, cs)
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
  -- TNBounds b ->
  --   let
  --     goSub :: (EvalEnv m) => TreeCursor -> Selector -> m TreeCursor
  --     goSub acc sel = getSubTC sel acc >>= f >>= levelUp sel
  --    in
  --     foldM goSub tc (map ListSelector [0 .. length (trBdList b) - 1])
  TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
  TNList _ -> throwError $ printf "%s: TNList is not implemented" header
  TNAtom _ -> return tc
  TNBounds _ -> return tc
  TNConstraint _ -> return tc
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
  TNAtom _ -> f tc
  TNBounds _ -> f tc
  -- TNBounds _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNConstraint _ -> f tc
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
      origAtom = mkTree (TNAtom $ trCnOrigAtom c) Nothing
      op = mkTree (TNBinaryOp $ mkTNBinaryOp AST.Unify (trCnUnify c) origAtom (trCnCnstr c)) Nothing
      unifyTC = (op, snd tc)
     in
      do
        dump $ printf "evalTC: constraint unify tc:\n%s" (showTreeCursor unifyTC)
        x <- evalTC unifyTC
        if (fst x) == origAtom
          then return (origAtom, snd tc)
          else throwError $ printf "evalTC: constraint not satisfied, %s != %s" (show (fst x)) (show origAtom)
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
  TNRefCycleVar -> return tc
  TNAtom _ -> return tc
  TNBounds _ -> return tc
  -- TNBounds _ -> traverseSubNodes evalTC tc
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
                        return $ Just (mkTree (TNAtom $ trCnAtom c) Nothing, snd tc)
                      _ -> do
                        dump $ printf "%s: resolves to tree node:\n%s" header (show tarNode)
                        return $ Just substTC
 where
  header :: String
  header = printf "followLink, link %s, path: %s" (show $ trlTarget link) (show $ pathFromTC tc)
  selfAbsPath = canonicalizePath $ pathFromTC tc

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
updateTCSub sel sub (par, cs) =
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

insertTCAtom :: (EvalEnv m) => Selector -> Atom -> TreeCursor -> m TreeCursor
insertTCAtom sel v tc =
  let sub = mkTreeAtom v Nothing
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

insertTCBound :: (EvalEnv m) => Selector -> Bound -> TreeCursor -> m TreeCursor
insertTCBound sel b tc =
  let sub = mkTNBounds [b] Nothing
   in insertTCSub sel sub tc
