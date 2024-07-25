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
  Atom (..),
  BdNumCmp (..),
  BdNumCmpOp (..),
  BdStrMatch (..),
  BdType (..),
  Bound (..),
  Config (..),
  EvalEnv,
  EvalMonad,
  FuncType (..),
  Number (..),
  TNAtom (..),
  TNBounds (..),
  TNConstraint (..),
  TNDisj (..),
  TNFunc (..),
  TNLink (..),
  TNList (..),
  TNScope (..),
  TNBottom (..),
  Tree (..),
  TreeCursor,
  TreeNode (..),
  LabelAttr (..),
  ScopeLabelType (..),
  aToLiteral,
  bdRep,
  buildASTExpr,
  dump,
  evalTC,
  extendTC,
  replaceTCTip,
  getScalarValue,
  goDownTCPath,
  goDownTCSel,
  goDownTCSelErr,
  goUpTC,
  isTreeBottom,
  isValueAtom,
  isValueConcrete,
  isValueNode,
  mergeAttrs,
  mkBinaryOp,
  mkBinaryOpDir,
  mkNewTree,
  mkStub,
  mkSubTC,
  mkBounds,
  mkTNConstraint,
  mkTNFunc,
  mkTreeAtom,
  mkTreeDisj,
  mkBottom,
  mkUnaryOp,
  pathFromTC,
  propRootEvalTC,
  propUpTCSel,
  searchTCVar,
  setOrigNodesTC,
  showTreeCursor,
  substLinkTC,
  substTreeNode,
  updateTNConstraintAtom,
  updateTNConstraintCnstr,
  defaultLabelAttr,
  insertScopeSub,
  mkScope,
  emptyTNScope,
  mkList,
  indexBySel,
  indexByTree,
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
import Data.Text (pack)
import Debug.Trace
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
  | Float Double
  | Bool Bool
  | Null
  deriving (Ord)

-- | Show is only used for debugging.
instance Show Atom where
  show (String s) = s
  show (Int i) = show i
  show (Float f) = show f
  show (Bool b) = show b
  show Top = "_"
  show Null = "null"

instance Eq Atom where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Int i1) (Float i2) = fromIntegral i1 == i2
  (==) (Float i1) (Int i2) = i1 == fromIntegral i2
  (==) (Float f1) (Float f2) = f1 == f2
  (==) (Bool b1) (Bool b2) = b1 == b2
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
  Float f -> AST.FloatLit f
  Bool b -> AST.BoolLit b
  Null -> AST.NullLit

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
  TNAtom leaf -> content t i (string7 (show $ trAmAtom leaf)) emptyTreeFields
  TNStub -> content t i mempty emptyTreeFields
  TNLink _ -> content t i mempty emptyTreeFields
  TNScope s ->
    let ordLabels =
          string7 "ord:"
            <> char7 '['
            <> string7 (intercalate ", " (map show $ trsOrdLabels s))
            <> char7 ']'
        label :: ScopeSelector -> Builder
        label k =
          string7 (show k)
            <> case lbAttrType (trsAttrs s Map.! k) of
              SLRegular -> mempty
              SLRequired -> string7 "!"
              SLOptional -> string7 "?"
            <> if lbAttrIsVar (trsAttrs s Map.! k)
              then string7 ",v"
              else mempty
        fields = map (\k -> (label k, (trsSubs s) Map.! k)) (trsOrdLabels s)
     in content t i ordLabels fields
  TNList vs ->
    let fields = map (\(j, v) -> (integerDec j, v)) (zip [0 ..] (trLstSubs vs))
     in content t i mempty fields
  TNDisj d ->
    let dfField = maybe [] (\v -> [(string7 (show $ DisjDefaultSelector), v)]) (trdDefault d)
        djFields = map (\(j, v) -> (string7 (show $ DisjDisjunctSelector j), v)) (zip [0 ..] (trdDisjuncts d))
     in content t i mempty (dfField ++ djFields)
  TNConstraint c ->
    content
      t
      i
      mempty
      [ (string7 "Atom", (mkNewTree (TNAtom $ trCnAtom c)))
      , (string7 "Cond", trCnCnstr c)
      ]
  TNBounds b -> content t i mempty (map (\(j, v) -> (integerDec j, v)) (zip [0 ..] (trBdList b)))
  TNRefCycleVar -> content t i mempty emptyTreeFields
  TNFunc f ->
    let args = map (\(j, v) -> (integerDec j, v)) (zip [0 ..] (trfnArgs f))
     in content t i (string7 $ trfnName f) args
  TNBottom b -> content t i (string7 $ show b) emptyTreeFields
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
  TNAtom _ -> "Leaf"
  TNBounds _ -> "Bounds"
  TNScope{} -> "Scope"
  TNList{} -> "List"
  TNLink{} -> "Link"
  TNDisj{} -> "Disj"
  TNStub -> "Stub"
  TNConstraint{} -> "Cnstr"
  TNRefCycleVar -> "RefCycleVar"
  TNFunc{} -> "Func"
  TNBottom _ -> "Bottom"

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNAtom _ -> "v"
  TNBounds _ -> "b"
  TNScope{} -> "{}"
  TNList{} -> "[]"
  TNLink l -> printf "-> %s" (show $ trlTarget l)
  TNDisj{} -> "dj"
  TNStub -> ".."
  TNConstraint{} -> "Cnstr"
  TNRefCycleVar -> "RefCycleVar"
  TNFunc{} -> "fn"
  TNBottom _ -> "_|_"

instance Show Tree where
  show tree = showTreeIdent tree 0

instance BuildASTExpr Tree where
  buildASTExpr t = case treeNode t of
    TNScope s -> buildASTExpr s
    TNList l -> buildASTExpr l
    TNDisj d -> buildASTExpr d
    TNLink l -> buildASTExpr l
    TNAtom s -> buildASTExpr s
    TNBounds b -> buildASTExpr b
    TNStub -> AST.litCons . AST.StringLit $ AST.SimpleStringLit "STUB"
    TNConstraint _ -> buildASTExpr (fromJust $ treeOrig t)
    TNRefCycleVar -> AST.litCons AST.TopLit
    TNFunc fn -> if isJust (treeOrig t) then buildASTExpr (fromJust $ treeOrig t) else buildASTExpr fn
    TNBottom _ -> AST.litCons AST.BottomLit

mkNewTree :: TreeNode -> Tree
mkNewTree n = Tree n Nothing

mkStub :: Tree
mkStub = mkNewTree TNStub

substTreeNode :: TreeNode -> Tree -> Tree
substTreeNode n t = t{treeNode = n}

-- | Tree represents a tree structure that contains values.
data TreeNode
  = -- | TreeScope is a struct that contains a value and a map of selectors to Tree.
    TNScope TNScope
  | TNList TNList
  | TNDisj TNDisj
  | -- | Unless the target is a scalar, the TNLink should not be pruned.
    TNLink TNLink
  | -- | TNAtom contains an atom value.
    TNAtom TNAtom
  | TNBounds TNBounds
  | TNStub
  | TNConstraint TNConstraint
  | TNRefCycleVar
  | TNFunc TNFunc
  | TNBottom TNBottom

instance Eq TreeNode where
  (==) (TNScope s1) (TNScope s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
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
  (==) (TNFunc f1) (TNFunc f2) = f1 == f2
  (==) (TNBounds b1) (TNBounds b2) = b1 == b2
  (==) (TNBottom _) (TNBottom _) = True
  (==) _ _ = False

instance ValueNode TreeNode where
  isValueNode n = case n of
    TNAtom _ -> True
    TNBounds _ -> True
    TNScope _ -> True
    TNList _ -> True
    TNDisj _ -> True
    TNConstraint _ -> True
    TNRefCycleVar -> False
    TNLink _ -> False
    TNStub -> False
    TNFunc _ -> False
    TNBottom _ -> True
  isValueAtom n = case n of
    TNAtom l -> case trAmAtom l of
      Top -> False
      _ -> True
    _ -> False
  isValueConcrete n = case n of
    TNScope scope -> isScopeConcrete scope
    _ -> isValueAtom n
  getScalarValue n = case n of
    TNAtom s -> Just (trAmAtom s)
    TNConstraint c -> Just (trAmAtom $ trCnAtom c)
    _ -> Nothing

data TNList = TreeList
  { trLstSubs :: [Tree]
  }

instance Eq TNList where
  (==) l1 l2 = trLstSubs l1 == trLstSubs l2

instance BuildASTExpr TNList where
  buildASTExpr l =
    AST.litCons . AST.ListLit . AST.EmbeddingList $ map buildASTExpr (trLstSubs l)

mkList :: [Tree] -> Tree
mkList ts = mkNewTree (TNList $ TreeList{trLstSubs = ts})

data LabelAttr = LabelAttr
  { lbAttrType :: ScopeLabelType
  , lbAttrIsVar :: Bool
  }
  deriving (Show, Eq)

defaultLabelAttr :: LabelAttr
defaultLabelAttr = LabelAttr SLRegular True

mergeAttrs :: LabelAttr -> LabelAttr -> LabelAttr
mergeAttrs a1 a2 =
  LabelAttr
    { lbAttrType = if lbAttrType a1 <= lbAttrType a2 then lbAttrType a1 else lbAttrType a2
    , lbAttrIsVar = lbAttrIsVar a1 || lbAttrIsVar a2
    }

data ScopeLabelType = SLRegular | SLRequired | SLOptional
  deriving (Eq, Ord, Enum, Show)

data TNScope = TreeScope
  { trsOrdLabels :: [ScopeSelector]
  , trsSubs :: Map.Map ScopeSelector Tree
  , trsAttrs :: Map.Map ScopeSelector LabelAttr
  }

instance Eq TNScope where
  (==) s1 s2 = trsOrdLabels s1 == trsOrdLabels s2 && trsSubs s1 == trsSubs s2 && trsAttrs s1 == trsAttrs s2

instance BuildASTExpr TNScope where
  buildASTExpr s =
    let
      processField :: (ScopeSelector, LabelAttr, Tree) -> AST.Declaration
      processField (label, attr, sub) = case label of
        StringSelector sel ->
          AST.FieldDecl $
            AST.Field
              [ labelCons attr $
                  if lbAttrIsVar attr
                    then AST.LabelID sel
                    else AST.LabelString sel
              ]
              (buildASTExpr sub)
        DynamicSelector _ e ->
          AST.FieldDecl $
            AST.Field
              [ labelCons attr $ AST.LabelNameExpr e
              ]
              (buildASTExpr sub)

      labelCons :: LabelAttr -> AST.LabelName -> AST.Label
      labelCons attr =
        AST.Label . case lbAttrType attr of
          SLRegular -> AST.RegularLabel
          SLRequired -> AST.RequiredLabel
          SLOptional -> AST.OptionalLabel
     in
      AST.litCons $ AST.StructLit $ map processField [(l, trsAttrs s Map.! l, trsSubs s Map.! l) | l <- trsOrdLabels s]

emptyTNScope :: TNScope
emptyTNScope = TreeScope{trsOrdLabels = [], trsSubs = Map.empty, trsAttrs = Map.empty}

mkScope :: [ScopeSelector] -> [(ScopeSelector, LabelAttr, Tree)] -> Tree
mkScope ordLabels fields =
  let fieldMap = Map.fromList [(l, (a, t)) | (l, a, t) <- fields]
   in mkNewTree . TNScope $
        TreeScope{trsOrdLabels = ordLabels, trsSubs = Map.map snd fieldMap, trsAttrs = Map.map fst fieldMap}

insertScopeSub :: TNScope -> ScopeSelector -> Maybe LabelAttr -> Tree -> TNScope
insertScopeSub s label attrMaybe sub =
  if Map.member label (trsSubs s)
    then
      s
        { trsSubs = Map.insert label sub (trsSubs s)
        , trsAttrs = Map.insert label (newAttr) (trsAttrs s)
        }
    else
      let newLabels = trsOrdLabels s ++ [label]
          newFields = Map.insert label sub (trsSubs s)
       in s{trsOrdLabels = newLabels, trsSubs = newFields, trsAttrs = Map.insert label (newAttr) (trsAttrs s)}
 where
  newAttr = case attrMaybe of
    Just attr -> attr
    Nothing -> case trsAttrs s Map.!? label of
      Just attr -> attr
      Nothing -> LabelAttr SLRegular False

isScopeConcrete :: TNScope -> Bool
isScopeConcrete s = foldl (\acc (Tree{treeNode = x}) -> acc && isValueConcrete x) True (Map.elems (trsSubs s))

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

mkTreeAtom :: Atom -> Tree
mkTreeAtom v = mkNewTree (TNAtom $ TreeAtom{trAmAtom = v})

isTreeBottom :: Tree -> Bool
isTreeBottom (Tree (TNBottom _) _) = True
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

mkTreeDisj :: Maybe Tree -> [Tree] -> Tree
mkTreeDisj m js = mkNewTree (TNDisj $ TreeDisj{trdDefault = m, trdDisjuncts = js})

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
          then TNFunc $ mkBinaryOp AST.Unify unify t (trCnCnstr c)
          else TNFunc $ mkBinaryOp AST.Unify unify (trCnCnstr c) t
   in c{trCnCnstr = mkNewTree newBinOp}

updateTNConstraintAtom :: TNAtom -> TNConstraint -> TNConstraint
updateTNConstraintAtom atom c = c{trCnAtom = atom}

data Number = NumInt Integer | NumFloat Double
  deriving (Eq)

instance Ord Number where
  compare (NumInt i1) (NumInt i2) = compare i1 i2
  compare (NumFloat f1) (NumFloat f2) = compare f1 f2
  compare (NumInt i) (NumFloat f) = compare (fromIntegral i) f
  compare (NumFloat f) (NumInt i) = compare f (fromIntegral i)

data BdNumCmpOp
  = BdLT
  | BdLE
  | BdGT
  | BdGE
  deriving (Eq, Enum, Ord)

instance Show BdNumCmpOp where
  show o = show $ case o of
    BdLT -> AST.LT
    BdLE -> AST.LE
    BdGT -> AST.GT
    BdGE -> AST.GE

data BdNumCmp = BdNumCmpCons BdNumCmpOp Number
  deriving (Eq)

data BdStrMatch
  = BdReMatch String
  | BdReNotMatch String
  deriving (Eq)

data BdType
  = BdBool
  | BdInt
  | BdFloat
  | BdNumber
  | BdString
  deriving (Eq, Enum, Bounded)

instance Show BdType where
  show BdBool = "bool"
  show BdInt = "int"
  show BdFloat = "float"
  show BdNumber = "number"
  show BdString = "string"

data Bound
  = BdNE Atom
  | BdNumCmp BdNumCmp
  | BdStrMatch BdStrMatch
  | BdType BdType
  | BdIsAtom Atom -- helper type
  deriving (Eq)

instance Show Bound where
  show b = AST.exprStr $ buildASTExpr b

instance TreeRepBuilder Bound where
  repTree _ b = char7 '(' <> string7 (show b) <> char7 ')'

instance BuildASTExpr Bound where
  buildASTExpr b = buildBoundASTExpr b

bdRep :: Bound -> String
bdRep b = case b of
  BdNE _ -> show $ AST.NE
  BdNumCmp (BdNumCmpCons o _) -> show o
  BdStrMatch m -> case m of
    BdReMatch _ -> show AST.ReMatch
    BdReNotMatch _ -> show AST.ReNotMatch
  BdType t -> show t
  BdIsAtom _ -> "="

buildBoundASTExpr :: Bound -> AST.Expression
buildBoundASTExpr b = case b of
  BdNE a -> litOp AST.NE (aToLiteral a)
  BdNumCmp (BdNumCmpCons o n) -> case o of
    BdLT -> numOp AST.LT n
    BdLE -> numOp AST.LE n
    BdGT -> numOp AST.GT n
    BdGE -> numOp AST.GE n
  BdStrMatch m -> case m of
    BdReMatch s -> litOp AST.ReMatch (AST.StringLit $ AST.SimpleStringLit s)
    BdReNotMatch s -> litOp AST.ReNotMatch (AST.StringLit $ AST.SimpleStringLit s)
  BdType t -> AST.idCons (show t)
  BdIsAtom a -> AST.litCons (aToLiteral a)
 where
  litOp :: AST.RelOp -> AST.Literal -> AST.Expression
  litOp op l =
    AST.ExprUnaryExpr $
      AST.UnaryExprUnaryOp
        (AST.UnaRelOp op)
        (AST.UnaryExprPrimaryExpr . AST.PrimExprOperand . AST.OpLiteral $ l)

  numOp :: AST.RelOp -> Number -> AST.Expression
  numOp op n =
    AST.ExprUnaryExpr $
      AST.UnaryExprUnaryOp
        (AST.UnaRelOp op)
        ( AST.UnaryExprPrimaryExpr . AST.PrimExprOperand . AST.OpLiteral $ case n of
            NumInt i -> AST.IntLit i
            NumFloat f -> AST.FloatLit f
        )

data TNBounds = TreeBounds
  { trBdList :: [Bound]
  }
  deriving (Eq)

instance BuildASTExpr TNBounds where
  buildASTExpr b = foldr1 (\x y -> AST.ExprBinaryOp AST.Unify x y) (map buildASTExpr (trBdList b))

mkBounds :: [Bound] -> Tree
mkBounds bs = mkNewTree (TNBounds $ TreeBounds{trBdList = bs})

data FuncType = UnaryOpFunc | BinaryOpFunc | DisjFunc | Function
  deriving (Eq, Enum)

data TNFunc = TreeFunc
  { trfnName :: String
  , trfnType :: FuncType
  , trfnArgs :: [Tree]
  , trfnExprGen :: [Tree] -> AST.Expression
  , trfnFunc :: forall m. (EvalEnv m) => [Tree] -> TreeCursor -> m TreeCursor
  }

instance BuildASTExpr TNFunc where
  buildASTExpr fn = trfnExprGen fn (trfnArgs fn)

instance Eq TNFunc where
  (==) f1 f2 = trfnName f1 == trfnName f2 && trfnArgs f1 == trfnArgs f2 && trfnType f1 == trfnType f2

mkTNFunc ::
  String -> FuncType -> ([Tree] -> TreeCursor -> EvalMonad TreeCursor) -> ([Tree] -> AST.Expression) -> [Tree] -> TNFunc
mkTNFunc name typ f g args =
  TreeFunc
    { trfnFunc = f
    , trfnType = typ
    , trfnExprGen = g
    , trfnName = name
    , trfnArgs = args
    }

mkUnaryOp :: AST.UnaryOp -> (Tree -> TreeCursor -> EvalMonad TreeCursor) -> Tree -> TNFunc
mkUnaryOp op f n =
  TreeFunc
    { trfnFunc = g
    , trfnType = UnaryOpFunc
    , trfnExprGen = gen
    , trfnName = show op
    , trfnArgs = [n]
    }
 where
  g :: [Tree] -> TreeCursor -> EvalMonad TreeCursor
  g (x : []) = f x
  g _ = \_ -> throwError "mkTNUnaryOp: invalid number of arguments"

  gen :: [Tree] -> AST.Expression
  gen (x : []) = buildUnaryExpr x
  gen _ = AST.litCons AST.BottomLit

  buildUnaryExpr :: Tree -> AST.Expression
  buildUnaryExpr t = case buildASTExpr t of
    (AST.ExprUnaryExpr ue) -> AST.ExprUnaryExpr $ AST.UnaryExprUnaryOp op ue
    e ->
      AST.ExprUnaryExpr $
        AST.UnaryExprUnaryOp
          op
          (AST.UnaryExprPrimaryExpr . AST.PrimExprOperand $ AST.OpExpression e)

mkBinaryOp ::
  AST.BinaryOp -> (Tree -> Tree -> TreeCursor -> EvalMonad TreeCursor) -> Tree -> Tree -> TNFunc
mkBinaryOp op f l r =
  TreeFunc
    { trfnFunc = g
    , trfnType = case op of
        AST.Disjunction -> DisjFunc
        _ -> BinaryOpFunc
    , trfnExprGen = gen
    , trfnName = show op
    , trfnArgs = [l, r]
    }
 where
  g :: [Tree] -> TreeCursor -> EvalMonad TreeCursor
  g (x : y : []) = f x y
  g _ = \_ -> throwError "mkTNUnaryOp: invalid number of arguments"

  gen :: [Tree] -> AST.Expression
  gen (x : y : []) = AST.ExprBinaryOp op (buildASTExpr x) (buildASTExpr y)
  gen _ = AST.litCons AST.BottomLit

mkBinaryOpDir ::
  AST.BinaryOp ->
  (Tree -> Tree -> TreeCursor -> EvalMonad TreeCursor) ->
  (BinOpDirect, Tree) ->
  (BinOpDirect, Tree) ->
  TNFunc
mkBinaryOpDir rep op (d1, t1) (_, t2) =
  case d1 of
    L -> mkBinaryOp rep op t1 t2
    R -> mkBinaryOp rep op t2 t1

data TNBottom = TreeBottom
  { trBmMsg :: String
  }

instance Eq TNBottom where
  (==) _ _ = True

instance BuildASTExpr TNBottom where
  buildASTExpr _ = AST.litCons $ AST.BottomLit

instance Show TNBottom where
  show (TreeBottom m) = m

mkBottom :: String -> Tree
mkBottom msg = mkNewTree (TNBottom $ TreeBottom{trBmMsg = msg})

-- -- --

-- step down the tree with the given selector.
-- This should only be used by TreeCursor.
goTreeSel :: Selector -> Tree -> Maybe Tree
goTreeSel sel t =
  case sel of
    RootSelector -> Just t
    ScopeSelector s -> case node of
      TNScope scope -> Map.lookup s (trsSubs scope)
      _ -> Nothing
    IndexSelector i -> case node of
      TNList vs -> (trLstSubs vs) !? i
      _ -> Nothing
    FuncArgSelector i -> case node of
      TNFunc fn -> (trfnArgs fn) !? i
      _ -> Nothing
    DisjDefaultSelector -> case node of
      TNDisj d -> trdDefault d
      _ -> Nothing
    DisjDisjunctSelector i -> case node of
      TNDisj d -> trdDisjuncts d !? i
      _ -> Nothing
    ParentSelector -> Nothing
 where
  node = treeNode t

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

{- | Go down the TreeCursor with the given selector and return the new cursor.
It handles the case when the current node is a disjunction node.
-}
goDownTCSel :: Selector -> TreeCursor -> Maybe TreeCursor
goDownTCSel sel cursor = case go sel cursor of
  Just c -> Just c
  Nothing -> case treeNode (fst cursor) of
    TNDisj d ->
      if isJust (trdDefault d)
        then goDownTCSel DisjDefaultSelector cursor >>= go sel
        else Nothing
    _ -> Nothing
 where
  go :: Selector -> TreeCursor -> Maybe TreeCursor
  go s (tree, vs) = do
    nextTree <- goTreeSel s tree
    return (nextTree, (s, tree) : vs)

goDownTCSelErr :: (MonadError String m) => Selector -> TreeCursor -> m TreeCursor
goDownTCSelErr sel tc = case goDownTCSel sel tc of
  Just c -> return c
  Nothing -> throwError $ printf "cannot go down tree with selector %s, tree: %s" (show sel) (show $ fst tc)

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
propUpTC tc@(subT, (sel, parT) : cs) = case sel of
  ScopeSelector s -> updateParScope parT s subT
  IndexSelector i -> case parNode of
    TNList vs ->
      let subs = trLstSubs vs
          l = TNList $ vs{trLstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return (substTreeNode l parT, cs)
    _ -> throwError insertErrMsg
  FuncArgSelector i -> case parNode of
    TNFunc fn ->
      let args = trfnArgs fn
          l = TNFunc $ fn{trfnArgs = take i args ++ [subT] ++ drop (i + 1) args}
       in return (substTreeNode l parT, cs)
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
  RootSelector -> throwError "propUpTC: RootSelector is not allowed"
 where
  parNode = treeNode parT
  updateParScope :: (MonadError String m) => Tree -> ScopeSelector -> Tree -> m TreeCursor
  updateParScope par label newSub = case treeNode par of
    TNScope parScope ->
      if isTreeBottom newSub
        then return (newSub, cs)
        else
          let
            newParNode = insertScopeSub parScope label Nothing newSub
           in
            return (substTreeNode (TNScope newParNode) parT, cs)
    _ -> throwError insertErrMsg

  insertErrMsg :: String
  insertErrMsg =
    printf
      "propUpTC: cannot insert child %s to parent %s, path: %s, selector: %s, child:\n%s\nparent:\n%s"
      (showTreeType subT)
      (showTreeType parT)
      (show $ pathFromTC tc)
      (show sel)
      (show subT)
      (show parT)

propUpTCSel :: (EvalEnv m) => Selector -> TreeCursor -> m TreeCursor
propUpTCSel _ (t, []) = return (t, [])
propUpTCSel sel tc@(_, (s, _) : _) =
  if s == sel
    then propUpTC tc
    else propUpTC tc >>= propUpTCSel sel

-- | Traverse all the sub nodes of the tree.
traverseSubNodes :: (EvalEnv m) => (TreeCursor -> EvalMonad TreeCursor) -> TreeCursor -> m TreeCursor
traverseSubNodes f tc = case treeNode (fst tc) of
  TNScope scope ->
    let
      goSub :: (EvalEnv m) => TreeCursor -> ScopeSelector -> m TreeCursor
      goSub acc k =
        if isTreeBottom (fst acc)
          then return acc
          else getSubTC (ScopeSelector k) acc >>= f >>= levelUp (ScopeSelector k)
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
  TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
  TNList l ->
    let
      goSub :: (EvalEnv m) => TreeCursor -> Int -> m TreeCursor
      goSub acc i =
        if isTreeBottom (fst acc)
          then return acc
          else getSubTC (IndexSelector i) acc >>= f >>= levelUp (IndexSelector i)
     in
      foldM goSub tc [0 .. length (trLstSubs l) - 1]
  TNFunc fn ->
    let
      goSub :: (EvalEnv m) => TreeCursor -> Int -> m TreeCursor
      goSub acc i =
        if isTreeBottom (fst acc)
          then return acc
          else getSubTC (FuncArgSelector i) acc >>= f >>= levelUp (FuncArgSelector i)
     in
      foldM goSub tc [0 .. length (trfnArgs fn) - 1]
  TNAtom _ -> return tc
  TNBounds _ -> return tc
  TNConstraint _ -> return tc
  TNRefCycleVar -> return tc
  TNLink _ -> return tc
  TNBottom _ -> return tc
 where
  header = "traverseSubNodes"

  levelUp :: (EvalEnv m) => Selector -> TreeCursor -> m TreeCursor
  levelUp = propUpTCSel

  getSubTC :: (EvalEnv m) => Selector -> TreeCursor -> m TreeCursor
  getSubTC sel cursor = goDownTCSelErr sel cursor

{- | Traverse the leaves of the tree cursor in the following order
1. Traverse the current node.
2. Traverse the sub-tree with the selector.
-}
traverseTC :: (EvalEnv m) => (TreeCursor -> EvalMonad TreeCursor) -> TreeCursor -> m TreeCursor
traverseTC f tc = case treeNode n of
  TNScope _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNDisj _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNFunc _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNList _ -> f tc >>= traverseSubNodes (traverseTC f)
  TNAtom _ -> f tc
  TNBounds _ -> f tc
  TNConstraint _ -> f tc
  TNRefCycleVar -> f tc
  TNLink _ -> f tc
  TNBottom _ -> f tc
  TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
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
  TNFunc fn -> do
    dump $ printf "evalTC: path: %s, evaluate function, tip:%s" (show $ pathFromTC tc) (show $ fst tc)
    trfnFunc fn (trfnArgs fn) tc
  TNConstraint c ->
    let
      origAtom = mkNewTree (TNAtom $ trCnOrigAtom c)
      op = mkNewTree (TNFunc $ mkBinaryOp AST.Unify (trCnUnify c) origAtom (trCnCnstr c))
      unifyTC = (op, snd tc)
     in
      do
        dump $ printf "evalTC: constraint unify tc:\n%s" (showTreeCursor unifyTC)
        x <- evalTC unifyTC
        if (fst x) == origAtom
          then return (origAtom, snd tc)
          else throwError $ printf "evalTC: constraint not satisfied, %s != %s" (show (fst x)) (show origAtom)
  TNLink l -> do
    dump $
      printf "evalTC: path: %s, evaluate link %s" (show $ pathFromTC tc) (show $ trlTarget l)
    res <- followLink l tc
    case res of
      Nothing -> return tc
      Just tarTC -> do
        u <- evalTC tarTC
        return (fst u, snd tc)
  TNStub -> throwError $ printf "%s: TNStub should have been resolved" header
  TNList _ -> traverseSubNodes evalTC tc
  TNRefCycleVar -> return tc
  TNAtom _ -> return tc
  TNBounds _ -> return tc
  TNBottom _ -> return tc
  TNScope _ -> traverseSubNodes evalTC tc
  TNDisj _ -> traverseSubNodes evalTC tc
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
                return $ Just (mkNewTree TNRefCycleVar, snd tc)
            | isPrefix tarAbsPath selfAbsPath ->
                throwError $
                  printf
                    "structural cycle detected. %s is a prefix of %s"
                    (show tarAbsPath)
                    (show selfAbsPath)
            | otherwise ->
                let tarNode = fst tarTC
                    substTC = (tarNode, snd tc)
                 in case treeNode tarNode of
                      TNLink newLink -> do
                        dump $ printf "%s: substitutes to another link. go to %s" header (show $ trlTarget newLink)
                        followLink newLink substTC
                      TNConstraint c -> do
                        dump $ printf "%s: substitutes to the atom value of the constraint" header
                        return $ Just (mkNewTree (TNAtom $ trCnAtom c), snd tc)
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

{- | Search the tree cursor up to the root and return the tree cursor that points to the variable.
The cursor will also be propagated to the parent block.
-}
searchTCVar :: (EvalEnv m) => Selector -> TreeCursor -> m (Maybe TreeCursor)
searchTCVar sel@(ScopeSelector ssel@(StringSelector _)) tc = case treeNode (fst tc) of
  TNScope scope -> case Map.lookup ssel (trsSubs scope) of
    -- TODO: extendTC
    Just node -> return $ Just (node, (sel, fst tc) : snd tc)
    Nothing -> goUp tc
  _ -> goUp tc
 where
  goUp :: (EvalEnv m) => TreeCursor -> m (Maybe TreeCursor)
  goUp (_, []) = return Nothing
  goUp utc = propUpTC utc >>= searchTCVar sel
searchTCVar _ _ = return Nothing

-- | Search the tree cursor up to the root and return the tree cursor that points to the path.
searchTCPath :: (EvalEnv m) => Path -> TreeCursor -> m (Maybe TreeCursor)
searchTCPath p tc = runEnvMaybe $ do
  fstSel <- newEvalEnvMaybe $ headSel p
  base <- EnvMaybe $ searchTCVar fstSel tc
  tailP <- newEvalEnvMaybe $ tailPath p
  -- TODO: what if the base contains unevaluated nodes?
  newEvalEnvMaybe $ goDownTCPath tailP (trace (printf "base is %s, tail is %s" (show base) (show tailP)) base)

data ExtendTCLabel = ExtendTCLabel
  { exlSelector :: Selector
  , exlAttr :: LabelAttr
  }
  deriving (Show)

{- | Update the tree node to the tree cursor with the given selector and returns the new cursor that focuses on the
updated value.
-}
extendTC :: Selector -> Tree -> TreeCursor -> TreeCursor
extendTC sel sub (tip, cs) = (sub, (sel, tip) : cs)

replaceTCTip :: Tree -> TreeCursor -> TreeCursor
replaceTCTip t (_, cs) = (t, cs)

indexBySel :: (EvalEnv m) => Selector -> AST.UnaryExpr -> Tree -> m Tree
indexBySel sel ue t = case treeNode t of
  -- The tree is an evaluated, final scope, which could be formed by an in-place expression, like ({}).a.
  TNScope scope -> case sel of
    ScopeSelector s -> case Map.lookup s (trsSubs scope) of
      Just sub -> return sub
      Nothing ->
        return $
          mkNewTree
            ( TNFunc $
                mkTNFunc "indexBySel" Function constFunc (\_ -> AST.ExprUnaryExpr ue) [t]
            )
    s -> throwError $ printf "invalid selector: %s" (show s)
  TNList list -> case sel of
    IndexSelector i ->
      return $
        if i < length (trLstSubs list)
          then trLstSubs list !! i
          else mkBottom $ "index out of bound: " ++ show i
    _ -> throwError "invalid list selector"
  TNLink link ->
    return $
      mkNewTree
        ( TNLink $
            link
              { trlTarget = appendSel sel (trlTarget link)
              , trlExpr = ue
              }
        )
  TNDisj dj ->
    if isJust (trdDefault dj)
      then indexBySel sel ue (fromJust (trdDefault dj))
      else throwError insertErr
  TNFunc _ ->
    return $
      mkNewTree
        ( TNFunc $
            mkTNFunc
              "indexBySel"
              Function
              ( \ts tc -> do
                  utc <- evalTC (mkSubTC unaryOpSelector (ts !! 0) tc)
                  r <- indexBySel sel ue (fst utc)
                  evalTC $ replaceTCTip r tc
              )
              (\_ -> AST.ExprUnaryExpr ue)
              [t]
        )
  _ -> throwError insertErr
 where
  insertErr = printf "index: cannot index %s with sel: %s" (show t) (show sel)

  constFunc :: (EvalEnv m) => [Tree] -> TreeCursor -> m TreeCursor
  constFunc _ = return

indexByTree :: (EvalEnv m) => Tree -> AST.UnaryExpr -> Tree -> m Tree
indexByTree sel ue tree =
  case treeNode sel of
    TNAtom ta -> do
      idxsel <- selFromAtom ta
      indexBySel idxsel ue tree
    TNDisj dj -> case trdDefault dj of
      Just df -> do
        dump $ printf "indexByTree: default disjunct: %s" (show df)
        indexByTree df ue tree
      Nothing -> return invalidSelector
    TNConstraint c -> do
      idxsel <- selFromAtom (trCnOrigAtom c)
      indexBySel idxsel ue tree
    TNLink link ->
      return $
        mkNewTree
          ( TNFunc $
              TreeFunc
                { trfnName = "indexByTree"
                , trfnType = Function
                , trfnArgs = [sel]
                , trfnExprGen = \_ -> AST.ExprUnaryExpr (trlExpr link)
                , trfnFunc = \ts tc -> do
                    idx <- evalTC (mkSubTC (FuncArgSelector 0) (ts !! 0) tc)
                    dump $ printf "indexByTree TNLink: index resolved to %s" (show $ fst idx)
                    t <- indexByTree (fst idx) ue tree
                    dump $ printf "indexByTree TNLink: index result created %s" (show $ t)
                    u <- evalTC $ replaceTCTip t tc
                    dump $ printf "indexByTree TNLink: index result resolved to %s" (show $ fst u)
                    return u
                }
          )
    TNFunc _ ->
      return $
        mkNewTree
          ( TNFunc $
              mkTNFunc
                "indexByTree"
                Function
                ( \ts tc -> do
                    selTC <- evalTC (mkSubTC (FuncArgSelector 0) (ts !! 0) tc)
                    dump $ printf "indexByTree: path: %s, sel: %s, tree: %s" (show $ pathFromTC tc) (show $ fst selTC) (show $ ts !! 1)
                    t <- indexByTree (fst selTC) ue (ts !! 1)
                    dump $ printf "indexByTree TNFunc: resolved to %s" (show t)
                    evalTC $ replaceTCTip t tc
                )
                (\_ -> AST.ExprUnaryExpr ue)
                [sel, tree]
          )
    _ -> return invalidSelector
 where
  selFromAtom :: (EvalEnv m) => TNAtom -> m Selector
  selFromAtom a = case trAmAtom a of
    (String s) -> return $ (ScopeSelector $ StringSelector s)
    (Int i) -> return $ IndexSelector $ fromIntegral i
    _ -> throwError "extendTCIndex: invalid selector"

  invalidSelector :: Tree
  invalidSelector = mkNewTree (TNBottom $ TreeBottom $ printf "invalid selector: %s" (show sel))
