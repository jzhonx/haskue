{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Tree (
  Atom (..),
  AtomV (..),
  BdNumCmp (..),
  BdNumCmpOp (..),
  BdStrMatch (..),
  BdType (..),
  Bottom (..),
  Bound (..),
  Bounds (..),
  CommonEnv,
  Config (..),
  Constraint (..),
  Context (..),
  CtxVal (..),
  Disj (..),
  DynamicStructField (..),
  EvalEnv,
  EvalEnvState,
  EvalMonad,
  Func (..),
  FuncEnv,
  FuncType (..),
  LabelAttr (..),
  Link (..),
  List (..),
  Number (..),
  StaticStructField (..),
  Struct (..),
  StructFieldAdder (..),
  StructLabelType (..),
  Tree (..),
  TreeCursor,
  TreeNode (..),
  ValCursor (..),
  aToLiteral,
  bdRep,
  buildASTExpr,
  ctxPath,
  cvPath,
  debugRunEvalEnv,
  defaultLabelAttr,
  dump,
  emptyContext,
  emptyStruct,
  evalCV,
  getCTFromFuncEnv,
  getCVCursor,
  getScalarValue,
  goDownTCPath,
  goDownTCSel,
  goDownTCSelErr,
  goUpTC,
  indexBySel,
  indexByTree,
  insertUnifyStruct,
  isTreeBottom,
  isValueAtom,
  isValueConcrete,
  isValueNode,
  mapEvalCVCur,
  mergeAttrs,
  mkBinaryOp,
  mkBinaryOpDir,
  mkBottomTree,
  mkBoundsTree,
  mkCVFromCur,
  mkConstraint,
  mkListTree,
  mkNewTree,
  mkReference,
  mkStructTree,
  mkSubTC,
  mkAtomTree,
  mkDisjTree,
  mkUnaryOp,
  newEvalEnvMaybe,
  propUpTCSel,
  putCTInFuncEnv,
  runEnvMaybe,
  searchTCVar,
  setOrigNodesCV,
  setTCFocus,
  substLink,
  substTN,
  tcPath,
  updateConstraintAtom,
  updateConstraintCnstr,
)
where

import qualified AST
import Control.Monad (foldM)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (
  MonadLogger,
  logDebugN,
  runStderrLoggingT,
 )
import Control.Monad.Reader (MonadReader, ask, runReaderT)
import Control.Monad.State.Strict (
  MonadState,
  StateT (StateT),
  evalStateT,
  get,
  gets,
  put,
  runStateT,
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
import Data.List (findIndex, intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust, isNothing)
import Data.Text (pack)
import Debug.Trace
import Path
import Text.Printf (printf)

dump :: (MonadLogger m) => String -> m ()
dump = logDebugN . pack

type CommonEnv m = (MonadError String m, MonadLogger m, MonadReader Config m)

type CommonEnvMonad a = forall m. (CommonEnv m) => m a

type EvalEnvState s m = (CommonEnv m, MonadState s m)

type EvalEnv m = EvalEnvState Context m

type EvalMonad a = forall m. (EvalEnv m) => m a

type FuncEnv m = EvalEnvState (CtxVal Func) m

type FuncMonad a = forall m. (FuncEnv m) => m a

debugRunEvalEnv :: (MonadIO m, MonadError String m) => EvalMonad a -> m a
debugRunEvalEnv a = runStderrLoggingT (runReaderT (evalStateT a emptyContext) Config{})

data Context = Context
  { ctxCrumbs :: [TreeCrumb]
  , ctxNotifiers :: Map.Map Path [Path]
  }

ctxPath :: Context -> Path
ctxPath = pathFromCrumbs . ctxCrumbs

emptyContext :: Context
emptyContext = Context{ctxCrumbs = [], ctxNotifiers = Map.empty}

data CtxVal a = CtxVal
  { cvVal :: a
  , cvCtx :: Context
  }

instance Functor CtxVal where
  fmap f c = c{cvVal = f (cvVal c)}

type CtxTree = CtxVal Tree

mkCVFromCtx :: Context -> a -> CtxVal a
mkCVFromCtx ctx v = CtxVal{cvVal = v, cvCtx = ctx}

mkCVFromCur :: ValCursor a -> CtxVal a
mkCVFromCur cur =
  CtxVal
    { cvVal = vcFocus cur
    , cvCtx = Context{ctxCrumbs = vcCrumbs cur, ctxNotifiers = Map.empty}
    }

mapEvalCV :: (CommonEnv m) => (a -> m b) -> CtxVal a -> m (CtxVal b)
mapEvalCV f cv = do
  b <- f (cvVal cv)
  return $ b <$ cv

mapEvalCVCur :: (CommonEnv m) => (ValCursor a -> m (ValCursor b)) -> CtxVal a -> m (CtxVal b)
mapEvalCVCur f cv = do
  cur <- f (getCVCursor cv)
  return $ setCVCur cur cv

cvPath :: CtxVal a -> Path
cvPath = ctxPath . cvCtx

getCVCursor :: CtxVal a -> ValCursor a
getCVCursor cv = ValCursor (cvVal cv) (ctxCrumbs . cvCtx $ cv)

setCVCur :: ValCursor a -> CtxVal b -> CtxVal a
setCVCur cur cv =
  cv
    { cvVal = vcFocus cur
    , cvCtx = (cvCtx cv){ctxCrumbs = vcCrumbs cur}
    }

copyCVNotifiers :: CtxVal a -> CtxVal b -> CtxVal a
copyCVNotifiers cv1 cv2 = cv1{cvCtx = (cvCtx cv1){ctxNotifiers = ctxNotifiers $ cvCtx cv2}}

addCVNotifier :: (Path, Path) -> CtxVal a -> CtxVal a
addCVNotifier (src, dep) cv = cv{cvCtx = ctx{ctxNotifiers = new}}
 where
  ctx = cvCtx cv
  old = ctxNotifiers . cvCtx $ cv
  new = case Map.lookup src old of
    Nothing -> Map.insert src [dep] old
    Just ps -> Map.insert src (dep : ps) old

emptyCtxTree :: CtxTree
emptyCtxTree =
  CtxVal
    { cvVal = mkNewTree TNTop
    , cvCtx = emptyContext
    }

data Config = Config
  { cfUnify :: forall m. (FuncEnv m) => Tree -> Tree -> m Tree
  , cfCreateCnstr :: Bool
  }

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

newCommonEnvMaybe :: (CommonEnv m) => Maybe a -> EnvMaybe m a
newCommonEnvMaybe = EnvMaybe . return

data Atom
  = String String
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
  show Null = "null"

instance Eq Atom where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Int i1) (Float i2) = fromIntegral i1 == i2
  (==) (Float i1) (Int i2) = i1 == fromIntegral i2
  (==) (Float f1) (Float f2) = f1 == f2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) Null Null = True
  (==) _ _ = False

instance BuildASTExpr Atom where
  buildASTExpr a = return $ (AST.litCons . aToLiteral) a

aToLiteral :: Atom -> AST.Literal
aToLiteral a = case a of
  String s -> AST.StringLit $ AST.SimpleStringLit (show AST.DoubleQuote ++ s ++ show AST.DoubleQuote)
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
  buildASTExpr :: forall m. (CommonEnv m) => a -> m AST.Expression

class TreeRepBuilder a where
  repTree :: Int -> a -> Builder

data Tree = Tree
  { treeNode :: TreeNode
  , treeOrig :: Maybe Tree
  }

setTN :: TreeNode -> Tree -> Tree
setTN n t = t{treeNode = n}

-- modifyTreeNode :: (TreeNode -> TreeNode) -> Tree -> Tree
-- modifyTreeNode f t = t{treeNode = f (treeNode t)}

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

instance TreeRepBuilder Tree where
  repTree = tnStrBldr

tnStrBldr :: Int -> Tree -> Builder
tnStrBldr i t = case treeNode t of
  TNAtom leaf -> content t i (string7 (show $ amvAtom leaf)) emptyTreeFields
  TNLink _ -> content t i mempty emptyTreeFields
  TNStruct s ->
    let ordLabels =
          string7 "ord:"
            <> char7 '['
            <> string7 (intercalate ", " (map show $ stcOrdLabels s))
            <> char7 ']'
        attr :: LabelAttr -> Builder
        attr a = case lbAttrType a of
          SLRegular -> mempty
          SLRequired -> string7 "!"
          SLOptional -> string7 "?"
        isVar :: LabelAttr -> Builder
        isVar a =
          if lbAttrIsVar a
            then string7 ",v"
            else mempty
        slabel :: StructSelector -> Builder
        slabel k =
          let sf = stcSubs s Map.! k
           in string7 (show k)
                <> attr (ssfAttr sf)
                <> isVar (ssfAttr sf)
        dlabel :: Int -> Builder
        dlabel j =
          let sf = stcDynSubs s !! j
           in string7 (show j)
                <> attr (dsfAttr sf)
                <> isVar (dsfAttr sf)
                <> string7 ",e"
        fields =
          map (\k -> (slabel k, ssfField $ stcSubs s Map.! k)) (structStaticLabels s)
            ++ map
              (\j -> (dlabel j, dsfField $ stcDynSubs s !! j))
              (structDynIndexes s)
     in content t i ordLabels fields
  TNList vs ->
    let fields = map (\(j, v) -> (integerDec j, v)) (zip [0 ..] (lstSubs vs))
     in content t i mempty fields
  TNDisj d ->
    let dfField = maybe [] (\v -> [(string7 (show $ DisjDefaultSelector), v)]) (dsjDefault d)
        djFields = map (\(j, v) -> (string7 (show $ DisjDisjunctSelector j), v)) (zip [0 ..] (dsjDisjuncts d))
     in content t i mempty (dfField ++ djFields)
  TNConstraint c ->
    content
      t
      i
      mempty
      [ (string7 "Atom", mkNewTree (TNAtom $ cnsAtom c))
      , (string7 "Cond", cnsCnstr c)
      ]
  TNBounds b -> content t i mempty (map (\(j, v) -> (integerDec j, v)) (zip [0 ..] (bdsList b)))
  TNRefCycleVar -> content t i mempty emptyTreeFields
  TNFunc f ->
    let args = map (\(j, v) -> (integerDec j, v)) (zip [0 ..] (fncArgs f))
     in content
          t
          i
          ( string7 (fncName f)
              <> char7 ' '
              <> string7 (show $ fncHasRef f)
              <> char7 ' '
              <> string7 (maybe "" show (fncRes f))
          )
          args
  TNBottom b -> content t i (string7 $ show b) emptyTreeFields
  TNTop -> content t i mempty emptyTreeFields
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

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNAtom _ -> "v"
  TNBounds _ -> "b"
  TNStruct{} -> "{}"
  TNList{} -> "[]"
  TNLink l -> printf "-> %s" (show $ lnkTarget l)
  TNDisj{} -> "dj"
  TNConstraint{} -> "Cnstr"
  TNRefCycleVar -> "RefCycleVar"
  TNFunc{} -> "fn"
  TNBottom _ -> "_|_"
  TNTop -> "_"

instance Show Tree where
  show tree = showTreeIdent tree 0

instance BuildASTExpr Tree where
  buildASTExpr t = case treeNode t of
    TNStruct s -> buildASTExpr s
    TNList l -> buildASTExpr l
    TNDisj d -> buildASTExpr d
    TNLink l -> buildASTExpr l
    TNAtom s -> buildASTExpr s
    TNBounds b -> buildASTExpr b
    TNConstraint _ -> buildASTExpr (fromJust $ treeOrig t)
    TNRefCycleVar -> return $ AST.litCons AST.TopLit
    TNFunc fn ->
      if isJust (treeOrig t)
        then buildASTExpr (fromJust $ treeOrig t)
        else buildASTExpr fn
    TNBottom _ -> return $ AST.litCons AST.BottomLit
    TNTop -> return $ AST.litCons AST.TopLit

mkNewTree :: TreeNode -> Tree
mkNewTree n = Tree n Nothing

substTN :: TreeNode -> Tree -> Tree
substTN n t = t{treeNode = n}

copyOrigNode :: Tree -> Tree -> Tree
copyOrigNode new old = new{treeOrig = treeOrig old}

-- | Tree represents a tree structure that contains values.
data TreeNode
  = -- | TNStruct is a struct that contains a value and a map of selectors to Tree.
    TNStruct Struct
  | TNList List
  | TNDisj Disj
  | -- | Unless the target is a scalar, the TNLink should not be pruned.
    TNLink Link
  | -- | TNAtom contains an atom value.
    TNAtom AtomV
  | TNBounds Bounds
  | TNConstraint Constraint
  | TNRefCycleVar
  | TNFunc Func
  | TNTop
  | TNBottom Bottom

instance Eq TreeNode where
  (==) (TNStruct s1) (TNStruct s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNLink l1) (TNLink l2) = l1 == l2
  (==) (TNAtom l1) (TNAtom l2) = l1 == l2
  (==) (TNConstraint c1) (TNConstraint c2) = c1 == c2
  (==) TNRefCycleVar TNRefCycleVar = True
  (==) (TNDisj dj1) n2@(TNAtom _) =
    if isNothing (dsjDefault dj1)
      then False
      else treeNode (fromJust $ dsjDefault dj1) == n2
  (==) (TNAtom a1) (TNDisj dj2) = (==) (TNDisj dj2) (TNAtom a1)
  (==) (TNFunc f1) (TNFunc f2) = f1 == f2
  (==) (TNBounds b1) (TNBounds b2) = b1 == b2
  (==) (TNBottom _) (TNBottom _) = True
  (==) TNTop TNTop = True
  (==) _ _ = False

instance ValueNode TreeNode where
  isValueNode n = case n of
    TNAtom _ -> True
    TNBounds _ -> True
    TNStruct _ -> True
    TNList _ -> True
    TNDisj _ -> True
    TNConstraint _ -> True
    TNRefCycleVar -> False
    TNLink _ -> False
    TNFunc _ -> False
    TNBottom _ -> True
    TNTop -> True
  isValueAtom n = case n of
    TNAtom _ -> True
    _ -> False

  isValueConcrete n = case n of
    TNStruct struct -> isStructConcrete struct
    _ -> isValueAtom n
  getScalarValue n = case n of
    TNAtom s -> Just (amvAtom s)
    TNConstraint c -> Just (amvAtom $ cnsAtom c)
    _ -> Nothing

isTNRefCycleVar :: TreeNode -> Bool
isTNRefCycleVar TNRefCycleVar = True
isTNRefCycleVar _ = False

newtype List = List
  { lstSubs :: [Tree]
  }

instance Eq List where
  (==) l1 l2 = lstSubs l1 == lstSubs l2

instance BuildASTExpr List where
  buildASTExpr l =
    AST.litCons . AST.ListLit . AST.EmbeddingList <$> mapM buildASTExpr (lstSubs l)

mkListTree :: [Tree] -> Tree
mkListTree ts = mkNewTree (TNList $ List{lstSubs = ts})

data LabelAttr = LabelAttr
  { lbAttrType :: StructLabelType
  , lbAttrIsVar :: Bool
  }
  deriving (Show, Eq)

defaultLabelAttr :: LabelAttr
defaultLabelAttr = LabelAttr SLRegular True

mergeAttrs :: LabelAttr -> LabelAttr -> LabelAttr
mergeAttrs a1 a2 =
  LabelAttr
    { lbAttrType = min (lbAttrType a1) (lbAttrType a2)
    , lbAttrIsVar = lbAttrIsVar a1 || lbAttrIsVar a2
    }

data StructLabelType = SLRegular | SLRequired | SLOptional
  deriving (Eq, Ord, Enum, Show)

data StaticStructField = StaticStructField
  { ssfField :: Tree
  , ssfAttr :: LabelAttr
  }
  deriving (Show)

instance Eq StaticStructField where
  (==) f1 f2 = ssfField f1 == ssfField f2 && ssfAttr f1 == ssfAttr f2

data DynamicStructField = DynamicStructField
  { dsfField :: Tree
  , dsfAttr :: LabelAttr
  , dsfSelExpr :: AST.Expression
  , dsfSelTree :: Tree
  }
  deriving (Show)

instance Eq DynamicStructField where
  (==) f1 f2 = dsfField f1 == dsfField f2 && dsfAttr f1 == dsfAttr f2 && dsfSelExpr f1 == dsfSelExpr f2

data Struct = Struct
  { stcOrdLabels :: [StructSelector] -- Should only contain string labels.
  , stcSubs :: Map.Map StructSelector StaticStructField
  , stcDynSubs :: [DynamicStructField]
  }

instance Eq Struct where
  (==) s1 s2 =
    stcOrdLabels s1 == stcOrdLabels s2
      && stcSubs s1 == stcSubs s2
      && stcDynSubs s1 == stcDynSubs s2

instance BuildASTExpr Struct where
  buildASTExpr s =
    let
      processStaticField :: (CommonEnv m) => (StructSelector, StaticStructField) -> m AST.Declaration
      processStaticField (label, sf) = case label of
        StringSelector sel -> do
          e <- buildASTExpr (ssfField sf)
          return $
            AST.FieldDecl $
              AST.Field
                [ labelCons (ssfAttr sf) $
                    if lbAttrIsVar (ssfAttr sf)
                      then AST.LabelID sel
                      else AST.LabelString sel
                ]
                e
        DynamicSelector _ -> throwError "DynamicSelector is not allowed in static fields."

      processDynField :: (CommonEnv m) => DynamicStructField -> m AST.Declaration
      processDynField sf = do
        e <- buildASTExpr (dsfField sf)
        return $
          AST.FieldDecl $
            AST.Field
              [ labelCons (dsfAttr sf) $ AST.LabelNameExpr (dsfSelExpr sf)
              ]
              e

      labelCons :: LabelAttr -> AST.LabelName -> AST.Label
      labelCons attr =
        AST.Label . case lbAttrType attr of
          SLRegular -> AST.RegularLabel
          SLRequired -> AST.RequiredLabel
          SLOptional -> AST.OptionalLabel
     in
      do
        stcs <- sequence [processStaticField (l, stcSubs s Map.! l) | l <- structStaticLabels s]
        dyns <- sequence [processDynField sf | sf <- stcDynSubs s]
        return $
          AST.litCons $
            AST.StructLit (stcs ++ dyns)

emptyStruct :: Struct
emptyStruct = Struct{stcOrdLabels = [], stcSubs = Map.empty, stcDynSubs = []}

data StructFieldAdder = Static StructSelector StaticStructField | Dynamic DynamicStructField
  deriving (Show)

mkStructTree :: [StructFieldAdder] -> Tree
mkStructTree as =
  mkNewTree . TNStruct $
    Struct
      { stcOrdLabels = ordLabels
      , stcSubs = Map.fromList statics
      , stcDynSubs = dynamics
      }
 where
  ordLabels = [l | Static l _ <- as]
  statics = [(s, sf) | Static s sf <- as]
  dynamics = [df | Dynamic df <- as]

-- Insert a new field into the struct. If the field is already in the struct, then unify the field with the new field.
insertUnifyStruct :: StructFieldAdder -> (Tree -> Tree -> FuncMonad Tree) -> Struct -> Struct
insertUnifyStruct (Static sel sf) unify struct = case subs Map.!? sel of
  Just extSF ->
    let
      unifySFOp =
        StaticStructField
          { ssfField = mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify (ssfField extSF) (ssfField sf))
          , ssfAttr = mergeAttrs (ssfAttr extSF) (ssfAttr sf)
          }
     in
      struct{stcSubs = Map.insert sel unifySFOp subs}
  Nothing ->
    struct
      { stcOrdLabels = stcOrdLabels struct ++ [sel]
      , stcSubs = Map.insert sel sf subs
      }
 where
  subs = stcSubs struct
insertUnifyStruct (Dynamic sf) _ struct = struct{stcDynSubs = stcDynSubs struct ++ [sf]}

structStaticLabels :: Struct -> [StructSelector]
structStaticLabels = filter (\x -> viewStructSelector x == 0) . stcOrdLabels

structDynIndexes :: Struct -> [Int]
structDynIndexes s = [0 .. length (stcDynSubs s) - 1]

isStructConcrete :: Struct -> Bool
isStructConcrete s =
  foldl
    ( \acc
       (StaticStructField{ssfField = Tree{treeNode = x}}) -> acc && isValueConcrete x
    )
    True
    (Map.elems (stcSubs s))

evalStruct :: (CommonEnv m) => CtxVal (Struct, Tree) -> m CtxTree
evalStruct cv =
  foldM evalSub ct (Map.keys (stcSubs struct) ++ map DynamicSelector [0 .. length (stcDynSubs struct) - 1])
 where
  ct = snd <$> cv
  struct = fst (cvVal cv)
  evalSub :: (CommonEnv m) => CtxTree -> StructSelector -> m CtxTree
  evalSub acc sel = case (treeNode . cvVal) acc of
    TNBottom _ -> return acc
    TNStruct x -> evalCVStructField sel ((x, cvVal acc) <$ acc)
    _ -> return $ mkBottomTree "not a struct" <$ acc

evalCVStructField :: (CommonEnv m) => StructSelector -> CtxVal (Struct, Tree) -> m CtxTree
evalCVStructField sel cv = case sel of
  StringSelector _ ->
    let sf = stcSubs struct Map.! sel
     in do
          return $ snd <$> cv
          >>= mapEvalCVCur (return . mkSubTC subSel (ssfField sf))
          >>= evalCV
          >>= mapEvalCVCur (propUpTCSel subSel)
  DynamicSelector i ->
    let dsf = stcDynSubs struct !! i
     in do
          -- evaluate the dynamic label.
          labelCT <-
            do
              return $ snd <$> cv
              >>= mapEvalCVCur (return . mkSubTC subSel (dsfSelTree dsf))
              >>= evalCV
          let label = cvVal labelCT
          dump $
            printf
              "evalCVStructField: path: %s, dynamic label is evaluated to %s"
              (show $ cvPath cv)
              (show label)
          case treeNode label of
            TNAtom (AtomV (String s)) -> do
              Config{cfUnify = unify} <- ask
              let
                mergedSF = dynToStaticField dsf (stcSubs struct Map.!? StringSelector s) unify
                sSel = StructSelector $ StringSelector s
              mergedCT <-
                do
                  mapEvalCVCur (propUpTCSel subSel) labelCT
                  >>= mapEvalCVCur (return . mkSubTC sSel (ssfField mergedSF))
                  >>= evalCV
                  >>= mapEvalCVCur (propUpTCSel sSel)
              return $ setTN (TNStruct $ updateDynStruct i s mergedSF struct) <$> mergedCT
            _ -> return $ mkBottomTree "selector can only be a string" <$ cv
 where
  focus = cvVal cv
  struct = fst focus
  subSel = StructSelector sel

  dynToStaticField ::
    DynamicStructField -> Maybe StaticStructField -> (Tree -> Tree -> FuncMonad Tree) -> StaticStructField
  dynToStaticField dsf sfM unify = case sfM of
    Just sf ->
      StaticStructField
        { ssfField = mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify (ssfField sf) (dsfField dsf))
        , ssfAttr = mergeAttrs (ssfAttr sf) (dsfAttr dsf)
        }
    Nothing ->
      StaticStructField
        { ssfField = dsfField dsf
        , ssfAttr = dsfAttr dsf
        }

  updateDynStruct :: Int -> String -> StaticStructField -> Struct -> Struct
  updateDynStruct i s sf x =
    x
      { stcSubs = Map.insert (StringSelector s) sf (stcSubs x)
      , stcDynSubs = take i (stcDynSubs x) ++ drop (i + 1) (stcDynSubs x)
      }

data Link = Link
  { lnkTarget :: Path
  , lnkExpr :: AST.UnaryExpr
  }

instance Eq Link where
  (==) l1 l2 = lnkTarget l1 == lnkTarget l2

instance BuildASTExpr Link where
  buildASTExpr l = return $ AST.ExprUnaryExpr $ lnkExpr l

mkReference :: Tree -> AST.UnaryExpr -> Func
mkReference t ue =
  Func
    { fncName = "Ref"
    , fncType = RegularFunc
    , fncHasRef = True
    , fncArgs = []
    , fncExprGen = \_ -> return $ AST.ExprUnaryExpr ue
    , fncFunc = \_ -> return t
    , fncRes = Just t
    }

evalLink :: (CommonEnv m) => CtxVal (Link, Tree) -> m CtxTree
evalLink cv = do
  dump $ printf "evalCV: path: %s, evaluate link %s" (show $ cvPath cv) (show $ lnkTarget link)
  let ct = snd <$> cv
  res <- followLink link (getCVCursor ct)
  case res of
    Nothing -> return ct
    Just (tp, tar) -> do
      if isValueAtom (treeNode tar) || isTNRefCycleVar (treeNode tar)
        -- If the target is an atom or a cycle head, there is no need to create the reference relation.
        then return $ tar <$ ct
        else do
          let
            ref = mkReference tar (lnkExpr link)
            -- add notifier. If the referenced value changes, then the reference should be updated.
            uct = addCVNotifier (tp, cvPath cv) ct
          return $ mkNewTree (TNFunc ref) <$ uct
 where
  link = fst (cvVal cv)

{- | Substitute the link node with the referenced node.
link should be the node that is currently being evaluated.
1. Find the target TC in the original tree.
2. Define the struct, which is the path of the target node.
3. Evaluate links that are outside the struct.
-}
substLink :: (CommonEnv m) => CtxVal (Link, Tree) -> m CtxTree
substLink cv = do
  dump $ printf "substLink: link (%s), path: %s starts" (show $ lnkTarget link) (show $ cvPath cv)
  dump $ printf "substLink, tc:\n%s" (show tc)
  res <- runEnvMaybe $ do
    (tp, tar) <- EnvMaybe (followLink link tc)
    lift $
      dump $
        printf
          "substLink: link (%s) target is found in the eval tree, tree: %s"
          (show $ lnkTarget link)
          (show tar)
    case treeNode tar of
      -- The link leads to a cycle head, which does not have the original node.
      TNRefCycleVar -> return (tp, tar)
      _ -> do
        -- we need to get the original (un-evalCVed) version of the target node.
        origTar <- newCommonEnvMaybe $ treeOrig tar
        return (tp, origTar)
  case res of
    Nothing -> do
      dump $ printf "substLink: original target of the link (%s) is not found" (show $ lnkTarget link)
      return $ snd <$> cv
    Just (tp, tar) -> do
      dump $
        printf
          "substLink: link (%s) target is found, path: %s, tree:\n%s"
          (show $ lnkTarget link)
          (show tp)
          (show tar)
      substCv <- evalOutStructLink tp (tar <$ cv)
      dump $
        printf
          "substLink: link (%s) target is evaluated to:\n%s"
          (show $ lnkTarget link)
          (show $ cvVal substCv)
      return substCv
 where
  tc = getCVCursor $ snd <$> cv
  link = fst (cvVal cv)

-- substitute out-struct links with evaluated nodes.
evalOutStructLink :: (CommonEnv m) => Path -> CtxTree -> m CtxTree
evalOutStructLink p =
  traverseCV $ \cv -> case treeNode (cvVal cv) of
    -- Use the first var to determine if the link is in the struct. Then search the whole path.
    -- This handles the x.a case correctly.
    TNLink l -> do
      varPathMaybe <- runEnvMaybe $ do
        fstSel <- newCommonEnvMaybe $ headSel p
        -- If the variable is outside of the struct, then no matter what the following selectors are, the link is
        -- outside of the struct.
        varTC <- EnvMaybe $ searchTCVar fstSel (getCVCursor cv)
        _ <- EnvMaybe $ searchTCPath (lnkTarget l) (getCVCursor cv)
        return $ tcPath varTC

      case varPathMaybe of
        Nothing -> return cv
        Just varPath ->
          -- If the first selector of the link references the struct or nodes outside the struct, then evaluate the
          -- link.
          if p == varPath || not (isPrefix p varPath)
            then evalCV cv
            else return cv
    _ -> return cv

newtype AtomV = AtomV
  { amvAtom :: Atom
  }

instance Show AtomV where
  show (AtomV v) = show v

instance Eq AtomV where
  (==) (AtomV v1) (AtomV v2) = v1 == v2

instance BuildASTExpr AtomV where
  buildASTExpr (AtomV v) = buildASTExpr v

mkAtomTree :: Atom -> Tree
mkAtomTree v = mkNewTree (TNAtom $ AtomV{amvAtom = v})

data Disj = Disj
  { dsjDefault :: Maybe Tree
  , dsjDisjuncts :: [Tree]
  }

instance Eq Disj where
  (==) (Disj ds1 js1) (Disj ds2 js2) = ds1 == ds2 && js1 == js2

instance BuildASTExpr Disj where
  buildASTExpr dj =
    if isJust (dsjDefault dj)
      then buildASTExpr $ fromJust (dsjDefault dj)
      else do
        xs <- mapM buildASTExpr (dsjDisjuncts dj)
        return $
          foldr1
            ( \x y -> AST.ExprBinaryOp AST.Disjunction x y
            )
            xs

mkDisjTree :: Maybe Tree -> [Tree] -> Tree
mkDisjTree m js = mkNewTree (TNDisj $ Disj{dsjDefault = m, dsjDisjuncts = js})

-- Constraint does not need to implement the BuildASTExpr.
data Constraint = Constraint
  { cnsAtom :: AtomV
  , cnsOrigAtom :: AtomV
  -- ^ trCnOrigNode is the original atom value that was unified with other expression. Notice that the atom value can be
  -- changed by binary operations.
  , cnsCnstr :: Tree
  , cnsUnify :: forall m. (FuncEnv m) => Tree -> Tree -> m Tree
  }

instance Eq Constraint where
  (==) (Constraint a1 o1 c1 _) (Constraint a2 o2 c2 _) =
    a1 == a2 && c1 == c2 && o1 == o2

mkConstraint :: AtomV -> Tree -> (Tree -> Tree -> FuncMonad Tree) -> Constraint
mkConstraint atom cnstr unify =
  Constraint
    { cnsAtom = atom
    , cnsOrigAtom = atom
    , cnsCnstr = cnstr
    , cnsUnify = unify
    }

updateConstraintCnstr ::
  (BinOpDirect, Tree) ->
  (Tree -> Tree -> FuncMonad Tree) ->
  Constraint ->
  Constraint
updateConstraintCnstr (d, t) unify c =
  let newBinOp =
        if d == L
          then TNFunc $ mkBinaryOp AST.Unify unify t (cnsCnstr c)
          else TNFunc $ mkBinaryOp AST.Unify unify (cnsCnstr c) t
   in c{cnsCnstr = mkNewTree newBinOp}

updateConstraintAtom :: AtomV -> Constraint -> Constraint
updateConstraintAtom atom c = c{cnsAtom = atom}

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
  show b = AST.exprStr $ buildBoundASTExpr b

instance TreeRepBuilder Bound where
  repTree _ b = char7 '(' <> string7 (show b) <> char7 ')'

instance BuildASTExpr Bound where
  buildASTExpr b = return $ buildBoundASTExpr b

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

newtype Bounds = Bounds
  { bdsList :: [Bound]
  }
  deriving (Eq)

instance BuildASTExpr Bounds where
  buildASTExpr b = do
    xs <- mapM buildASTExpr (bdsList b)
    return $ foldr1 (AST.ExprBinaryOp AST.Unify) xs

mkBoundsTree :: [Bound] -> Tree
mkBoundsTree bs = mkNewTree (TNBounds $ Bounds{bdsList = bs})

data FuncType = RegularFunc | DisjFunc
  deriving (Eq, Enum)

data Func = Func
  { fncName :: String
  , fncType :: FuncType
  , fncHasRef :: Bool
  , -- Args stores the arguments that may or may not need to be evaluated.
    fncArgs :: [Tree]
  , fncExprGen :: forall m. (CommonEnv m) => [Tree] -> m AST.Expression
  , -- The call convention:
    -- The return value is the result of the function.
    fncFunc :: forall m. (FuncEnv m) => [Tree] -> m Tree
  , -- fncRes stores the temporary non-atom, non-function result of the function.
    fncRes :: Maybe Tree
  }

instance BuildASTExpr Func where
  buildASTExpr fn =
    if isJust (fncRes fn)
      then buildASTExpr (fromJust $ fncRes fn)
      else fncExprGen fn (fncArgs fn)

instance Eq Func where
  (==) f1 f2 =
    fncName f1 == fncName f2
      && fncType f1 == fncType f2
      && fncHasRef f1 == fncHasRef f2
      && fncArgs f1 == fncArgs f2
      && fncRes f1 == fncRes f2

getCTFromFuncEnv :: (FuncEnv m) => m CtxTree
getCTFromFuncEnv = gets (mkNewTree . TNFunc <$>)

putCTInFuncEnv :: (FuncEnv m) => CtxTree -> m ()
putCTInFuncEnv ct = case treeNode . cvVal $ ct of
  TNFunc fn -> put (fn <$ ct)
  _ -> throwError "putCTInFuncEnv: the tree node is not a function."

getFuncHasRef :: [Tree] -> Bool
getFuncHasRef =
  any
    ( \x -> case treeNode x of
        TNFunc fn -> fncHasRef fn
        _ -> False
    )

mkUnaryOp :: AST.UnaryOp -> (Tree -> FuncMonad Tree) -> Tree -> Func
mkUnaryOp op f n =
  Func
    { fncFunc = g
    , fncType = RegularFunc
    , fncHasRef = getFuncHasRef [n]
    , fncExprGen = gen
    , fncName = show op
    , fncArgs = [n]
    , fncRes = Nothing
    }
 where
  g :: [Tree] -> FuncMonad Tree
  g [x] = f x
  g _ = throwError "mkTNUnaryOp: invalid number of arguments"

  gen :: (CommonEnv m) => [Tree] -> m AST.Expression
  gen [x] = buildUnaryExpr x
  gen _ = throwError "can not generate unary expression because of invalid number of arguments"

  buildUnaryExpr :: (CommonEnv m) => Tree -> m AST.Expression
  buildUnaryExpr t = do
    te <- buildASTExpr t
    case te of
      (AST.ExprUnaryExpr ue) -> return $ AST.ExprUnaryExpr $ AST.UnaryExprUnaryOp op ue
      e ->
        return $
          AST.ExprUnaryExpr $
            AST.UnaryExprUnaryOp
              op
              (AST.UnaryExprPrimaryExpr . AST.PrimExprOperand $ AST.OpExpression e)

mkBinaryOp ::
  AST.BinaryOp -> (Tree -> Tree -> FuncMonad Tree) -> Tree -> Tree -> Func
mkBinaryOp op f l r =
  Func
    { fncFunc = g
    , fncType = case op of
        AST.Disjunction -> DisjFunc
        _ -> RegularFunc
    , fncHasRef = getFuncHasRef [l, r]
    , fncExprGen = gen
    , fncName = show op
    , fncArgs = [l, r]
    , fncRes = Nothing
    }
 where
  g :: [Tree] -> FuncMonad Tree
  g [x, y] = f x y
  g _ = throwError "mkTNUnaryOp: invalid number of arguments"

  gen :: (CommonEnv m) => [Tree] -> m AST.Expression
  gen [x, y] = do
    xe <- buildASTExpr x
    ye <- buildASTExpr y
    return $ AST.ExprBinaryOp op xe ye
  gen _ = throwError "can not generate binary expression because of invalid number of arguments"

mkBinaryOpDir ::
  AST.BinaryOp ->
  (Tree -> Tree -> FuncMonad Tree) ->
  (BinOpDirect, Tree) ->
  (BinOpDirect, Tree) ->
  Func
mkBinaryOpDir rep op (d1, t1) (_, t2) =
  case d1 of
    L -> mkBinaryOp rep op t1 t2
    R -> mkBinaryOp rep op t2 t1

evalFunc :: (CommonEnv m) => CtxVal (Func, Tree) -> m CtxTree
evalFunc cv = do
  let
  dump $
    printf
      "evalFunc: path: %s, evaluate function %s, tip:%s"
      (show $ cvPath ct)
      (show $ fncName fn)
      (show $ cvVal ct)
  (a, newCV) <- runStateT (fncFunc fn (fncArgs fn)) (fst <$> cv)
  res <-
    if isValueAtom (treeNode a) || not (fncHasRef fn)
      then do
        -- keep the original expression.
        let newNode = copyOrigNode a (snd $ cvVal cv)
        return $ newNode <$ newCV
      else do
        dump $
          printf
            "evalFunc: path: %s, function %s evaluated to :%s"
            (show $ cvPath ct)
            (show $ fncName fn)
            (show a)
        v <- case treeNode a of
          TNFunc f -> case fncRes f of
            Just x -> return x
            Nothing -> throwError $ printf "evalFunc: function %s does not have a result" (show a)
          _ -> return a
        let
          newFn = fn{fncRes = Just v}
          newNode = substTN (TNFunc newFn) (snd $ cvVal cv)
        return $ newNode <$ newCV
  dump $
    printf
      "evalFunc: path: %s, evaluate function %s, res:%s"
      (show $ cvPath res)
      (show $ fncName fn)
      (show $ cvVal res)
  return res
 where
  fn = fst $ cvVal cv
  ct = snd <$> cv

newtype Bottom = Bottom {btmMsg :: String}

instance Eq Bottom where
  (==) _ _ = True

instance BuildASTExpr Bottom where
  buildASTExpr _ = return $ AST.litCons AST.BottomLit

instance Show Bottom where
  show (Bottom m) = m

mkBottomTree :: String -> Tree
mkBottomTree msg = mkNewTree (TNBottom $ Bottom{btmMsg = msg})

isTreeBottom :: Tree -> Bool
isTreeBottom (Tree (TNBottom _) _) = True
isTreeBottom _ = False

-- -- --

-- step down the tree with the given selector.
-- This should only be used by TreeCursor.
goTreeSel :: Selector -> Tree -> Maybe Tree
goTreeSel sel t =
  case sel of
    RootSelector -> Just t
    StructSelector s -> case node of
      TNStruct struct -> case s of
        StringSelector _ -> ssfField <$> Map.lookup s (stcSubs struct)
        DynamicSelector i -> Just $ dsfField $ stcDynSubs struct !! i
      _ -> Nothing
    IndexSelector i -> case node of
      TNList vs -> lstSubs vs `index` i
      _ -> Nothing
    FuncArgSelector i -> case node of
      TNFunc fn -> fncArgs fn `index` i
      _ -> Nothing
    DisjDefaultSelector -> case node of
      TNDisj d -> dsjDefault d
      _ -> Nothing
    DisjDisjunctSelector i -> case node of
      TNDisj d -> dsjDisjuncts d `index` i
      _ -> Nothing
    ParentSelector -> Nothing
 where
  node = treeNode t

  index :: [a] -> Int -> Maybe a
  index xs i = if i < length xs then Just (xs !! i) else Nothing

-- | TreeCrumb is a pair of a name and an environment. The name is the name of the field in the parent environment.
type TreeCrumb = (Selector, Tree)

pathFromCrumbs :: [TreeCrumb] -> Path
pathFromCrumbs crumbs = Path . reverse $ go crumbs []
 where
  go :: [TreeCrumb] -> [Selector] -> [Selector]
  go [] acc = acc
  go ((n, _) : cs) acc = go cs (n : acc)

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
data ValCursor a = ValCursor
  { vcFocus :: a
  , vcCrumbs :: [TreeCrumb]
  }
  deriving (Eq)

instance (Show a) => Show (ValCursor a) where
  show = showCursor

instance Functor ValCursor where
  fmap f (ValCursor t cs) = ValCursor (f t) cs

mapEvalValCursor :: (CommonEnv m) => (a -> m b) -> ValCursor a -> m (ValCursor b)
mapEvalValCursor f cs = do
  b <- f (vcFocus cs)
  return $ b <$ cs

type TreeCursor = ValCursor Tree

viewTC :: TreeCursor -> TreeNode
viewTC tc = treeNode (vcFocus tc)

-- tcNodeSetter :: TreeCursor -> TreeNode -> TreeCursor
-- tcNodeSetter (TreeCursor t cs) n = TreeCursor (substTN n t) cs

showCursor :: (Show a) => ValCursor a -> String
showCursor tc = LBS.unpack $ toLazyByteString $ prettyBldr tc
 where
  prettyBldr :: (Show a) => ValCursor a -> Builder
  prettyBldr (ValCursor t cs) =
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

setTCFocus :: a -> ValCursor a -> ValCursor a
setTCFocus t (ValCursor _ cs) = ValCursor t cs

mkSubTC :: Selector -> a -> TreeCursor -> ValCursor a
mkSubTC sel a tc = ValCursor a ((sel, vcFocus tc) : vcCrumbs tc)

-- | Go up the tree cursor and return the new cursor.
goUpTC :: TreeCursor -> Maybe TreeCursor
goUpTC (ValCursor _ []) = Nothing
goUpTC (ValCursor _ ((_, v) : vs)) = Just $ ValCursor v vs

goDownTCPath :: Path -> TreeCursor -> Maybe TreeCursor
goDownTCPath (Path sels) = go (reverse sels)
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
goDownTCSel sel tc = case go sel tc of
  Just c -> Just c
  Nothing -> case treeNode (vcFocus tc) of
    TNDisj d ->
      if isJust (dsjDefault d)
        then goDownTCSel DisjDefaultSelector tc >>= go sel
        else Nothing
    _ -> Nothing
 where
  go :: Selector -> TreeCursor -> Maybe TreeCursor
  go s x = do
    nextTree <- goTreeSel s (vcFocus x)
    return $ mkSubTC s nextTree x

goDownTCSelErr :: (MonadError String m) => Selector -> TreeCursor -> m TreeCursor
goDownTCSelErr sel tc = case goDownTCSel sel tc of
  Just c -> return c
  Nothing -> throwError $ printf "cannot go down tree with selector %s, tree: %s" (show sel) (show $ vcFocus tc)

tcPath :: ValCursor a -> Path
tcPath c = pathFromCrumbs (vcCrumbs c)

{- | propUp propagates the changes made to the tip of the block to the parent block.
The structure of the tree is not changed.
-}
propUpTC :: (CommonEnv m) => TreeCursor -> m TreeCursor
propUpTC tc@(ValCursor _ []) = return tc
propUpTC tc@(ValCursor subT ((sel, parT) : cs)) = case sel of
  StructSelector s -> updateParStruct parT s subT
  IndexSelector i -> case parNode of
    TNList vs ->
      let subs = lstSubs vs
          l = TNList $ vs{lstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return (ValCursor (substTN l parT) cs)
    _ -> throwError insertErrMsg
  FuncArgSelector i -> case parNode of
    TNFunc fn ->
      let args = fncArgs fn
          l = TNFunc $ fn{fncArgs = take i args ++ [subT] ++ drop (i + 1) args}
       in return (ValCursor (substTN l parT) cs)
    _ -> throwError insertErrMsg
  DisjDefaultSelector -> case parNode of
    TNDisj d ->
      return
        (ValCursor (substTN (TNDisj $ d{dsjDefault = dsjDefault d}) parT) cs)
    _ -> throwError insertErrMsg
  DisjDisjunctSelector i -> case parNode of
    TNDisj d ->
      return
        ( ValCursor
            ( substTN (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)}) parT
            )
            cs
        )
    _ -> throwError insertErrMsg
  ParentSelector -> throwError "propUpTC: ParentSelector is not allowed"
  RootSelector -> throwError "propUpTC: RootSelector is not allowed"
 where
  parNode = treeNode parT
  updateParStruct :: (MonadError String m) => Tree -> StructSelector -> Tree -> m TreeCursor
  updateParStruct par label newSub = case treeNode par of
    TNStruct parStruct ->
      if
        | isTreeBottom newSub -> return (ValCursor newSub cs)
        | Map.member label (stcSubs parStruct) ->
            let
              sf = stcSubs parStruct Map.! label
              newSF = sf{ssfField = newSub}
              newStruct = parStruct{stcSubs = Map.insert label newSF (stcSubs parStruct)}
             in
              return (ValCursor (substTN (TNStruct newStruct) parT) cs)
        | otherwise -> case label of
            DynamicSelector i ->
              let
                sf = stcDynSubs parStruct !! i
                newSF = sf{dsfField = newSub}
                newStruct =
                  parStruct
                    { stcDynSubs =
                        take i (stcDynSubs parStruct) ++ [newSF] ++ drop (i + 1) (stcDynSubs parStruct)
                    }
               in
                return (ValCursor (substTN (TNStruct newStruct) parT) cs)
            _ -> throwError insertErrMsg
    _ -> throwError insertErrMsg

  insertErrMsg :: String
  insertErrMsg =
    printf
      "propUpTC: cannot insert child %s to parent %s, path: %s, selector: %s, child:\n%s\nparent:\n%s"
      (showTreeSymbol subT)
      (showTreeSymbol parT)
      (show $ tcPath tc)
      (show sel)
      (show subT)
      (show parT)

propUpTCSel :: (CommonEnv m) => Selector -> TreeCursor -> m TreeCursor
propUpTCSel _ tc@(ValCursor _ []) = return tc
propUpTCSel sel tc@(ValCursor _ ((s, _) : _)) =
  if s == sel
    then propUpTC tc
    else propUpTC tc >>= propUpTCSel sel

-- | Traverse all the sub nodes of the tree.
traverseSubNodes :: (CommonEnv m) => (CtxTree -> CommonEnvMonad CtxTree) -> CtxTree -> m CtxTree
traverseSubNodes f ct = case treeNode (cvVal ct) of
  TNStruct struct -> foldM goSub ct (map StructSelector $ Map.keys (stcSubs struct))
  TNList l -> foldM goSub ct $ map IndexSelector [0 .. length (lstSubs l) - 1]
  TNFunc fn -> foldM goSub ct $ map FuncArgSelector [0 .. length (fncArgs fn) - 1]
  TNDisj d -> do
    uctx <- maybe (return ct) (\_ -> goSub ct DisjDefaultSelector) (dsjDefault d)
    foldM goSub uctx (map DisjDisjunctSelector [0 .. length (dsjDisjuncts d) - 1])
  _ -> return ct
 where
  levelUp :: (CommonEnv m) => Selector -> TreeCursor -> m TreeCursor
  levelUp = propUpTCSel

  getSubTC :: (CommonEnv m) => Selector -> TreeCursor -> m TreeCursor
  getSubTC = goDownTCSelErr

  goSub :: (CommonEnv m) => CtxTree -> Selector -> m CtxTree
  goSub acc sel =
    if isTreeBottom (cvVal acc)
      then return acc
      else
        mapEvalCVCur (getSubTC sel) acc
          >>= f
          >>= mapEvalCVCur (levelUp sel)

{- | Traverse the leaves of the tree cursor in the following order
1. Traverse the current node.
2. Traverse the sub-tree with the selector.
-}
traverseCV :: (CommonEnv m) => (CtxTree -> CommonEnvMonad CtxTree) -> CtxTree -> m CtxTree
traverseCV f ct = case treeNode (cvVal ct) of
  TNStruct _ -> f ct >>= traverseSubNodes (traverseCV f)
  TNDisj _ -> f ct >>= traverseSubNodes (traverseCV f)
  TNFunc _ -> f ct >>= traverseSubNodes (traverseCV f)
  TNList _ -> f ct >>= traverseSubNodes (traverseCV f)
  _ -> f ct

setOrigNodesCV :: (CommonEnv m) => CtxTree -> m CtxTree
setOrigNodesCV = traverseCV (mapEvalCVCur f)
 where
  f :: (CommonEnv m) => TreeCursor -> m TreeCursor
  f tc =
    let cur = vcFocus tc
        updated = if isNothing (treeOrig cur) then cur{treeOrig = Just cur} else cur
     in return (ValCursor updated (vcCrumbs tc))

-- Evaluate the tree cursor. Notice that the tree cursor can start from any node in the tree, so that the constraint is
-- not EvalEnv.
evalCV :: (CommonEnv m) => CtxTree -> m CtxTree
evalCV ct = do
  res <- case treeNode (cvVal ct) of
    TNFunc fn -> evalFunc ((fn,) <$> ct)
    TNConstraint c ->
      let
        origAtomT = mkNewTree (TNAtom $ cnsOrigAtom c)
        op = mkNewTree (TNFunc $ mkBinaryOp AST.Unify (cnsUnify c) origAtomT (cnsCnstr c))
       in
        do
          dump $ printf "evalCV: constraint unify tc:\n%s" (show (ValCursor op (ctxCrumbs . cvCtx $ ct)))
          x <- evalCV $ op <$ ct
          if cvVal x == origAtomT
            -- discard other states when evaluating the sub structure of the constraint.
            then return $ origAtomT <$ ct
            else
              throwError $
                printf
                  "evalCV: constraint not satisfied, %s != %s"
                  (show (cvVal x))
                  (show origAtomT)
    TNLink l -> evalLink ((l,) <$> ct)
    TNStruct struct -> evalStruct ((struct,) <$> ct)
    TNList _ -> traverseSubNodes evalCV ct
    TNDisj _ -> traverseSubNodes evalCV ct
    _ -> return ct
  let
    resPath = cvPath res
    notifers = ctxNotifiers . cvCtx $ res
    deps = maybe [] id (Map.lookup resPath notifers)
  final <- foldM (\acc dep -> reEval dep (cvVal res) acc) res deps
  dump $ printf "evalCV: path: %s, final result: %s" (show $ cvPath ct) (show $ cvVal final)
  return final

-- | Re-evaluate the tree indicated by the path with the new value.
reEval :: (CommonEnv m) => Path -> Tree -> CtxTree -> m CtxTree
reEval tp t ct = do
  dump $ printf "reEval: %s -> %s, new value: %s" (show $ cvPath ct) (show tp) (show t)
  tar <- goPath tp ct
  utar <- case treeNode (cvVal tar) of
    TNFunc fn -> do
      if not (fncHasRef fn)
        then throwError $ printf "reEval: the target node %s is not a reference." (show $ cvVal tar)
        else do
          let newFn = fn{fncRes = Just t, fncFunc = \_ -> return t}
          return $ substTN (TNFunc newFn) (cvVal tar) <$ tar
    _ -> throwError $ printf "reEval: the target node %s is not a function." (show $ cvVal tar)
  dump $ printf "reEval: path: %s, updated func: %s" (show $ cvPath tar) (show $ cvVal utar)
  fn <- upTillHighestFunc utar
  dump $ printf "reEval: re-evaluating the function, path: %s, node: %s" (show $ cvPath fn) (show $ cvVal fn)
  evalCV fn >>= goPath (cvPath ct)

upTillHighestFunc :: (CommonEnv m) => CtxTree -> m CtxTree
upTillHighestFunc ct =
  if null sels || not hasFuncSel
    then return ct
    else mapEvalCVCur propUpTC ct >>= upTillHighestFunc
 where
  (Path.Path sels) = cvPath ct
  hasFuncSel =
    any
      ( \s -> case s of
          FuncArgSelector _ -> True
          _ -> False
      )
      sels

goPath :: (CommonEnv m) => Path -> CtxTree -> m CtxTree
goPath p ct =
  if headSel p /= Just Path.RootSelector
    then throwError "goPath: the path should start with the root selector."
    else do
      let
        path = fromJust $ tailPath p
        tc = getCVCursor ct
      res <- searchTCPath path tc
      case res of
        Nothing -> throwError $ printf "goPath: path %s not found." (show p)
        Just tar -> return $ setCVCur tar ct

-- Follow the link by moving the cursor to the target node indicated by the link.
-- TODO: Update the substituted tree cursor.
followLink :: (CommonEnv m) => Link -> TreeCursor -> m (Maybe (Path, Tree))
followLink link tc = do
  res <- searchTCPath (lnkTarget link) tc
  case res of
    Nothing -> return Nothing
    Just tarTC ->
      let tarAbsPath = canonicalizePath $ tcPath tarTC
       in if
            | tarAbsPath == selfAbsPath -> do
                dump $
                  printf
                    "%s: reference cycle detected: %s == %s."
                    header
                    (show $ tcPath tc)
                    (show $ tcPath tarTC)
                return $ Just (tcPath tarTC, mkNewTree TNRefCycleVar)
            | isPrefix tarAbsPath selfAbsPath ->
                throwError $
                  printf
                    "structural cycle detected. %s is a prefix of %s"
                    (show tarAbsPath)
                    (show selfAbsPath)
            | otherwise ->
                let tarNode = vcFocus tarTC
                    substTC = ValCursor tarNode (vcCrumbs tc)
                 in case treeNode tarNode of
                      TNLink newLink -> do
                        dump $ printf "%s: substitutes to another link. go to %s" header (show $ lnkTarget newLink)
                        followLink newLink substTC
                      TNConstraint c -> do
                        dump $ printf "%s: substitutes to the atom value of the constraint" header
                        return $ Just (tcPath tarTC, mkAtomTree (amvAtom . cnsAtom $ c))
                      _ -> do
                        dump $ printf "%s: resolves to tree node:\n%s" header (show tarNode)
                        return $ Just (tcPath tarTC, tarNode)
 where
  selfAbsPath = canonicalizePath $ tcPath tc

  header :: String
  header = printf "followLink, link %s, path: %s" (show $ lnkTarget link) (show $ tcPath tc)

{- | Search the tree cursor up to the root and return the tree cursor that points to the variable.
The cursor will also be propagated to the parent block.
-}
searchTCVar :: (CommonEnv m) => Selector -> TreeCursor -> m (Maybe TreeCursor)
searchTCVar sel@(StructSelector ssel@(StringSelector _)) tc = case treeNode (vcFocus tc) of
  TNStruct struct -> case Map.lookup ssel (stcSubs struct) of
    Just sf ->
      if lbAttrIsVar (ssfAttr sf)
        then return . Just $ mkSubTC sel (ssfField sf) tc
        else goUp tc
    _ -> goUp tc
  _ -> goUp tc
 where
  goUp :: (CommonEnv m) => TreeCursor -> m (Maybe TreeCursor)
  goUp (ValCursor _ [(RootSelector, _)]) = return Nothing
  goUp utc = propUpTC utc >>= searchTCVar sel
searchTCVar _ _ = return Nothing

{- | Search the tree cursor up to the root and return the tree cursor that points to the path.
The path should not start with the root selector.
-}
searchTCPath :: (CommonEnv m) => Path -> TreeCursor -> m (Maybe TreeCursor)
searchTCPath p tc =
  if headSel p == Just Path.RootSelector
    then throwError "searchTCPath: the path should not start with the root selector."
    else runEnvMaybe $ do
      fstSel <- newCommonEnvMaybe $ headSel p
      base <- EnvMaybe $ searchTCVar fstSel tc
      tailP <- newCommonEnvMaybe $ tailPath p
      -- TODO: what if the base contains unevaluated nodes?
      newCommonEnvMaybe $ goDownTCPath tailP base

indexBySel :: (CommonEnv m) => Selector -> AST.UnaryExpr -> Tree -> m Tree
indexBySel sel ue t = case treeNode t of
  -- The tree is an evaluated, final struct, which could be formed by an in-place expression, like ({}).a.
  TNStruct struct -> case sel of
    StructSelector s -> case Map.lookup s (stcSubs struct) of
      Just sf -> return (ssfField sf)
      Nothing ->
        return $
          mkNewTree
            ( TNFunc $
                Func
                  { fncName = "indexBySel"
                  , fncType = RegularFunc
                  , fncHasRef = getFuncHasRef [t]
                  , fncArgs = [t]
                  , fncExprGen = \_ -> return $ AST.ExprUnaryExpr ue
                  , fncFunc = constFunc
                  , fncRes = Nothing
                  }
            )
    s -> throwError $ printf "invalid selector: %s" (show s)
  TNList list -> case sel of
    IndexSelector i ->
      return $
        if i < length (lstSubs list)
          then lstSubs list !! i
          else mkBottomTree $ "index out of bound: " ++ show i
    _ -> throwError "invalid list selector"
  TNLink link ->
    return $
      mkNewTree
        ( TNLink $
            link
              { lnkTarget = appendSel sel (lnkTarget link)
              , lnkExpr = ue
              }
        )
  TNDisj dj ->
    if isJust (dsjDefault dj)
      then indexBySel sel ue (fromJust (dsjDefault dj))
      else throwError insertErr
  TNFunc _ ->
    return $
      mkNewTree
        ( TNFunc $
            Func
              { fncName = "indexBySel"
              , fncType = RegularFunc
              , fncHasRef = getFuncHasRef [t]
              , fncFunc = \ts ->
                  -- Does not change the state.
                  getCTFromFuncEnv
                    >>= mapEvalCVCur (return . mkSubTC sel (ts !! 0))
                    >>= evalCV
                    >>= mapEvalCV (indexBySel sel ue)
                    >>= return . cvVal
              , fncExprGen = \_ -> return $ AST.ExprUnaryExpr ue
              , fncArgs = [t]
              , fncRes = Nothing
              }
        )
  _ -> throwError insertErr
 where
  insertErr = printf "index: cannot index %s with sel: %s" (show t) (show sel)

  -- TODO: fix
  constFunc :: (FuncEnv m) => [Tree] -> m Tree
  constFunc _ = throwError "constFunc"

indexByTree :: (CommonEnv m) => Tree -> AST.UnaryExpr -> Tree -> m Tree
indexByTree sel ue tree =
  case treeNode sel of
    TNAtom ta -> do
      idxsel <- selFromAtom ta
      indexBySel idxsel ue tree
    TNDisj dj -> case dsjDefault dj of
      Just df -> do
        dump $ printf "indexByTree: default disjunct: %s" (show df)
        indexByTree df ue tree
      Nothing -> return invalidSelector
    TNConstraint c -> do
      idxsel <- selFromAtom (cnsOrigAtom c)
      indexBySel idxsel ue tree
    TNLink _ -> return $ mkIndexByTreeFunc sel tree
    TNFunc fn ->
      if isJust (fncRes fn)
        then indexByTree (fromJust $ fncRes fn) ue tree
        else return $ mkIndexByTreeFunc sel tree
    _ -> return invalidSelector
 where
  selFromAtom :: (CommonEnv m) => AtomV -> m Selector
  selFromAtom a = case amvAtom a of
    (String s) -> return (StructSelector $ StringSelector s)
    (Int i) -> return $ IndexSelector $ fromIntegral i
    _ -> throwError "extendTCIndex: invalid selector"

  invalidSelector :: Tree
  invalidSelector = mkNewTree (TNBottom $ Bottom $ printf "invalid selector: %s" (show sel))

  mkIndexByTreeFunc :: Tree -> Tree -> Tree
  mkIndexByTreeFunc selArg treeArg =
    mkNewTree
      ( TNFunc $
          Func
            { fncName = "indexByTree"
            , fncType = RegularFunc
            , fncHasRef = getFuncHasRef [selArg, treeArg]
            , fncArgs = [selArg, treeArg]
            , fncExprGen = \_ -> return $ AST.ExprUnaryExpr ue
            , fncFunc =
                \ts -> do
                  cv <- getCTFromFuncEnv
                  selCV <-
                    mapEvalCVCur (return . mkSubTC (FuncArgSelector 0) (ts !! 0)) cv
                      >>= evalCV
                  dump $
                    printf
                      "indexByTree Func: path: %s, sel: %s, tree: %s"
                      (show $ cvPath cv)
                      (show $ cvVal selCV)
                      (show $ ts !! 1)
                  t <- indexByTree (cvVal selCV) ue (ts !! 1)
                  dump $ printf "indexByTree Func: resolved to %s" (show t)
                  u <- evalCV $ t <$ cv
                  return $ cvVal u
            , fncRes = Nothing
            }
      )