{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

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
  FuncType (..),
  HasCtxVal (..),
  LabelAttr (..),
  List (..),
  Number (..),
  PatternStructField (..),
  PendingStructElem (..),
  StaticStructField (..),
  Struct (..),
  StructElemAdder (..),
  StructLabelType (..),
  Tree (..),
  TreeCursor,
  TreeMonad,
  TreeNode (..),
  ValCursor (..),
  RefCycle (..),
  bdRep,
  buildASTExpr,
  debugRunEvalEnv,
  defaultLabelAttr,
  dump,
  eliminateTMCycle,
  emptyContext,
  emptyStruct,
  evalFuncArg,
  evalTM,
  exhaustTM,
  getCVCursor,
  getTMTree,
  insertUnifyStruct,
  isFuncRef,
  isTreeValue,
  mergeAttrs,
  mkAtomTree,
  mkAtomVTree,
  mkBinaryOp,
  mkBinaryOpDir,
  mkBottomTree,
  mkBoundsTree,
  mkCVFromCur,
  mkCnstrTree,
  mkDisjTree,
  mkIndexFuncTree,
  mkListTree,
  mkNewTree,
  mkRefFunc,
  mkReference,
  mkStructTree,
  mkUnaryOp,
  mkVarLinkTree,
  putTMTree,
  setOrigNodes,
  substTN,
  updateCnstrAtom,
  validateCnstrs,
  withDumpInfo,
  withTree,
)
where

import qualified AST
import Control.Monad (foldM, unless, when)
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
  evalState,
  evalStateT,
  gets,
  modify,
 )
import Data.ByteString.Builder (
  Builder,
  char7,
  string7,
  toLazyByteString,
 )
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing)
import qualified Data.Set as Set
import Data.Text (pack)
import Path
import Text.Printf (printf)

class BuildASTExpr a where
  -- The first argument is a flag to indicate whether the expression is required to be concrete.
  buildASTExpr :: forall m. (CommonEnv m) => Bool -> a -> m AST.Expression

class TreeRepBuilder a where
  repTree :: Int -> a -> String

class TreeRepBuilderIter a where
  -- (symbol, meta, fields, listedMetas)
  -- field : (Label, Attr, Value)
  iterRepTree :: a -> (String, String, [(String, String, a)], [(String, String)])

dump :: (MonadLogger m) => String -> m ()
dump !s = logDebugN . pack $ s

type CommonEnv m = (MonadError String m, MonadLogger m, MonadReader Config m)

type EvalEnvState s m = (CommonEnv m, MonadState s m)

type EvalEnv m = EvalEnvState Context m

type EvalMonad a = forall m. (EvalEnv m) => m a

debugRunEvalEnv :: (MonadIO m, MonadError String m) => EvalMonad a -> m a
debugRunEvalEnv a = runStderrLoggingT (runReaderT (evalStateT a emptyContext) Config{})

data Config = Config
  { cfUnify :: forall s m. (TreeMonad s m) => Tree -> Tree -> m ()
  , cfCreateCnstr :: Bool
  , cfMermaid :: Bool
  }

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
  buildASTExpr :: (CommonEnv m) => Bool -> Atom -> m AST.Expression
  buildASTExpr _ a = return $ (AST.litCons . aToLiteral) a

aToLiteral :: Atom -> AST.Literal
aToLiteral a = case a of
  String s -> AST.StringLit $ AST.SimpleStringLit (show AST.DoubleQuote ++ s ++ show AST.DoubleQuote)
  Int i -> AST.IntLit i
  Float f -> AST.FloatLit f
  Bool b -> AST.BoolLit b
  Null -> AST.NullLit

-- Some rules:
-- 1. If a node is a Func that contains references, then the node should not be supplanted to other places without
-- changing the dependencies.
-- 2. Evaluation is top-down. Evaluation do not go deeper unless necessary.
data Tree = Tree
  { treeNode :: TreeNode
  , treeOrig :: Maybe Tree
  , treeEvaled :: Bool
  }

setTN :: TreeNode -> Tree -> Tree
setTN n t = t{treeNode = n}

setOrig :: Tree -> Tree -> Tree
setOrig t o = t{treeOrig = Just o}

setTNOrig :: TreeNode -> Tree -> Tree
setTNOrig tn o = (mkNewTree tn){treeOrig = Just o}

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

instance TreeRepBuilder Tree where
  repTree = treeToSimpleStr

instance TreeRepBuilderIter Tree where
  iterRepTree t = case treeNode t of
    TNAtom leaf -> (symbol, show (amvAtom leaf), emptyTreeFields, [])
    TNStruct s ->
      let ordLabels = printf "ord:[%s]" $ intercalate ", " (map show $ stcOrdLabels s)
          attr :: LabelAttr -> String
          attr a = case lbAttrType a of
            SLRegular -> mempty
            SLRequired -> "!"
            SLOptional -> "?"

          isVar :: LabelAttr -> String
          isVar a =
            if lbAttrIsVar a
              then ",v"
              else mempty

          slabelAttr :: StructSelector -> String
          slabelAttr k =
            let sf = stcSubs s Map.! k
             in attr (ssfAttr sf) <> isVar (ssfAttr sf)

          dlabelAttr :: DynamicStructField -> String
          dlabelAttr dsf = attr (dsfAttr dsf) <> isVar (dsfAttr dsf) <> ",e,dsf"

          plabelAttr :: String
          plabelAttr = "e,psf"

          psfLabelAttr :: PatternStructField -> String
          psfLabelAttr psf =
            "["
              <> show (psfPattern psf)
              <> "]"
              <> ",psf"

          fields :: [(String, String, Tree)]
          fields =
            map (\k -> (show k, slabelAttr k, ssfField $ stcSubs s Map.! k)) (structStaticLabels s)
              ++ map
                (\(j, k) -> (show (StructSelector $ PatternSelector j), psfLabelAttr k, psfValue k))
                (zip [0 ..] (stcPatterns s))
              ++ map
                ( \j ->
                    let a = stcPendSubs s !! j
                     in case a of
                          DynamicField dsf -> (show (StructSelector $ PendingSelector j), dlabelAttr dsf, dsfValue dsf)
                          PatternField _ val -> (show (StructSelector $ PatternSelector j), plabelAttr, val)
                )
                (structPendIndexes s)
       in (symbol, ordLabels, fields, [])
    TNList vs ->
      let fields = map (\(j, v) -> (show (IndexSelector j), mempty, v)) (zip [0 ..] (lstSubs vs))
       in (symbol, mempty, fields, [])
    TNDisj d ->
      let dfField = maybe [] (\v -> [(show DisjDefaultSelector, mempty, v)]) (dsjDefault d)
          djFields = map (\(j, v) -> (show $ DisjDisjunctSelector j, mempty, v)) (zip [0 ..] (dsjDisjuncts d))
       in (symbol, mempty, dfField ++ djFields, [])
    TNConstraint c ->
      ( symbol
      , mempty
      ,
        [ ("Atom", mempty, mkAtomVTree (cnsAtom c))
        , (show unaryOpSelector, mempty, cnsValidator c)
        ]
      , []
      )
    -- TODO: selector
    TNBounds b -> (symbol, mempty, [], map (\(j, v) -> (show j, repTree 0 v)) (zip [0 ..] (bdsList b)))
    TNRefCycle c -> case c of
      RefCycle p -> (symbol, show p, emptyTreeFields, [])
      RefCycleTail -> (symbol, "tail", emptyTreeFields, [])
    TNFunc f ->
      let
        args = map (\(j, v) -> (show (FuncArgSelector j), mempty, v)) (zip [0 ..] (fncArgs f))
        res = maybe mempty (\s -> [("res", mempty, s)]) (fncRes f)
       in
        ( symbol
        , fncName f
            <> ( if isFuncRef f
                  then mempty
                  else
                    printf ", args:%s" (show . length $ fncArgs f)
                      <> (if funcHasRef f then ", hasRef" else mempty)
               )
        , args ++ res
        , []
        )
    TNBottom b -> (symbol, show b, emptyTreeFields, [])
    TNTop -> (symbol, mempty, emptyTreeFields, [])
   where
    emptyTreeFields :: forall a. (TreeRepBuilder a) => [(String, String, a)]
    emptyTreeFields = []

    symbol :: String
    symbol = showTreeSymbol t

treeToSimpleStr :: Int -> Tree -> String
treeToSimpleStr toff t =
  let (symbol, meta, fields, listedMetas) = iterRepTree t
   in "("
        <> (symbol <> " " <> meta)
        <> ( if null fields
              then mempty
              else
                -- we need to add a newline for the fields block.
                "\n"
                  <> foldl
                    ( \acc (label, attr, sub) ->
                        let pre = replicate (toff + 1) ' ' <> "(" <> label <> attr <> " "
                         in acc
                              <> pre
                              <> treeToSimpleStr (length pre) sub
                              <> ")"
                              <> "\n"
                    )
                    mempty
                    fields
                  -- reserve spaces for the closing parenthesis.
                  <> replicate toff ' '
           )
        <> ( if null listedMetas
              then mempty
              else
                "\n"
                  <> foldl
                    ( \acc (label, lmeta) ->
                        let pre = replicate (toff + 1) ' ' <> "(" <> label <> " "
                         in acc
                              <> pre
                              <> lmeta
                              <> ")"
                              <> "\n"
                    )
                    mempty
                    listedMetas
                  <> replicate toff ' '
           )
        <> ")"

pathToMermaidNodeID :: Path -> String
pathToMermaidNodeID (Path sels) = go (reverse sels)
 where
  mapSel :: Selector -> String
  mapSel RootSelector = "root"
  mapSel sel = show sel

  go :: [Selector] -> String
  go [sel] = mapSel sel
  go (sel : xs) = mapSel sel ++ "_" ++ go xs
  go [] = "nil"

treeToMermaid :: (MonadState Int m) => String -> Path -> Tree -> m String
treeToMermaid msg evalPath root = do
  let w = printf "---\ntitle: %s, path %s\n---\n" msg (show evalPath) <> "flowchart TD"
  rest <- subgraph 0 root "root"
  return $ w <> "\n" <> rest <> printf "style %s fill:#56e,stroke:#333,stroke-width:4px" (pathToMermaidNodeID evalPath)
 where
  indent :: Int -> String
  indent n = replicate n ' '

  subgraph :: (MonadState Int m) => Int -> Tree -> String -> m String
  subgraph toff t path = do
    let
      (symbol, meta, fields, _) = iterRepTree t
      writeLine :: String -> String
      writeLine content = indent toff <> content <> "\n"
      writer =
        writeLine
          ( printf
              "%s[\"`%s`\"]"
              path
              ( symbol
                  -- <> printf ", O:%s" (if (isJust $ treeOrig t) then "Y" else "N")
                  <> if null meta then mempty else " " <> meta
              )
          )

    foldM
      ( \acc (label, _, sub) -> do
          let subName = path ++ "_" ++ label
          rest <- subgraph (toff + 2) sub subName
          return $
            acc
              <> writeLine (printf "%s -->|%s| %s" path label subName)
              <> rest
      )
      writer
      fields

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNAtom _ -> "v"
  TNBounds _ -> "b"
  TNStruct{} -> "{}"
  TNList{} -> "[]"
  TNDisj{} -> "dj"
  TNConstraint{} -> "Cnstr"
  TNRefCycle _ -> "RC"
  TNFunc{} -> "fn"
  TNBottom _ -> "_|_"
  TNTop -> "_"

instance Show Tree where
  show = treeToSimpleStr 0

instance BuildASTExpr Tree where
  buildASTExpr cr t = case treeNode t of
    TNTop -> return $ AST.litCons AST.TopLit
    TNBottom _ -> return $ AST.litCons AST.BottomLit
    TNAtom s -> buildASTExpr cr s
    TNBounds b -> buildASTExpr cr b
    TNStruct s -> buildASTExpr cr s
    TNList l -> buildASTExpr cr l
    TNDisj d -> buildASTExpr cr d
    TNFunc fn -> buildASTExpr cr fn
    TNConstraint c ->
      maybe
        (throwError $ printf "orig expr for %s does not exist" (show (cnsAtom c)))
        (buildASTExpr cr)
        (treeOrig t)
    TNRefCycle c -> case c of
      RefCycle p -> do
        if isPathEmpty p
          -- If the path is empty, then it is a reference to the itself.
          then return $ AST.litCons AST.TopLit
          else buildASTExpr cr (fromJust $ treeOrig t)
      RefCycleTail -> return $ AST.litCons AST.TopLit

mkNewTree :: TreeNode -> Tree
mkNewTree n = Tree{treeNode = n, treeOrig = Nothing, treeEvaled = False}

substTN :: TreeNode -> Tree -> Tree
substTN n t = t{treeNode = n}

-- | TreeNode represents a tree structure that contains values.
data TreeNode
  = -- | TNStruct is a struct that contains a value and a map of selectors to Tree.
    TNStruct Struct
  | TNList List
  | TNDisj Disj
  | -- | TNAtom contains an atom value.
    TNAtom AtomV
  | TNBounds Bounds
  | TNConstraint Constraint
  | TNRefCycle RefCycle
  | TNFunc Func
  | TNTop
  | TNBottom Bottom

instance Eq TreeNode where
  (==) (TNStruct s1) (TNStruct s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNAtom l1) (TNAtom l2) = l1 == l2
  (==) (TNConstraint c1) (TNConstraint c2) = c1 == c2
  (==) (TNRefCycle c1) (TNRefCycle c2) = c1 == c2
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

-- TODO: should add Constraint
isTreeAtom :: Tree -> Bool
isTreeAtom t = case treeNode t of
  TNAtom _ -> True
  _ -> False

isTreeBottom :: Tree -> Bool
isTreeBottom t = case treeNode t of
  TNBottom _ -> True
  _ -> False

isTreeValue :: Tree -> Bool
isTreeValue n = case treeNode n of
  TNAtom _ -> True
  TNBounds _ -> True
  TNStruct _ -> True
  TNList _ -> True
  TNDisj _ -> True
  TNConstraint _ -> True
  TNBottom _ -> True
  TNTop -> True
  TNRefCycle _ -> False
  TNFunc _ -> False

isTreeRefCycle :: Tree -> Bool
isTreeRefCycle t = case treeNode t of
  TNRefCycle _ -> True
  _ -> False

newtype List = List {lstSubs :: [Tree]}

instance Eq List where
  (==) l1 l2 = lstSubs l1 == lstSubs l2

instance BuildASTExpr List where
  buildASTExpr c l =
    AST.litCons . AST.ListLit . AST.EmbeddingList <$> mapM (buildASTExpr c) (lstSubs l)

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
  { -- For pattern constraint, this is omitted.
    dsfAttr :: LabelAttr
  , dsfLabel :: Tree
  , dsfLabelExpr :: AST.Expression
  , dsfValue :: Tree
  }
  deriving (Show)

instance Eq DynamicStructField where
  (==) f1 f2 =
    dsfValue f1 == dsfValue f2
      && dsfAttr f1 == dsfAttr f2
      && dsfLabel f1 == dsfLabel f2
      && dsfLabelExpr f1 == dsfLabelExpr f2

data PatternStructField = PatternStructField
  { psfPattern :: Bounds
  , psfValue :: Tree
  }
  deriving (Show)

instance Eq PatternStructField where
  (==) f1 f2 = psfPattern f1 == psfPattern f2 && psfValue f1 == psfValue f2

data PendingStructElem = DynamicField DynamicStructField | PatternField Tree Tree
  deriving (Show, Eq)

modifyPSEValue :: (Tree -> Tree) -> PendingStructElem -> PendingStructElem
modifyPSEValue f pse = case pse of
  DynamicField dsf -> DynamicField dsf{dsfValue = f (dsfValue dsf)}
  PatternField pattern val -> PatternField pattern (f val)

data Struct = Struct
  { stcOrdLabels :: [StructSelector] -- Should only contain string labels.
  , stcSubs :: Map.Map StructSelector StaticStructField
  , stcPatterns :: [PatternStructField]
  , stcPendSubs :: [PendingStructElem]
  }

instance Eq Struct where
  (==) s1 s2 =
    stcOrdLabels s1 == stcOrdLabels s2
      && stcSubs s1 == stcSubs s2
      && stcPatterns s1 == stcPatterns s2
      && stcPendSubs s1 == stcPendSubs s2

instance BuildASTExpr Struct where
  -- Patterns are not included in the AST.
  buildASTExpr concrete s =
    let
      processStaticField :: (CommonEnv m) => (StructSelector, StaticStructField) -> m AST.Declaration
      processStaticField (label, sf) = case label of
        StringSelector sel -> do
          e <- buildASTExpr concrete (ssfField sf)
          return $
            AST.FieldDecl $
              AST.Field
                [ labelCons (ssfAttr sf) $
                    if lbAttrIsVar (ssfAttr sf)
                      then AST.LabelID sel
                      else AST.LabelString sel
                ]
                e
        _ -> throwError "Only StringSelector is allowed in static fields."

      processDynField :: (CommonEnv m) => DynamicStructField -> m AST.Declaration
      processDynField sf = do
        e <- buildASTExpr concrete (dsfValue sf)
        return $
          AST.FieldDecl $
            AST.Field
              [ labelCons (dsfAttr sf) $ AST.LabelNameExpr (dsfLabelExpr sf)
              ]
              e

      labelCons :: LabelAttr -> AST.LabelName -> AST.Label
      labelCons attr ln =
        AST.Label $
          AST.LabelName
            ln
            ( case lbAttrType attr of
                SLRegular -> AST.RegularLabel
                SLRequired -> AST.RequiredLabel
                SLOptional -> AST.OptionalLabel
            )
     in
      do
        stcs <- sequence [processStaticField (l, stcSubs s Map.! l) | l <- structStaticLabels s]
        dyns <-
          sequence $
            foldr
              ( \x acc -> case x of
                  DynamicField dsf -> processDynField dsf : acc
                  _ -> acc
              )
              []
              (stcPendSubs s)
        return $ AST.litCons $ AST.StructLit (stcs ++ dyns)

emptyStruct :: Struct
emptyStruct =
  Struct
    { stcOrdLabels = []
    , stcSubs = Map.empty
    , stcPendSubs = []
    , stcPatterns = []
    }

data StructElemAdder
  = Static StructSelector StaticStructField
  | Dynamic DynamicStructField
  | Pattern Tree Tree
  deriving (Show)

mkStructTree :: [StructElemAdder] -> Tree
mkStructTree as =
  mkNewTree . TNStruct $
    Struct
      { stcOrdLabels = ordLabels
      , stcSubs = Map.fromList statics
      , stcPatterns = []
      , stcPendSubs = pendings
      }
 where
  ordLabels = [l | Static l _ <- as]
  statics = [(s, sf) | Static s sf <- as]
  pendings =
    foldr
      ( \x acc ->
          case x of
            Dynamic dsf -> DynamicField dsf : acc
            Pattern pattern val -> PatternField pattern val : acc
            _ -> acc
      )
      []
      as

-- Insert a new field into the struct. If the field is already in the struct, then unify the field with the new field.
insertUnifyStruct :: StructElemAdder -> (forall s m. (TreeMonad s m) => Tree -> Tree -> m ()) -> Struct -> Struct
insertUnifyStruct adder unify struct = case adder of
  (Static sel sf) -> case subs Map.!? sel of
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
  (Dynamic dsf) -> struct{stcPendSubs = stcPendSubs struct ++ [DynamicField dsf]}
  (Pattern pattern val) -> struct{stcPendSubs = stcPendSubs struct ++ [PatternField pattern val]}
 where
  subs = stcSubs struct

structStaticLabels :: Struct -> [StructSelector]
structStaticLabels = filter (\x -> viewStructSelector x == 0) . stcOrdLabels

structPendIndexes :: Struct -> [Int]
structPendIndexes s = [0 .. length (stcPendSubs s) - 1]

-- TODO: remove origStruct as the function argument
evalStruct :: forall s m. (TreeMonad s m) => Struct -> m ()
evalStruct origStruct = do
  delIdxes <- do
    mapM_ (evalStaticSF . fst) (Map.toList . stcSubs $ origStruct)
    mapM_ evalPattern (zip (map PatternSelector [0 ..]) (stcPatterns origStruct))
    foldM evalPendSE [] (zip (map PendingSelector [0 ..]) (stcPendSubs origStruct))

  whenStruct () $ \struct -> do
    let newStruct = mk struct{stcPendSubs = [pse | (i, pse) <- zip [0 ..] (stcPendSubs struct), i `notElem` delIdxes]}
    withDumpInfo $ \path _ ->
      dump $ printf "evalStruct: path: %s, new struct: %s" (show path) (show newStruct)
    putTMTree newStruct
 where
  mk = mkNewTree . TNStruct

evalStaticSF :: (TreeMonad s m) => StructSelector -> m ()
evalStaticSF sel = whenStruct () $ \struct ->
  inSubTM (StructSelector sel) (ssfField (stcSubs struct Map.! sel)) exhaustTM

evalPattern :: (TreeMonad s m) => (StructSelector, PatternStructField) -> m ()
evalPattern (sel, psf) = whenStruct () $ \_ -> inSubTM (StructSelector sel) (psfValue psf) exhaustTM

evalPendSE :: (TreeMonad s m) => [Int] -> (StructSelector, PendingStructElem) -> m [Int]
evalPendSE idxes (sel, pse) = whenStruct idxes $ \struct -> do
  case (sel, pse) of
    (PendingSelector i, DynamicField dsf) -> do
      -- evaluate the dynamic label.
      label <- inSubTM (StructSelector sel) (dsfLabel dsf) $ exhaustTM >> getTMTree
      withDumpInfo $ \path _ ->
        dump $
          printf
            "evalPendSE: path: %s, dynamic label is evaluated to %s"
            (show path)
            (show label)
      case treeNode label of
        TNAtom (AtomV (String s)) -> do
          Config{cfUnify = unify} <- ask
          let
            mergedSF = dynToStaticField dsf (stcSubs struct Map.!? StringSelector s) unify
            sSel = StructSelector $ StringSelector s

          pushTMSub sSel (ssfField mergedSF)
          mergedT <- exhaustTM >> getTMTree
          -- do not use propUpTCSel here because the field was not in the original struct.
          let nstruct = mkNewTree (TNStruct $ addStatic s (mergedSF{ssfField = mergedT}) struct)
          discardTMAndPut nstruct
          return (i : idxes)

        -- TODO: pending label
        _ -> putTMTree (mkBottomTree "selector can only be a string") >> return idxes
    (PendingSelector i, PatternField pattern val) -> do
      -- evaluate the pattern.
      evaledPattern <- inSubTM (StructSelector sel) pattern (exhaustTM >> getTMTree)
      withDumpInfo $ \path _ ->
        dump $
          printf
            "evalPendSE: path: %s, pattern is evaluated to %s"
            (show path)
            (show evaledPattern)
      case treeNode evaledPattern of
        TNBounds bds ->
          if null (bdsList bds)
            then putTMTree (mkBottomTree "patterns must be non-empty") >> return idxes
            else do
              Config{cfUnify = unify} <- ask
              pushTMSub (StructSelector sel) val
              defaultVal <- exhaustTM >> getTMTree
              -- apply the pattern to all existing fields.
              -- TODO: apply the pattern to filtered fields.
              let
                nodes =
                  [ mkNewTree . TNFunc $
                    mkBinaryOp AST.Unify unify (ssfField n) defaultVal
                  | n <- Map.elems (stcSubs struct)
                  ]
              mapM_ (\x -> whenNotBottom () (putTMTree x >> exhaustTM)) nodes
              -- r <- foldM (\acc n -> whenNotBottom acc (exhaustTM n)) defaultVal nodes
              whenNotBottom idxes $ do
                let newStruct = mkNewTree . TNStruct $ addPattern (PatternStructField bds defaultVal) struct
                discardTMAndPut newStruct
                return (i : idxes)
        _ ->
          putTMTree (mkBottomTree (printf "pattern should be bounds, but is %s" (show evaledPattern)))
            >> return idxes
    _ -> throwError "evalStructField: invalid selector field combination"
 where
  dynToStaticField ::
    DynamicStructField ->
    Maybe StaticStructField ->
    (forall s m. (TreeMonad s m) => Tree -> Tree -> m ()) ->
    StaticStructField
  dynToStaticField dsf sfM unify = case sfM of
    Just sf ->
      StaticStructField
        { ssfField = mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify (ssfField sf) (dsfValue dsf))
        , ssfAttr = mergeAttrs (ssfAttr sf) (dsfAttr dsf)
        }
    Nothing ->
      StaticStructField
        { ssfField = dsfValue dsf
        , ssfAttr = dsfAttr dsf
        }

  addStatic :: String -> StaticStructField -> Struct -> Struct
  addStatic s sf x =
    x
      { stcSubs = Map.insert (StringSelector s) sf (stcSubs x)
      , stcOrdLabels =
          if StringSelector s `elem` stcOrdLabels x
            then stcOrdLabels x
            else stcOrdLabels x ++ [StringSelector s]
      }

  addPattern :: PatternStructField -> Struct -> Struct
  addPattern psf x = x{stcPatterns = stcPatterns x ++ [psf]}

-- | Create a new identifier reference.
mkVarLinkTree :: String -> AST.UnaryExpr -> Tree
mkVarLinkTree var ue = mkFuncTree $ mkRefFunc (Path [StructSelector $ StringSelector var]) ue

-- | Create an index function node.
mkIndexFuncTree :: Tree -> Tree -> AST.UnaryExpr -> Tree
mkIndexFuncTree treeArg selArg ue = mkFuncTree $ case treeNode treeArg of
  TNFunc g
    | isFuncIndex g ->
        g
          { fncArgs = fncArgs g ++ [selArg]
          , fncExprGen = return $ AST.ExprUnaryExpr ue
          }
  _ ->
    Func
      { fncName = "index"
      , fncType = IndexFunc
      , fncArgs = [treeArg, selArg]
      , fncExprGen = return $ AST.ExprUnaryExpr ue
      , fncFunc = index ue
      , fncRes = Nothing
      }

treesToPath :: [Tree] -> Maybe Path
treesToPath ts = pathFromList <$> mapM treeToSel ts
 where
  treeToSel :: Tree -> Maybe Selector
  treeToSel t = case treeNode t of
    TNAtom a
      | (String s) <- va -> Just (StructSelector $ StringSelector s)
      | (Int j) <- va -> Just (IndexSelector $ fromIntegral j)
     where
      va = amvAtom a
    -- If a disjunct has a default, then we should try to use the default.
    TNDisj dj | isJust (dsjDefault dj) -> treeToSel (fromJust $ dsjDefault dj)
    _ -> Nothing

{- | Index the tree with the selectors. The index should have a list of arguments where the first argument is the tree
to be indexed, and the rest of the arguments are the selectors.
-}
index :: (TreeMonad s m) => AST.UnaryExpr -> [Tree] -> m ()
index ue ts@(t : _)
  | length ts > 1 = do
      idxPathM <- treesToPath <$> mapM evalIndexArg [1 .. length ts - 1]
      whenJustE idxPathM $ \idxPath -> case treeNode t of
        TNFunc fn
          -- If the function is a ref, then we should append the path to the ref. For example, if the ref is a.b, and
          -- the path is c, then the new ref should be a.b.c.
          | isFuncRef fn -> do
              refFunc <- appendRefFuncPath fn idxPath ue
              putTMTree (mkFuncTree refFunc) >> exhaustTM
        -- in-place expression, like ({}).a, or regular functions.
        _ -> do
          res <- evalFuncArg (FuncSelector $ FuncArgSelector 0) t False exhaustTM
          putTMTree res
          dump $ printf "index: tree is evaluated to %s, idxPath: %s" (show res) (show idxPath)

          -- descendTM can not be used here because it would change the tree cursor.
          tc <- getTMCursor
          maybe
            (throwError $ printf "index: %s is not found" (show idxPath))
            (putTMTree . vcFocus)
            (goDownTCPath idxPath tc)
          withDumpInfo $ \_ r ->
            dump $ printf "index: the indexed is %s" (show r)
 where
  evalIndexArg :: (TreeMonad s m) => Int -> m Tree
  evalIndexArg i = inSubTM (FuncSelector $ FuncArgSelector i) (ts !! i) (exhaustTM >> getTMTree)

  whenJustE :: (Monad m) => Maybe a -> (a -> m ()) -> m ()
  whenJustE m f = maybe (return ()) f m
index _ _ = throwError "index: invalid arguments"

appendRefFuncPath :: (TreeMonad s m) => Func -> Path -> AST.UnaryExpr -> m Func
appendRefFuncPath Func{fncType = RefFunc origTP} p ue = do
  -- remove original receiver because origP would not exist.
  delNotifRecvs origTP
  mkReference (appendPath p origTP) Nothing ue
appendRefFuncPath _ _ _ = throwError "appendRefFuncPath: invalid function type"

-- Reference the target node when the target node is not an atom or a cycle head.
-- It returns a function that when called, will return the latest value of the target node.
mkReference :: (TreeMonad s m) => Path -> Maybe Tree -> AST.UnaryExpr -> m Func
mkReference tp tM ue = withCtxTree $ \ct -> do
  -- add notifier. If the referenced value changes, then the reference should be updated.
  putTMContext $ addCtxNotifier (tp, cvPath ct) (cvCtx ct)
  let fn = mkRefFunc tp ue
  return $ fn{fncRes = tM}

mkRefFunc :: Path -> AST.UnaryExpr -> Func
mkRefFunc tp ue =
  Func
    { fncName = printf "&%s" (show tp)
    , fncType = RefFunc tp
    , fncArgs = []
    , fncExprGen = return $ AST.ExprUnaryExpr ue
    , fncFunc = \_ -> do
        ok <- deref tp
        when ok $ withTree $ \t -> putTMTree $ t{treeEvaled = False}
    , fncRes = Nothing
    }

-- Dereference the reference. It keeps dereferencing until the target node is not a reference node.
-- If the target is not found, the current node is kept.
-- No more evaluation is done after the dereference.
deref :: (TreeMonad s m) => Path -> m Bool
deref tp = do
  path <- getTMAbsPath
  withDumpInfo $ \_ r -> dump $ printf "deref: start, path: %s, tp: %s, tip: %s" (show path) (show tp) (show r)
  follow tp >>= \case
    (Just tar) -> do
      withDumpInfo $ \_ r -> dump $ printf "deref: done, path: %s, tp: %s, tip: %s" (show path) (show tp) (show r)
      putTMTree tar
      return True
    Nothing -> return False
 where
  -- Keep dereferencing until the target node is not a reference node.
  -- returns the target node.
  follow :: (TreeMonad s m) => Path -> m (Maybe Tree)
  follow dst = do
    srcPath <- getTMAbsPath
    dump $ printf "deref: path: %s, dereferencing: %s" (show srcPath) (show dst)
    resE <- getDstVal srcPath dst
    case resE of
      Left (cycleStartPath, cycleTailRelPath) -> do
        ctx <- getTMContext
        putTMContext $ ctx{ctxCycle = Just (cycleStartPath, cycleTailRelPath)}
        return $ Just (mkNewTree $ TNRefCycle RefCycleTail)
      Right origM
        | Nothing <- origM -> return Nothing
        | (Just orig) <- origM -> do
            withDumpInfo $ \path _ -> do
              dump $ printf "deref: path: %s, substitutes with orig: %s" (show path) (show orig)
            -- substitute the reference with the target node.
            putTMTree orig
            withTN $ \case
              -- follow the reference.
              TNFunc fn | RefFunc nextDst <- fncType fn -> do
                follow nextDst
              _ -> Just <$> getTMTree

  -- Get the value pointed by the reference.
  -- If the reference path is self or visited, then return the tuple of the absolute path of the start of the cycle and
  -- the cycle tail relative path.
  getDstVal :: (TreeMonad s m) => Path -> Path -> m (Either (Path, Path) (Maybe Tree))
  getDstVal srcPath dst = inRemoteTMMaybe dst $ do
    dstPath <- getTMAbsPath
    visitingSet <- ctxVisiting <$> getTMContext
    let
      canSrcPath = canonicalizePath srcPath
      canDstPath = canonicalizePath dstPath
    if
      | Set.member dstPath visitingSet -> do
          delNotifRecvs dstPath
          dump $ printf "deref: reference cycle detected: %s, set: %s" (show dstPath) (show $ Set.toList visitingSet)
          return $ Left (dstPath, relPath dstPath srcPath)
      | canDstPath == canSrcPath -> do
          dump $ printf "deref: reference self cycle detected: %s == %s." (show dstPath) (show srcPath)
          return $ Left (dstPath, relPath dstPath srcPath)
      | isPrefix canDstPath canSrcPath ->
          throwError $ printf "structural cycle detected. %s is a prefix of %s" (show dstPath) (show srcPath)
      -- The value of a reference is a copy of the expression associated with the field that it is bound to, with
      -- any references within that expression bound to the respective copies of the fields they were originally
      -- bound to.
      | otherwise -> withTree $ \tar -> case treeNode tar of
          -- The atom value is final, so we can return it directly.
          TNAtom _ -> return . Right $ Just tar
          TNConstraint c -> return . Right $ Just (mkAtomVTree $ cnsAtom c)
          _ -> do
            let x = fromMaybe tar (treeOrig tar)
                -- back up the original tree.
                orig = x{treeOrig = Just x}
            dump $
              printf
                "deref: path: %s, deref'd orig is: %s, set: %s, tar: %s"
                (show dstPath)
                (show orig)
                (show $ Set.toList visitingSet)
                (show tar)
            return . Right $ Just orig

  inRemoteTMMaybe :: (TreeMonad s m) => Path -> m (Either a (Maybe b)) -> m (Either a (Maybe b))
  inRemoteTMMaybe p f = do
    origAbsPath <- getTMAbsPath
    tarM <- goLowestAncPathTM p (Just <$> getTMTree)
    res <- maybe (return (Right Nothing)) (\x -> putTMTree x >> f) tarM
    backM <- goTMAbsPath origAbsPath
    unless backM $ throwError "inRemoteTMMaybe: failed to go back to the original path"
    return res

-- Delete the notification receiver.
-- This should be called when the reference becomes invalid.
delNotifRecvs :: (TreeMonad s m) => Path -> m ()
delNotifRecvs pathPrefix = do
  withContext $ \ctx -> do
    putTMContext $ ctx{ctxNotifiers = del (ctxNotifiers ctx)}
  withDumpInfo $ \path _ -> do
    notifiers <- ctxNotifiers <$> getTMContext
    dump $
      printf
        "delNotifRecvs: path: %s delete receiver prefix: %s, updated notifiers: %s"
        (show path)
        (show pathPrefix)
        (show notifiers)
 where
  del :: Map.Map Path [Path] -> Map.Map Path [Path]
  del = Map.map (filter (\p -> not (isPrefix pathPrefix p)))

newtype AtomV = AtomV
  { amvAtom :: Atom
  }

instance Show AtomV where
  show (AtomV v) = show v

instance Eq AtomV where
  (==) (AtomV v1) (AtomV v2) = v1 == v2

instance BuildASTExpr AtomV where
  buildASTExpr c (AtomV v) = buildASTExpr c v

mkAtomVTree :: AtomV -> Tree
mkAtomVTree v = mkNewTree (TNAtom v)

mkAtomTree :: Atom -> Tree
mkAtomTree a = mkAtomVTree (AtomV a)

data Disj = Disj
  { dsjDefault :: Maybe Tree
  , dsjDisjuncts :: [Tree]
  }

instance Eq Disj where
  (==) (Disj ds1 js1) (Disj ds2 js2) = ds1 == ds2 && js1 == js2

instance BuildASTExpr Disj where
  buildASTExpr c dj =
    if isJust (dsjDefault dj)
      then buildASTExpr c $ fromJust (dsjDefault dj)
      else do
        xs <- mapM (buildASTExpr c) (dsjDisjuncts dj)
        return $
          foldr1
            (AST.ExprBinaryOp AST.Disjunction)
            xs

mkDisjTree :: Maybe Tree -> [Tree] -> Tree
mkDisjTree m js = mkNewTree (TNDisj $ Disj{dsjDefault = m, dsjDisjuncts = js})

data Constraint = Constraint
  { cnsAtom :: AtomV
  , -- validator is used when validateCnstrs is called.
    cnsValidator :: Tree
  }

instance Eq Constraint where
  (==) (Constraint a1 v1) (Constraint a2 v2) = a1 == a2 && v1 == v2

isTreeCnstr :: Tree -> Bool
isTreeCnstr t = case treeNode t of
  TNConstraint _ -> True
  _ -> False

mkCnstrTree :: AtomV -> Tree -> Tree
mkCnstrTree a = setTNOrig (TNConstraint $ Constraint a (mkBottomTree "validator not initialized"))

validateCnstrs :: (TreeMonad s m) => m ()
validateCnstrs = do
  dump $ printf "validateCnstrs: start"

  ctx <- getTMContext
  -- remove all notifiers.
  putTMContext $ ctx{ctxNotifiers = Map.empty}
  -- first rewrite all functions to their results if the results exist.
  traverseTM $ withTN $ \case
    TNFunc fn -> maybe (return ()) putTMTree (fncRes fn)
    _ -> return ()

  -- then validate all constraints.
  traverseTM $ withTN $ \case
    TNConstraint c -> validateCnstr c
    _ -> return ()

-- Validate the constraint. It creates a validate function, and then evaluates the function. Notice that the validator
-- will be assigned to the constraint in the propValUp.
validateCnstr :: (TreeMonad s m) => Constraint -> m ()
validateCnstr c = withTree $ \t -> do
  withDumpInfo $ \path _ -> do
    tc <- getTMCursor
    dump $ printf "evalConstraint: path: %s, constraint unify tc:\n%s" (show path) (show tc)

  Config{cfUnify = unify} <- ask
  let
    origAtomT = mkAtomVTree $ cnsAtom c
    orig = fromJust $ treeOrig t
    fn = mkFuncTree (mkBinaryOp AST.Unify unify origAtomT orig)

  -- run the function in a sub context.
  pushTMSub unaryOpSelector fn
  x <- exhaustTM >> getTMTree
  discardTMAndPop

  when (isTreeAtom x) $ do
    when (x /= origAtomT) $
      throwError $
        printf
          "validateCnstr: constraint not satisfied, %s != %s"
          (show x)
          (show origAtomT)
    putTMTree origAtomT

updateCnstrAtom :: AtomV -> Constraint -> Constraint
updateCnstrAtom atom c = c{cnsAtom = atom}

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
  repTree _ b = "(" <> show b <> ")"

instance BuildASTExpr Bound where
  buildASTExpr _ b = return $ buildBoundASTExpr b

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

newtype Bounds = Bounds {bdsList :: [Bound]}
  deriving (Eq, Show)

instance BuildASTExpr Bounds where
  buildASTExpr c b = do
    xs <- mapM (buildASTExpr c) (bdsList b)
    return $ foldr1 (AST.ExprBinaryOp AST.Unify) xs

mkBoundsTree :: [Bound] -> Tree
mkBoundsTree bs = mkNewTree (TNBounds $ Bounds{bdsList = bs})

data FuncType = RegularFunc | DisjFunc | RefFunc Path | IndexFunc
  deriving (Eq, Show)

data Func = Func
  { fncName :: String
  , fncType :: FuncType
  , -- Args stores the arguments that may or may not need to be evaluated.
    fncArgs :: [Tree]
  , fncExprGen :: forall m. (CommonEnv m) => m AST.Expression
  , -- Note that the return value of the function should be stored in the tree.
    fncFunc :: forall s m. (TreeMonad s m) => [Tree] -> m ()
  , -- fncRes stores the temporary non-atom, non-function (isTreeValue true) result of the function.
    fncRes :: Maybe Tree
  }

instance BuildASTExpr Func where
  buildASTExpr c fn = do
    -- dump $
    --   printf
    --     "buildASTExpr: Func: %s, %s, c: %s, require: %s"
    --     (fncName fn)
    --     (show $ fncType fn)
    --     (show c)
    --     (show $ requireFuncConcrete fn)
    if
      -- If the expression must be concrete, but due to incomplete evaluation, we need to use original expression.
      | (c || requireFuncConcrete fn) -> fncExprGen fn
      | otherwise -> maybe (fncExprGen fn) (buildASTExpr c) (fncRes fn)

-- \| otherwise -> fncExprGen fn

instance Eq Func where
  (==) f1 f2 =
    fncName f1 == fncName f2
      && fncType f1 == fncType f2
      && fncArgs f1 == fncArgs f2
      && fncRes f1 == fncRes f2

requireFuncConcrete :: Func -> Bool
requireFuncConcrete fn = case fncType fn of
  RegularFunc -> fncName fn `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
  _ -> False

isFuncRef :: Func -> Bool
isFuncRef fn = case fncType fn of
  RefFunc _ -> True
  _ -> False

isFuncIndex :: Func -> Bool
isFuncIndex fn = case fncType fn of
  IndexFunc -> True
  _ -> False

funcHasRef :: Func -> Bool
funcHasRef fn = isFuncRef fn || argsHaveRef (fncArgs fn)
 where
  argsHaveRef :: [Tree] -> Bool
  argsHaveRef =
    any
      ( \x -> case treeNode x of
          TNFunc subFn -> funcHasRef subFn
          _ -> False
      )

{- | Get the result of the function. If the result is not found, return the original tree.
If the require Atom is true, then the result must be an atom. Otherwise, the function itself is returned.
-}
getFuncResOrTree :: Bool -> Tree -> Tree
getFuncResOrTree reqA t = case treeNode t of
  TNFunc fn ->
    maybe
      t
      ( \r ->
          if
            | reqA && isTreeAtom r -> r
            | reqA -> t
            | otherwise -> r
      )
      (fncRes fn)
  _ -> t

mkFuncTree :: Func -> Tree
mkFuncTree fn = mkNewTree (TNFunc fn)

mkUnaryOp :: AST.UnaryOp -> (forall s m. (TreeMonad s m) => Tree -> m ()) -> Tree -> Func
mkUnaryOp op f n =
  Func
    { fncFunc = g
    , fncType = RegularFunc
    , fncExprGen = gen
    , fncName = show op
    , fncArgs = [n]
    , fncRes = Nothing
    }
 where
  g :: (TreeMonad s m) => [Tree] -> m ()
  g [x] = f x
  g _ = throwError "invalid number of arguments for unary function"

  gen :: (CommonEnv m) => m AST.Expression
  gen = buildUnaryExpr n

  buildUnaryExpr :: (CommonEnv m) => Tree -> m AST.Expression
  buildUnaryExpr t = do
    let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
    te <- buildASTExpr c t
    case te of
      (AST.ExprUnaryExpr ue) -> return $ AST.ExprUnaryExpr $ AST.UnaryExprUnaryOp op ue
      e ->
        return $
          AST.ExprUnaryExpr $
            AST.UnaryExprUnaryOp
              op
              (AST.UnaryExprPrimaryExpr . AST.PrimExprOperand $ AST.OpExpression e)

mkBinaryOp ::
  AST.BinaryOp -> (forall s m. (TreeMonad s m) => Tree -> Tree -> m ()) -> Tree -> Tree -> Func
mkBinaryOp op f l r =
  Func
    { fncFunc = g
    , fncType = case op of
        AST.Disjunction -> DisjFunc
        _ -> RegularFunc
    , fncExprGen = gen
    , fncName = show op
    , fncArgs = [l, r]
    , fncRes = Nothing
    }
 where
  g :: (TreeMonad s m) => [Tree] -> m ()
  g [x, y] = f x y
  g _ = throwError "invalid number of arguments for binary function"

  gen :: (CommonEnv m) => m AST.Expression
  gen = do
    let c = show op `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]
    xe <- buildASTExpr c l
    ye <- buildASTExpr c r
    return $ AST.ExprBinaryOp op xe ye

mkBinaryOpDir ::
  AST.BinaryOp ->
  (forall s m. (TreeMonad s m) => Tree -> Tree -> m ()) ->
  (BinOpDirect, Tree) ->
  (BinOpDirect, Tree) ->
  Func
mkBinaryOpDir rep op (d1, t1) (_, t2) =
  case d1 of
    L -> mkBinaryOp rep op t1 t2
    R -> mkBinaryOp rep op t2 t1

{- | Evaluate the function.
 - Function evaluation is a top-down process, unlike other languages where the arguments are evaluated first.
Function call convention:
1. The result of a function is stored in the fncRes.
2. If the result can be used to replace the function itself, then the function is replaced by the result.
3. Otherwise, the function is kept.
-}
evalFunc :: (TreeMonad s m) => Func -> m ()
evalFunc fn = do
  let name = fncName fn
  withDumpInfo $ \path t ->
    dump $
      printf
        "evalFunc: path: %s, evaluate function %s, tip:\n%s"
        (show path)
        (show name)
        (show t)

  r <- fncFunc fn (fncArgs fn) >> getTMTree
  reduceFunc fn r

  withDumpInfo $ \path t ->
    dump $
      printf
        "evalFunc: path: %s, function %s evaluated to:\n%s"
        (show path)
        (show name)
        (show t)

-- Evaluate the sub node of the tree. The node must be a function.
-- Notice that the argument is a function and the result of the function is not reducible, the result is still returned.
-- This works because we do not reduce the argument. Next time the parent function is evaluated, the argument function
-- will be evaluated again.
evalFuncArg :: (TreeMonad s m) => Selector -> Tree -> Bool -> m () -> m Tree
evalFuncArg sel sub reqA f = withTN $ \case
  TNFunc _ -> do
    res <- inSubTM sel sub (f >> getTMTree)
    withDumpInfo $ \path _ ->
      dump $ printf "evalSubTM: path: %s, %s is evaluated to:\n%s" (show path) (show sub) (show res)
    return $ getFuncResOrTree reqA res
  _ -> throwError "evalFuncArg: node is not a function"

{- | Try to reduce the function by using the function result to replace the function node.
 - This should be called after the function is evaluated.
-}
reduceFunc :: (TreeMonad s m) => Func -> Tree -> m ()
reduceFunc fn val = case treeNode val of
  TNFunc newFn -> putTMTree $ mkFuncTree newFn
  _ -> do
    let
      fnHasNoRef = not (funcHasRef fn)
      reducible = isTreeAtom val || isTreeBottom val || isTreeCnstr val || isTreeRefCycle val || fnHasNoRef
    withDumpInfo $ \path _ ->
      dump $
        printf
          "reduceFunc: func %s, path: %s, is reducible: %s, fnHasNoRef: %s, args: %s"
          (show $ fncName fn)
          (show path)
          (show reducible)
          (show fnHasNoRef)
          (show $ fncArgs fn)
    if reducible
      then do
        path <- getTMAbsPath
        -- we need to delete receiver starting with the path, not only is the path. For example, if the function is
        -- index and the first argument is a reference, then the first argument dependency should also be deleted.
        delNotifRecvs path
        putTMTree val
      else putTMTree . mkFuncTree $ fn{fncRes = Just val}

newtype Bottom = Bottom {btmMsg :: String}

instance Eq Bottom where
  (==) _ _ = True

instance BuildASTExpr Bottom where
  buildASTExpr _ _ = return $ AST.litCons AST.BottomLit

instance Show Bottom where
  show (Bottom m) = m

mkBottomTree :: String -> Tree
mkBottomTree msg = mkNewTree (TNBottom $ Bottom{btmMsg = msg})

data RefCycle
  = RefCycle Path
  | RefCycleTail
  deriving (Show)

instance Eq RefCycle where
  (==) (RefCycle _) (RefCycle _) = True
  (==) RefCycleTail RefCycleTail = True
  (==) _ _ = False

instance BuildASTExpr RefCycle where
  buildASTExpr _ _ = throwError "RefCycle should not be used in the AST"

mkRefCycleTree :: Path -> Tree -> Tree
mkRefCycleTree p = setTN (TNRefCycle $ RefCycle p)

-- -- --

-- step down the tree with the given selector.
-- This should only be used by TreeCursor.
goTreeSel :: Selector -> Tree -> Maybe Tree
goTreeSel sel t =
  case (sel, treeNode t) of
    (RootSelector, _) -> Just t
    (StructSelector s, TNStruct struct) -> case s of
      StringSelector _ -> ssfField <$> Map.lookup s (stcSubs struct)
      PatternSelector i -> Just (psfValue $ stcPatterns struct !! i)
      PendingSelector i -> case stcPendSubs struct !! i of
        DynamicField dsf -> Just (dsfValue dsf)
        PatternField _ val -> Just val
    (IndexSelector i, TNList vs) -> lstSubs vs `indexList` i
    (FuncSelector f, TNFunc fn) -> case f of
      FuncArgSelector i -> fncArgs fn `indexList` i
      FuncResSelector -> fncRes fn
    (DisjDefaultSelector, TNDisj d) -> dsjDefault d
    (DisjDisjunctSelector i, TNDisj d) -> dsjDisjuncts d `indexList` i
    (_, TNConstraint c) | sel == unaryOpSelector -> Just (cnsValidator c)
    _ -> Nothing
 where
  indexList :: [a] -> Int -> Maybe a
  indexList xs i = if i < length xs then Just (xs !! i) else Nothing

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

tcPath :: ValCursor a -> Path
tcPath c = pathFromCrumbs (vcCrumbs c)

type TreeCursor = ValCursor Tree

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

mkSubTC :: Selector -> a -> TreeCursor -> ValCursor a
mkSubTC sel a tc = ValCursor a ((sel, vcFocus tc) : vcCrumbs tc)

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
    TNDisj d
      | isJust (dsjDefault d) ->
          goDownTCSel DisjDefaultSelector tc >>= go sel
    _ -> Nothing
 where
  go :: Selector -> TreeCursor -> Maybe TreeCursor
  go s x = do
    nextTree <- goTreeSel s (vcFocus x)
    return $ mkSubTC s nextTree x

{- | propUp propagates the changes made to the tip of the block to the parent block.
The structure of the tree is not changed.
-}
propValUp :: (CommonEnv m) => TreeCursor -> m TreeCursor
propValUp tc@(ValCursor _ []) = return tc
propValUp tc@(ValCursor subT ((sel, parT) : cs)) = case (sel, treeNode parT) of
  (StructSelector s, _) -> updateParStruct parT s subT
  (IndexSelector i, TNList vs) ->
    let subs = lstSubs vs
        l = TNList $ vs{lstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
     in return $ ValCursor (substTN l parT) cs
  (FuncSelector f, TNFunc fn) -> case f of
    FuncArgSelector i -> do
      let
        args = fncArgs fn
        l = TNFunc $ fn{fncArgs = take i args ++ [subT] ++ drop (i + 1) args}
      return $ ValCursor (substTN l parT) cs
    FuncResSelector -> do
      let l = TNFunc $ fn{fncRes = Just subT}
      return $ ValCursor (substTN l parT) cs
  (DisjDefaultSelector, TNDisj d) ->
    return $ ValCursor (substTN (TNDisj $ d{dsjDefault = dsjDefault d}) parT) cs
  (DisjDisjunctSelector i, TNDisj d) ->
    return $
      ValCursor
        (substTN (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)}) parT)
        cs
  (FuncSelector _, TNConstraint c) ->
    return $
      ValCursor (substTN (TNConstraint $ c{cnsValidator = subT}) parT) cs
  (ParentSelector, _) -> throwError "propValUp: ParentSelector is not allowed"
  (RootSelector, _) -> throwError "propValUp: RootSelector is not allowed"
  _ -> throwError insertErrMsg
 where
  updateParStruct :: (MonadError String m) => Tree -> StructSelector -> Tree -> m TreeCursor
  updateParStruct par label newSub = case treeNode par of
    TNStruct parStruct ->
      if
        | isTreeBottom newSub -> return (ValCursor newSub cs)
        -- the label should already exist in the parent struct.
        | Map.member label (stcSubs parStruct) ->
            let
              sf = stcSubs parStruct Map.! label
              newSF = sf{ssfField = newSub}
              newStruct = parStruct{stcSubs = Map.insert label newSF (stcSubs parStruct)}
             in
              return (ValCursor (substTN (TNStruct newStruct) parT) cs)
        | otherwise -> case label of
            PatternSelector i ->
              let
                psf = stcPatterns parStruct !! i
                newPSF = psf{psfValue = newSub}
                newStruct =
                  parStruct
                    { stcPatterns = take i (stcPatterns parStruct) ++ [newPSF] ++ drop (i + 1) (stcPatterns parStruct)
                    }
               in
                return (ValCursor (substTN (TNStruct newStruct) parT) cs)
            PendingSelector i ->
              let
                psf = stcPendSubs parStruct !! i
                newPSF = modifyPSEValue (const newSub) psf
                newStruct =
                  parStruct
                    { stcPendSubs =
                        take i (stcPendSubs parStruct) ++ [newPSF] ++ drop (i + 1) (stcPendSubs parStruct)
                    }
               in
                return (ValCursor (substTN (TNStruct newStruct) parT) cs)
            _ -> throwError insertErrMsg
    _ -> throwError insertErrMsg

  insertErrMsg :: String
  insertErrMsg =
    printf
      "propValUp: cannot insert child %s to parent %s, path: %s, selector: %s, child:\n%s\nparent:\n%s"
      (showTreeSymbol subT)
      (showTreeSymbol parT)
      (show $ tcPath tc)
      (show sel)
      (show subT)
      (show parT)

propUpTCUntil :: (CommonEnv m) => Selector -> TreeCursor -> m TreeCursor
propUpTCUntil _ (ValCursor _ []) = throwError "propUpTCUntil: already at the top"
propUpTCUntil sel tc@(ValCursor _ ((s, _) : _)) = do
  if s == sel
    then return tc
    else propValUp tc >>= propUpTCUntil sel

data Context = Context
  { ctxCrumbs :: [TreeCrumb]
  , ctxNotifiers :: Map.Map Path [Path]
  , ctxVisiting :: Set.Set Path
  , -- The tuple is the absolute path of the start of the cycle and the cycle tail relative path.
    ctxCycle :: Maybe (Path, Path)
  }
  deriving (Eq, Show)

addCtxNotifier :: (Path, Path) -> Context -> Context
addCtxNotifier (src, dep) ctx = ctx{ctxNotifiers = new}
 where
  old = ctxNotifiers ctx
  new = case Map.lookup src old of
    Nothing -> Map.insert src [dep] old
    Just ps -> Map.insert src (dep : ps) old

ctxPath :: Context -> Path
ctxPath = pathFromCrumbs . ctxCrumbs

emptyContext :: Context
emptyContext =
  Context
    { ctxCrumbs = []
    , ctxNotifiers = Map.empty
    , ctxVisiting = Set.empty
    , ctxCycle = Nothing
    }

data CtxVal a = CtxVal
  { cvVal :: a
  , cvCtx :: Context
  }

type CtxTree = CtxVal Tree

class HasCtxVal s a | s -> a where
  getCtxVal :: s -> CtxVal a
  setCtxVal :: s -> CtxVal a -> s

instance Functor CtxVal where
  fmap f c = c{cvVal = f (cvVal c)}

instance HasCtxVal (CtxVal a) a where
  getCtxVal = id
  setCtxVal _ x = x

instance (Show a) => Show (CtxVal a) where
  show a = printf "CtxVal, val: %s, ctx: %s" (show $ cvVal a) (show $ cvCtx a)

mkCVFromCur :: ValCursor a -> CtxVal a
mkCVFromCur cur =
  CtxVal
    { cvVal = vcFocus cur
    , cvCtx =
        Context
          { ctxCrumbs = vcCrumbs cur
          , ctxNotifiers = Map.empty
          , ctxVisiting = Set.empty
          , ctxCycle = Nothing
          }
    }

cvPath :: CtxVal a -> Path
cvPath = ctxPath . cvCtx

getCVCursor :: CtxVal a -> ValCursor a
getCVCursor cv = ValCursor (cvVal cv) (ctxCrumbs . cvCtx $ cv)

type TreeMonad s m = (CommonEnv m, MonadState s m, HasCtxVal s Tree)

getTMCursor :: (TreeMonad s m) => m TreeCursor
getTMCursor = gets (getCVCursor . getCtxVal)

getTMAbsPath :: (TreeMonad s m) => m Path
getTMAbsPath = gets (cvPath . getCtxVal)

getTMCrumbs :: (TreeMonad s m) => m [TreeCrumb]
getTMCrumbs = ctxCrumbs <$> getTMContext

putTMCrumbs :: (TreeMonad s m) => [TreeCrumb] -> m ()
putTMCrumbs crumbs = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvCtx = ctx{ctxCrumbs = crumbs}})

putTMCursor :: (TreeMonad s m) => TreeCursor -> m ()
putTMCursor tc = putTMCrumbs (vcCrumbs tc) >> putTMTree (vcFocus tc)

getTMContext :: (TreeMonad s m) => m Context
getTMContext = gets (cvCtx . getCtxVal)

putTMContext :: (TreeMonad s m) => Context -> m ()
putTMContext ctx = modify $ \s ->
  let ct = getCtxVal s
   in setCtxVal s (ct{cvCtx = ctx})

propUpTMSel :: (TreeMonad s m) => Selector -> m ()
propUpTMSel sel = getTMCursor >>= go >>= putTMCursor
 where
  go :: (CommonEnv m) => TreeCursor -> m TreeCursor
  go (ValCursor _ []) = throwError "propUpTMSel: already at the top"
  go tc@(ValCursor _ ((s, _) : _)) = do
    -- dump $ printf "propUpTMSel: sel: %s" (show s)
    if s == sel
      then propValUp tc
      else propValUp tc >>= go

propUpTMUntilSel :: (TreeMonad s m) => Selector -> m ()
propUpTMUntilSel sel = getTMCursor >>= propUpTCUntil sel >>= putTMCursor

propUpTM :: (TreeMonad s m) => m ()
propUpTM = getTMCursor >>= propValUp >>= putTMCursor

withTree :: (TreeMonad s m) => (Tree -> m a) -> m a
withTree f = getTMTree >>= f

withTN :: (TreeMonad s m) => (TreeNode -> m a) -> m a
withTN f = withTree (f . treeNode)

withContext :: (TreeMonad s m) => (Context -> m a) -> m a
withContext f = getTMContext >>= f

withCtxTree :: (TreeMonad s m) => (CtxTree -> m a) -> m a
withCtxTree f = gets getCtxVal >>= f

withDumpInfo :: (TreeMonad s m) => (Path -> Tree -> m a) -> m a
withDumpInfo f = do
  path <- getTMAbsPath
  withTree (f path)

putTMTree :: (TreeMonad s m) => Tree -> m ()
putTMTree t = modify $ \s -> setCtxVal s (t <$ getCtxVal s)

getTMTree :: (TreeMonad s m) => m Tree
getTMTree = gets (cvVal . getCtxVal)

pushTMSub :: (TreeMonad s m) => Selector -> Tree -> m ()
pushTMSub sel tip = do
  t <- getTMTree
  crumbs <- getTMCrumbs
  putTMCrumbs ((sel, t) : crumbs)
  putTMTree tip

inSubTM :: (TreeMonad s m) => Selector -> Tree -> m a -> m a
inSubTM sel t f = do
  pushTMSub sel t
  r <- f
  propUpTMSel sel
  return r

inAbsRemoteTM :: (TreeMonad s m) => Path -> m a -> m a
inAbsRemoteTM p f = do
  inAbsRemoteTMMaybe p (Just <$> f) >>= maybe (throwError "inAbsRemoteTM: path does not exist") return

-- | Go to the absolute path in the tree and execute the action. The path must exist.
inAbsRemoteTMMaybe :: (TreeMonad s m) => Path -> m (Maybe a) -> m (Maybe a)
inAbsRemoteTMMaybe p f = do
  origAbsPath <- getTMAbsPath

  tarM <- whenM (goTMAbsPath p) f
  backM <- goTMAbsPath origAbsPath
  unless backM $ throwError "inAbsRemoteTMMaybe: failed to go back to the original path"
  return tarM
 where
  whenM :: (TreeMonad s m) => m Bool -> m (Maybe a) -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then g else return Nothing

-- | Go to the absolute path in the tree. The path must exist.
goTMAbsPath :: (TreeMonad s m) => Path -> m Bool
goTMAbsPath dst = do
  when (headSel dst /= Just Path.RootSelector) $
    throwError (printf "goTMAbsPath: the path %s should start with the root selector" (show dst))
  propUpTMUntilSel Path.RootSelector
  let dstNoRoot = fromJust $ tailPath dst
  descendTM dstNoRoot

-- Locate the node in the lowest ancestor tree by specified path. The path must start with a locatable var.
goLowestAncPathTM :: (TreeMonad s m) => Path -> m (Maybe a) -> m (Maybe a)
goLowestAncPathTM dst f = do
  when (isPathEmpty dst) $ throwError "locate: empty path"
  let fstSel = fromJust $ headSel dst
  tc <- getTMCursor
  varTC <-
    maybeM
      (throwError $ printf "reference %s is not found" (show fstSel))
      return
      (searchTCVar fstSel tc)

  -- var must be found.
  putTMCursor varTC
  -- the selectors may not exist. And if the selectors exist, the value may not exist.
  whenJust (tailPath dst) $ \selPath -> do
    r <- descendTM selPath
    if r then f else return Nothing

descendTM :: (TreeMonad s m) => Path -> m Bool
descendTM dst = do
  tc <- getTMCursor
  maybe
    (return False)
    (\r -> putTMCursor r >> return True)
    (goDownTCPath dst tc)

discardTMAndPut :: (TreeMonad s m) => Tree -> m ()
discardTMAndPut t = modify $ \s ->
  let ct = getCtxVal s
      ctx = cvCtx ct
   in setCtxVal s (ct{cvVal = t, cvCtx = ctx{ctxCrumbs = tail (ctxCrumbs ctx)}})

discardTMAndPop :: (TreeMonad s m) => m ()
discardTMAndPop = do
  ctx <- getTMContext
  let
    crumbs = ctxCrumbs ctx
    t = head crumbs
  putTMContext ctx{ctxCrumbs = tail crumbs}
  putTMTree (snd t)

eliminateTMCycle :: (TreeMonad s m) => m ()
eliminateTMCycle = do
  ctx <- getTMContext
  putTMContext ctx{ctxCycle = Nothing}

dumpEntireTree :: (TreeMonad s m) => String -> m ()
dumpEntireTree msg = do
  Config{cfMermaid = mermaid} <- ask
  when mermaid $ do
    withTN $ \case
      TNAtom _ -> return ()
      TNBottom _ -> return ()
      TNTop -> return ()
      _ -> do
        tc <- getTMCursor
        rtc <- propUpTCUntil Path.RootSelector tc
        let
          t = vcFocus rtc
          evalPath = pathFromCrumbs (vcCrumbs tc)
          s = evalState (treeToMermaid msg evalPath t) 0
        dump $ printf "entire tree:\n```mermaid\n%s\n```" s

whenStruct :: (TreeMonad s m) => a -> (Struct -> m a) -> m a
whenStruct a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    TNStruct struct -> f struct
    _ -> do
      putTMTree $ mkBottomTree "not a struct"
      return a

whenNotBottom :: (TreeMonad s m) => a -> m a -> m a
whenNotBottom a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    _ -> f

subNodes :: Tree -> [(Selector, Tree)]
subNodes t = case treeNode t of
  TNStruct struct -> [(StructSelector s, ssfField sf) | (s, sf) <- Map.toList (stcSubs struct)]
  TNList l -> [(IndexSelector i, v) | (i, v) <- zip [0 ..] (lstSubs l)]
  -- TODO: do we need this?
  TNFunc fn -> [(FuncSelector $ FuncArgSelector i, v) | (i, v) <- zip [0 ..] (fncArgs fn)]
  TNDisj d ->
    maybe [] (\x -> [(DisjDefaultSelector, x)]) (dsjDefault d)
      ++ [(DisjDisjunctSelector i, v) | (i, v) <- zip [0 ..] (dsjDisjuncts d)]
  _ -> []

-- | Traverse all the one-level sub nodes of the tree.
traverseSub :: forall s m. (TreeMonad s m) => m () -> m ()
traverseSub f = withTree $ \t -> mapM_ go (subNodes t)
 where
  go :: (TreeMonad s m) => (Selector, Tree) -> m ()
  go (sel, sub) = whenNotBottom () $ inSubTM sel sub f

{- | Traverse the leaves of the tree cursor in the following order
1. Traverse the current node.
2. Traverse the sub-tree with the selector.
-}
traverseTM :: forall s m. (TreeMonad s m) => m () -> m ()
traverseTM f = f >> traverseSub (traverseTM f)

setOrigNodes :: forall s m. (TreeMonad s m) => m ()
setOrigNodes = traverseTM $ withTree $ \t ->
  when (isNothing (treeOrig t)) $ putTMTree t{treeOrig = Just t}

-- Exhaust the tree by evaluating dereferenced functions.
exhaustTM :: (TreeMonad s m) => m ()
exhaustTM = do
  wasRef <- withTN $ \case
    TNFunc fn | isFuncRef fn -> return True
    _ -> return False
  evalTM
  withTN $ \case
    -- If previous node was a reference, and the current node has been evaluated to a new function, then we need to
    -- evaluate the new function.
    TNFunc fn | wasRef && not (isFuncRef fn) -> evalTM
    _ -> return ()

-- Evaluate the tree.
evalTM :: (TreeMonad s m) => m ()
evalTM = withTree $ \t -> do
  let cond = case treeNode t of
        TNFunc fn | isFuncRef fn -> True
        _ -> True
  parHasCycle <- isJust . ctxCycle <$> getTMContext
  withDumpInfo $ \path _ ->
    dump $ printf "evalTM: path: %s, cond: %s, parHasCycle: %s" (show path) (show cond) (show parHasCycle)
  when (cond && not parHasCycle) forceEvalCV

forceEvalCV :: (TreeMonad s m) => m ()
forceEvalCV = do
  dumpEntireTree "evalTM start"

  origT <- getTMTree
  markTMVisiting
  withTree $ \t -> case treeNode t of
    TNFunc fn -> evalFunc fn
    TNStruct struct -> evalStruct struct
    TNList _ -> traverseSub evalTM
    TNDisj _ -> traverseSub evalTM
    _ -> return ()

  withTree $ \t -> do
    let nt = setOrig t origT
    putTMTree $ nt{treeEvaled = True}
  -- withDumpInfo $ \path _ ->
  --   dump $ printf "evalTM: path: %s, set evaled" (show path)
  unmarkTMVisiting

  ctx <- getTMContext
  path <- getTMAbsPath
  case ctxCycle ctx of
    Just (cycleStart, cycleTail) | cycleStart == path -> do
      dump $ printf "evalTM: path: %s, cycle head found" (show path)
      putTMTree $ mkRefCycleTree cycleTail origT
      putTMContext $ ctx{ctxCycle = Nothing}
    _ -> return ()

  withTree tryPopulateRef

  dump $ printf "evalTM: path: %s, done" (show path)
  dumpEntireTree "evalTM done"
 where
  markTMVisiting :: (TreeMonad s m) => m ()
  markTMVisiting = do
    path <- getTMAbsPath
    withCtxTree $ \ct -> do
      let
        ctx = cvCtx ct
        newCtx = ctx{ctxVisiting = Set.insert path (ctxVisiting ctx)}
      putTMContext newCtx

  unmarkTMVisiting :: (TreeMonad s m) => m ()
  unmarkTMVisiting = do
    path <- getTMAbsPath
    withCtxTree $ \ct -> do
      let
        ctx = cvCtx ct
        newCtx = ctx{ctxVisiting = Set.delete path (ctxVisiting ctx)}
      putTMContext newCtx

tryPopulateRef :: (TreeMonad s m) => Tree -> m ()
tryPopulateRef nt = do
  withCtxTree $ \ct -> do
    let
      resPath = cvPath ct
      notifers = ctxNotifiers . cvCtx $ ct
      deps = fromMaybe [] (Map.lookup resPath notifers)
    withDumpInfo $ \path _ ->
      unless (null deps) $
        dump $
          printf "evalTM: path: %s, using value to update %s" (show path) (show deps)
    mapM_ (\dep -> inAbsRemoteTM dep (populateRef nt)) deps

{- | Substitute the cached result of the Func node pointed by the path with the new value. Then trigger the re-evluation
of the lowest ancestor Func.
-}
populateRef :: (TreeMonad s m) => Tree -> m ()
populateRef nt = do
  withDumpInfo $ \path _ ->
    dump $ printf "populateRef: path: %s, new value: %s" (show path) (show nt)
  withTree $ \tar -> case (treeNode tar, treeNode nt) of
    -- If the new value is a function, just skip the re-evaluation.
    (TNFunc _, TNFunc _) -> return ()
    (TNFunc fn, _) -> do
      unless (isFuncRef fn) $
        throwError $
          printf "populateRef: the target node %s is not a reference." (show tar)

      reduceFunc fn nt
      withDumpInfo $ \path v ->
        dump $ printf "populateRef: path: %s, updated value: %s" (show path) (show v)
    _ -> throwError $ printf "populateRef: the target node %s is not a function." (show tar)

  locateLAFunc
  withTree $ \t -> case treeNode t of
    TNFunc fn
      | isFuncRef fn -> do
          -- If it is a reference, the re-evaluation can be skipped because
          -- 1. The highest function is actually itself.
          -- 2. Re-evaluating the reference would get the same value.
          withDumpInfo $ \path _ ->
            dump $
              printf
                "populateRef: lowest ancestor function is a reference, skip re-evaluation. path: %s, node: %s"
                (show path)
                (show t)
          tryPopulateRef nt
      -- re-evaluate the highest function when it is not a reference.
      | otherwise -> do
          withDumpInfo $ \path _ ->
            dump $ printf "populateRef: re-evaluating the lowest ancestor function, path: %s, node: %s" (show path) (show t)
          r <- evalFunc fn >> getTMTree
          tryPopulateRef r
    _ -> throwError "populateRef: the target node is not a function"

-- Locate the lowest ancestor node of type regular function.
locateLAFunc :: (TreeMonad s m) => m ()
locateLAFunc = do
  path <- getTMAbsPath
  if hasEmptyPath path || not (hasFuncSel path)
    then return ()
    else propUpTM >> locateLAFunc
 where
  hasEmptyPath (Path.Path sels) = null sels
  hasFuncSel (Path.Path sels) =
    any
      ( \case
          (FuncSelector (FuncArgSelector _)) -> True
          _ -> False
      )
      sels

{- | Search the tree cursor up to the root and return the tree cursor that points to the variable.
The cursor will also be propagated to the parent block.
-}
searchTCVar :: (CommonEnv m) => Selector -> TreeCursor -> m (Maybe TreeCursor)
searchTCVar sel@(StructSelector ssel@(StringSelector _)) tc = case treeNode (vcFocus tc) of
  TNStruct struct
    | Just (sf, True) <-
        ( do
            sf <- Map.lookup ssel (stcSubs struct)
            return (sf, lbAttrIsVar (ssfAttr sf))
        ) ->
        return . Just $ mkSubTC sel (ssfField sf) tc
  _ -> goUp tc
 where
  goUp :: (CommonEnv m) => TreeCursor -> m (Maybe TreeCursor)
  goUp (ValCursor _ [(RootSelector, _)]) = return Nothing
  goUp utc = propValUp utc >>= searchTCVar sel
searchTCVar _ _ = return Nothing

maybeM :: (Monad m) => m b -> (a -> m b) -> m (Maybe a) -> m b
maybeM b f m = do
  ma <- m
  maybe b f ma

whenJust :: (Monad m) => Maybe a -> (a -> m (Maybe b)) -> m (Maybe b)
whenJust m = whenJustM (return m)

whenJustM :: (Monad m) => m (Maybe a) -> (a -> m (Maybe b)) -> m (Maybe b)
whenJustM m f = do
  ma <- m
  maybe (return Nothing) f ma
