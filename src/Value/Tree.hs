{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Tree (
  module Value.Atom,
  module Value.Bottom,
  module Value.Bounds,
  module Value.Constraint,
  module Value.Cycle,
  module Value.Disj,
  module Value.List,
  module Value.Struct,
  module Value.Tree,
  module Value.TreeNode,
  module Value.Mutable,
)
where

import qualified AST
import Class
import Config
import Control.Monad (foldM, when)
import Control.Monad.Reader (MonadReader, ask)
import Control.Monad.State.Strict (MonadState, evalState)
import Cursor
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import Env
import Error
import GHC.Stack (HasCallStack)
import Path
import TMonad
import Text.Printf (printf)
import Util
import Value.Atom
import Value.Bottom
import Value.Bounds
import Value.Constraint
import Value.Cycle
import Value.Disj
import Value.List
import Value.Mutable
import Value.Struct
import Value.TreeNode

class TreeRepBuilderIter a where
  iterRepTree :: a -> TreeRep

-- TreeMonad stores the tree structure in its state.
type TreeMonad s m =
  ( Env m
  , MonadState s m
  , HasCtxVal s Tree Tree
  , HasTrace s
  , MonadReader (Config Tree) m
  , HasCallStack
  )

-- Some rules:
-- 1. If a node is a Mutable that contains references, then the node should not be supplanted to other places without
-- changing the dependencies.
-- 2. Evaluation is top-down. Evaluation do not go deeper unless necessary.
data Tree = Tree
  { treeNode :: TreeNode Tree
  , treeOrig :: Maybe AST.Expression
  , treeTemp :: Maybe Tree
  -- ^ treeTemp is used to store the temporary tree node that is created during the evaluation process.
  }

data TreeRep = TreeRep
  { trSymbol :: String
  , trMeta :: String
  , trFields :: [TreeRepField]
  , trMetas :: [TreeRepMeta]
  }

data TreeRepField = TreeRepField
  { trfLabel :: String
  , trfAttr :: String
  , trfValue :: Tree
  }

data TreeRepMeta = TreeRepMeta
  { trmLabel :: String
  , trmAttr :: String
  }

instance HasTreeNode Tree where
  getTreeNode = treeNode
  setTreeNode = setTN

instance TreeOp Tree where
  subTree sel t = case sel of
    TempSelector -> treeTemp t
    _ -> subTreeTN sel t
  setSubTree sel sub t = case sel of
    TempSelector -> return $ t{treeTemp = Just sub}
    _ -> setSubTreeTN sel sub t

  getVarField = getVarFieldTN
  delTemp t = t{treeTemp = Nothing}
  isTreeAtom = isJust . getAtomVFromTree
  isTreeBottom = isJust . getBottomFromTree
  isTreeCnstr = isJust . getCnstrFromTree
  isTreeRefCycle = isJust . getRefCycleFromTree
  isTreeMutable = isJust . getMutableFromTree
  isTreeValue t = case treeNode t of
    TNRefCycle _ -> False
    TNMutable _ -> False
    _ -> True
  treeHasRef t = case treeNode t of
    TNMutable fn -> mutHasRef fn
    _ -> False
  treeHasAtom t = case treeNode t of
    TNAtom _ -> True
    TNConstraint _ -> True
    TNDisj dj -> maybe False treeHasAtom (dsjDefault dj)
    _ -> False

instance TreeRepBuilder Tree where
  repTree = treeToSimpleStr

instance TreeRepBuilderIter Tree where
  iterRepTree t =
    let trf = buildRepTreeTN t (treeNode t)
     in trf{trFields = trFields trf ++ maybe [] (\x -> [TreeRepField (show TempSelector) "" x]) (treeTemp t)}

buildRepTreeTN :: Tree -> TreeNode Tree -> TreeRep
buildRepTreeTN t tn = case tn of
  TNAtom leaf -> consRep (mempty, show (amvAtom leaf), [], [])
  -- TODO: selector
  TNBounds b ->
    consRep
      ( mempty
      , show b
      , []
      , consMetas $ zipWith (\j v -> (show (j :: Int), repTree 0 v)) [0 ..] (bdsList b)
      )
  TNStruct s ->
    let ordLabels = printf "ord:[%s]" $ intercalate ", " (map show $ stcOrdLabels s)
        attr :: LabelAttr -> String
        attr a = case lbAttrCnstr a of
          SFCRegular -> mempty
          SFCRequired -> "!"
          SFCOptional -> "?"

        isVar :: LabelAttr -> String
        isVar a =
          if lbAttrIsVar a
            then ",v"
            else mempty

        slabelAttr :: StructSelector -> String
        slabelAttr k =
          let sf = stcSubs s Map.! k
           in attr (ssfAttr sf) <> isVar (ssfAttr sf)

        dlabelAttr :: DynamicStructField Tree -> String
        dlabelAttr dsf = attr (dsfAttr dsf) <> isVar (dsfAttr dsf) <> ",e,dynpend"

        plabelAttr :: String
        plabelAttr = ",e,patpend"

        fields :: [(String, String, Tree)]
        fields =
          map (\k -> (show k, slabelAttr k, ssfField $ stcSubs s Map.! k)) (structStaticLabels s)
            ++ zipWith
              ( \j k -> (show (StructSelector $ PatternSelector j), "", psfValue k)
              )
              [0 ..]
              (stcPatterns s)
            ++ map
              ( \j ->
                  let a = stcPendSubs s !! j
                   in case a of
                        DynamicField dsf -> (show (StructSelector $ PendingSelector j), dlabelAttr dsf, dsfValue dsf)
                        PatternField _ val -> (show (StructSelector $ PendingSelector j), plabelAttr, val)
              )
              (structPendIndexes s)

        metas :: [(String, String)]
        metas =
          zipWith
            (\j psf -> (show (StructSelector $ PatternSelector j), show (psfPattern psf)))
            [0 ..]
            (stcPatterns s)
     in consRep ((if stcClosed s then "#" else mempty) <> symbol, ordLabels, consFields fields, consMetas metas)
  TNList vs ->
    let fields = zipWith (\j v -> (show (IndexSelector j), mempty, v)) [0 ..] (lstSubs vs)
     in consRep (symbol, mempty, consFields fields, [])
  TNDisj d ->
    let dfField = maybe [] (\v -> [(show DisjDefaultSelector, mempty, v)]) (dsjDefault d)
        djFields = zipWith (\j v -> (show $ DisjDisjunctSelector j, mempty, v)) [0 ..] (dsjDisjuncts d)
     in consRep (symbol, mempty, consFields dfField ++ consFields djFields, [])
  TNConstraint c ->
    consRep
      ( symbol
      , mempty
      , consFields
          [ ("atom", mempty, mkAtomVTree (cnsAtom c))
          , ("validator", mempty, mkAtomTree $ String (show $ cnsValidator c))
          ]
      , []
      )
  TNRefCycle c -> case c of
    RefCycleVert -> consRep (symbol, "vert", [], [])
    RefCycleVertMerger p -> consRep (symbol, "vert-merger: " ++ show p, [], [])
    RefCycleHori p -> consRep (symbol, "hori " ++ show p, [], [])
  TNMutable m -> case m of
    Mut mut ->
      let
        args = zipWith (\j v -> (show (MutableArgSelector j), mempty, v)) [0 ..] (mutArgs mut)
        val = maybe mempty (\s -> [(show MutableValSelector, mempty, s)]) (mutValue mut)
       in
        consRep
          ( symbol
          , mutName mut
              <> ( printf ", args:%s" (show . length $ mutArgs mut)
                    <> (if mutHasRef m then ", hasRef" else mempty)
                 )
          , consFields (args ++ val)
          , []
          )
    Ref ref ->
      let
        val = maybe mempty (\s -> [(show MutableValSelector, mempty, s)]) (refValue ref)
       in
        consRep (symbol, show $ refPath ref, consFields val, [])
  TNBottom b -> consRep (symbol, show b, [], [])
  TNTop -> consRep (symbol, mempty, [], [])
 where
  symbol :: String
  symbol = showTreeSymbol t

  consRep :: (String, String, [TreeRepField], [TreeRepMeta]) -> TreeRep
  consRep (s, m, f, l) = TreeRep s m f l

  consFields :: [(String, String, Tree)] -> [TreeRepField]
  consFields = map (\(l, a, v) -> TreeRepField l a v)

  consMetas :: [(String, String)] -> [TreeRepMeta]
  consMetas = map (\(l, a) -> TreeRepMeta l a)

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
    TNMutable mut -> case mut of
      Mut _ -> buildASTExpr cr mut
      Ref _ -> maybe (throwErrSt "expression not found for reference") return (treeOrig t)
    TNConstraint c -> maybe (return $ cnsValidator c) return (treeOrig t)
    TNRefCycle c -> case c of
      RefCycleHori _ -> return $ AST.litCons AST.TopLit
      RefCycleVert -> maybe (throwErrSt "RefCycle: original expression not found") return (treeOrig t)
      RefCycleVertMerger _ -> throwErrSt "RefCycleVert should not be used in the AST"

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

treeToSimpleStr :: Int -> Tree -> String
treeToSimpleStr toff t =
  let TreeRep symbol meta fields listedMetas = iterRepTree t
   in "("
        <> (if null symbol then meta else symbol <> " " <> meta)
        <> ( if null fields
              then mempty
              else
                -- we need to add a newline for the fields block.
                "\n"
                  <> foldl
                    ( \acc (TreeRepField label attr sub) ->
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
                    ( \acc (TreeRepMeta label lmeta) ->
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
  subgraph toff t treeID = do
    let
      (TreeRep symbol meta subReps _) = iterRepTree t
      writeLine :: String -> String
      writeLine content = indent toff <> content <> "\n"
      curTreeRepStr =
        writeLine
          ( printf
              "%s[\"`%s`\"]"
              treeID
              $ escape
                ( symbol
                    <> (if null meta then mempty else " " <> meta)
                    -- print whether the node has an original expression.
                    -- Currently disabled.
                    <> printf ", %s" (if isJust $ treeOrig t then "Y" else "N")
                )
          )

    foldM
      ( \acc (TreeRepField label _ sub) -> do
          let subTreeID = treeID ++ "_" ++ label
          rest <- subgraph (toff + 2) sub subTreeID
          return $
            acc
              <> writeLine (printf "%s -->|%s| %s" treeID label subTreeID)
              <> rest
      )
      curTreeRepStr
      subReps

  escape :: String -> String
  escape = concatMap $ \case
    '"' -> "#quot;"
    c -> [c]

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNAtom _ -> ""
  TNBounds _ -> "b"
  TNStruct{} -> "{}"
  TNList{} -> "[]"
  TNDisj{} -> "dj"
  TNConstraint{} -> "Cnstr"
  TNRefCycle _ -> "RC"
  TNMutable m -> case m of
    Mut _ -> "fn"
    Ref _ -> "ref"
  TNBottom _ -> "_|_"
  TNTop -> "_"

subNodes :: Tree -> [(Selector, Tree)]
subNodes t = case treeNode t of
  TNStruct struct -> [(StructSelector s, ssfField sf) | (s, sf) <- Map.toList (stcSubs struct)]
  TNList l -> [(IndexSelector i, v) | (i, v) <- zip [0 ..] (lstSubs l)]
  TNMutable (Mut mut) -> [(MutableSelector $ MutableArgSelector i, v) | (i, v) <- zip [0 ..] (mutArgs mut)]
  TNDisj d ->
    maybe [] (\x -> [(DisjDefaultSelector, x)]) (dsjDefault d)
      ++ [(DisjDisjunctSelector i, v) | (i, v) <- zip [0 ..] (dsjDisjuncts d)]
  _ -> []

mutHasRef :: Mutable Tree -> Bool
mutHasRef (Ref _) = True
mutHasRef (Mut mut) = argsHaveRef (mutArgs mut)
 where
  argsHaveRef :: [Tree] -> Bool
  argsHaveRef =
    any
      ( \x -> case treeNode x of
          TNMutable subFn -> mutHasRef subFn
          _ -> False
      )

-- Helpers

setTN :: Tree -> TreeNode Tree -> Tree
setTN t n = t{treeNode = n}

setOrig :: Tree -> Maybe AST.Expression -> Tree
setOrig t eM = t{treeOrig = eM}

getAtomVFromTree :: Tree -> Maybe AtomV
getAtomVFromTree t = case treeNode t of
  TNAtom a -> Just a
  _ -> Nothing

getBottomFromTree :: Tree -> Maybe Bottom
getBottomFromTree t = case treeNode t of
  TNBottom b -> Just b
  _ -> Nothing

getCnstrFromTree :: Tree -> Maybe (Constraint Tree)
getCnstrFromTree t = case treeNode t of
  TNConstraint c -> Just c
  _ -> Nothing

getRefCycleFromTree :: Tree -> Maybe RefCycle
getRefCycleFromTree t = case treeNode t of
  TNRefCycle c -> Just c
  _ -> Nothing

getMutableFromTree :: Tree -> Maybe (Mutable Tree)
getMutableFromTree t = case treeNode t of
  TNMutable f -> Just f
  _ -> Nothing

-- | Check if the node is a reducible ref cycle.
isTreeRefCycleTail :: Tree -> Bool
isTreeRefCycleTail t = case treeNode t of
  TNRefCycle (RefCycleVertMerger _) -> True
  -- TNRefCycle (RefCycleHori _) -> True
  _ -> False

mkNewTree :: TreeNode Tree -> Tree
mkNewTree n = Tree{treeNode = n, treeOrig = Nothing, treeTemp = Nothing}

mkAtomVTree :: AtomV -> Tree
mkAtomVTree v = mkNewTree (TNAtom v)

mkAtomTree :: Atom -> Tree
mkAtomTree a = mkAtomVTree (AtomV a)

mkBottomTree :: String -> Tree
mkBottomTree msg = mkNewTree (TNBottom $ Bottom{btmMsg = msg})

mkBoundsTree :: [Bound] -> Tree
mkBoundsTree bs = mkNewTree (TNBounds $ Bounds{bdsList = bs})

mkCnstrTree :: AtomV -> AST.Expression -> Tree
mkCnstrTree a e = mkNewTree . TNConstraint $ Constraint a a e

mkDisjTree :: Maybe Tree -> [Tree] -> Tree
mkDisjTree m js = mkNewTree (TNDisj $ Disj{dsjDefault = m, dsjDisjuncts = js})

mkMutableTree :: Mutable Tree -> Tree
mkMutableTree fn = mkNewTree (TNMutable fn)

mkListTree :: [Tree] -> Tree
mkListTree ts = mkNewTree (TNList $ List{lstSubs = ts})

mkStructTree :: Struct Tree -> Tree
mkStructTree s = mkNewTree (TNStruct s)

convRefCycleTree :: Tree -> Tree
convRefCycleTree t = setTN t (TNRefCycle RefCycleVert)

withTN :: (TreeMonad s m) => (TreeNode Tree -> m a) -> m a
withTN f = withTree (f . treeNode)

unlessTFBottom :: (TreeMonad s m) => a -> m a -> m a
unlessTFBottom a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    _ -> f

mustMutable :: (TreeMonad s m) => (Mutable Tree -> m a) -> m a
mustMutable f = withTree $ \t -> case treeNode t of
  TNMutable fn -> f fn
  _ -> throwErrSt $ printf "tree focus %s is not a mutator" (show t)

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

pathToTrees :: Path -> Maybe [Tree]
pathToTrees p = mapM selToTree (pathToList p)
 where
  selToTree :: Selector -> Maybe Tree
  selToTree sel = case sel of
    StructSelector (StringSelector s) -> Just $ mkAtomTree (String s)
    IndexSelector j -> Just $ mkAtomTree (Int (fromIntegral j))
    _ -> Nothing

-- | Traverse all the one-level sub nodes of the tree.
traverseSub :: forall s m. (TreeMonad s m) => m () -> m ()
traverseSub f = withTree $ \t -> mapM_ go (subNodes t)
 where
  go :: (TreeMonad s m) => (Selector, Tree) -> m ()
  go (sel, sub) = unlessTFBottom () $ inSubTM sel sub f

{- | Traverse the leaves of the tree cursor in the following order
1. Traverse the current node.
2. Traverse the sub-tree with the selector.
-}
traverseTM :: (TreeMonad s m) => m () -> m ()
traverseTM f = f >> traverseSub (traverseTM f)

{- | Traverse the tree and replace the Mutable node with the result of the mutator if it exists, otherwise the
original mutator node is kept.
-}
snapshotTM :: (TreeMonad s m) => m ()
snapshotTM =
  traverseTM $ withTN $ \case
    TNMutable m -> maybe (return ()) putTMTree (getMutVal m)
    _ -> return ()

dumpEntireTree :: (TreeMonad s m) => String -> m ()
dumpEntireTree msg = do
  withTN $ \case
    TNAtom _ -> return ()
    TNBottom _ -> return ()
    TNTop -> return ()
    _ -> do
      Config{cfMermaid = mermaid} <- ask
      when mermaid $ do
        logDebugStr "--- dump entire tree states: ---"
        notifiers <- ctxNotifiers <$> getTMContext
        logDebugStr $ printf "notifiers: %s" (show $ Map.toList notifiers)
        tc <- getTMCursor
        rtc <- propUpTCUntil Path.RootSelector tc

        let
          t = vcFocus rtc
          evalPath = pathFromCrumbs (vcCrumbs tc)
          s = evalState (treeToMermaid msg evalPath t) 0
        logDebugStr $ printf "\n```mermaid\n%s\n```" s

        logDebugStr "--- dump entire tree done ---"
