{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Tree (
  module Value.Atom,
  module Value.Bottom,
  module Value.Bounds,
  module Value.Class,
  module Value.Constraint,
  module Value.Cursor,
  module Value.Cycle,
  module Value.Disj,
  module Value.List,
  module Value.Struct,
  module Value.TMonad,
  module Value.Tree,
  module Value.TreeNode,
  Func,
  fncName,
  fncType,
  fncArgs,
  fncExprGen,
  FuncType (..),
  isFuncRef,
  isFuncIndex,
  mkUnaryOp,
  mkBinaryOp,
  mkBinaryOpDir,
  mkStubFunc,
)
where

import qualified AST
import Control.Monad (foldM, when)
import Control.Monad.Except (throwError)
import Control.Monad.Reader (ask)
import Control.Monad.State.Strict (MonadState, evalState)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import Path
import Text.Printf (printf)
import Util
import Value.Atom
import Value.Bottom
import Value.Bounds
import Value.Class
import Value.Constraint
import Value.Cursor
import Value.Cycle
import Value.Disj
import Value.Func
import Value.List
import Value.Struct
import Value.TMonad
import Value.TreeNode

-- TreeMonad stores the tree structure in its state.
type TreeMonad s m = (CommonEnv m, MonadState s m, HasCtxVal s Tree Tree)

-- Some rules:
-- 1. If a node is a Func that contains references, then the node should not be supplanted to other places without
-- changing the dependencies.
-- 2. Evaluation is top-down. Evaluation do not go deeper unless necessary.
data Tree = Tree
  { treeNode :: TreeNode Tree
  , treeOrig :: Maybe Tree
  , treeEvaled :: Bool
  }

instance HasTreeNode Tree where
  getTreeNode = treeNode
  setTreeNode = setTN

instance TreeOp Tree where
  subTree = subTreeTN
  setSubTree = setSubTreeTN
  getVarField = getVarFieldTN
  isTreeAtom = isJust . getAtomVFromTree
  isTreeBottom = isJust . getBottomFromTree
  isTreeCnstr = isJust . getCnstrFromTree
  isTreeRefCycle = isJust . getRefCycleFromTree
  isTreeFunc = isJust . getFuncFromTree
  isTreeValue t = case treeNode t of
    TNRefCycle _ -> False
    TNFunc _ -> False
    _ -> True
  treeHasRef t = case treeNode t of
    TNFunc fn -> funcHasRef fn
    _ -> False
  treeHasAtom t = case treeNode t of
    TNAtom _ -> True
    TNConstraint _ -> True
    TNDisj dj -> maybe False treeHasAtom (dsjDefault dj)
    _ -> False

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

          dlabelAttr :: DynamicStructField Tree -> String
          dlabelAttr dsf = attr (dsfAttr dsf) <> isVar (dsfAttr dsf) <> ",e,dsf"

          plabelAttr :: String
          plabelAttr = "e,psf"

          psfLabelAttr :: PatternStructField Tree -> String
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
      RefCycleTail p -> (symbol, "tail " ++ show p, emptyTreeFields, [])
    TNFunc f -> case fncType f of
      RefFunc ->
        let
          res = maybe mempty (\s -> [("res", mempty, s)]) (fncTempRes f)
         in
          (symbol, fncName f, res, [])
      _ ->
        let
          args = map (\(j, v) -> (show (FuncArgSelector j), mempty, v)) (zip [0 ..] (fncArgs f))
          res = maybe mempty (\s -> [("res", mempty, s)]) (fncTempRes f)
         in
          ( symbol
          , fncName f
              <> ( printf ", args:%s" (show . length $ fncArgs f)
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
        if p
          -- If the path is empty, then it is a self-reference.
          then return $ AST.litCons AST.TopLit
          else buildASTExpr cr (fromJust $ treeOrig t)
      RefCycleTail _ -> throwError "RefCycleTail should have been converted to RefCycle"

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

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

funcHasRef :: Func Tree -> Bool
funcHasRef fn = isFuncRef fn || argsHaveRef (fncArgs fn)
 where
  argsHaveRef :: [Tree] -> Bool
  argsHaveRef =
    any
      ( \x -> case treeNode x of
          TNFunc subFn -> funcHasRef subFn
          _ -> False
      )

-- Helpers

setTN :: Tree -> TreeNode Tree -> Tree
setTN t n = t{treeNode = n}

setOrig :: Tree -> Tree -> Tree
setOrig t o = t{treeOrig = Just o}

setTNOrig :: TreeNode Tree -> Tree -> Tree
setTNOrig tn o = (mkNewTree tn){treeOrig = Just o}

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

getFuncFromTree :: Tree -> Maybe (Func Tree)
getFuncFromTree t = case treeNode t of
  TNFunc f -> Just f
  _ -> Nothing

isTreeRefCycleTail :: Tree -> Bool
isTreeRefCycleTail t = case treeNode t of
  TNRefCycle (RefCycleTail _) -> True
  _ -> False

mkNewTree :: TreeNode Tree -> Tree
mkNewTree n = Tree{treeNode = n, treeOrig = Nothing, treeEvaled = False}

mkAtomVTree :: AtomV -> Tree
mkAtomVTree v = mkNewTree (TNAtom v)

mkAtomTree :: Atom -> Tree
mkAtomTree a = mkAtomVTree (AtomV a)

mkBottomTree :: String -> Tree
mkBottomTree msg = mkNewTree (TNBottom $ Bottom{btmMsg = msg})

mkBoundsTree :: [Bound] -> Tree
mkBoundsTree bs = mkNewTree (TNBounds $ Bounds{bdsList = bs})

mkCnstrTree :: AtomV -> Tree -> Tree
mkCnstrTree a = setTNOrig (TNConstraint $ Constraint a (mkBottomTree "validator not initialized"))

mkDisjTree :: Maybe Tree -> [Tree] -> Tree
mkDisjTree m js = mkNewTree (TNDisj $ Disj{dsjDefault = m, dsjDisjuncts = js})

mkFuncTree :: Func Tree -> Tree
mkFuncTree fn = mkNewTree (TNFunc fn)

mkListTree :: [Tree] -> Tree
mkListTree ts = mkNewTree (TNList $ List{lstSubs = ts})

convRefCycleTree :: Tree -> Bool -> Tree
convRefCycleTree t p = setTN t (TNRefCycle $ RefCycle p)

withTN :: (TreeMonad s m) => (TreeNode Tree -> m a) -> m a
withTN f = withTree (f . treeNode)

whenStruct :: (TreeMonad s m) => a -> (Struct Tree -> m a) -> m a
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
  go (sel, sub) = whenNotBottom () $ inSubTM sel sub f

{- | Traverse the leaves of the tree cursor in the following order
1. Traverse the current node.
2. Traverse the sub-tree with the selector.
-}
traverseTM :: (TreeMonad s m) => m () -> m ()
traverseTM f = f >> traverseSub (traverseTM f)

{- | Traverse the tree and replace the function node with the result of the function if it exists, otherwise the
original function node is kept.
-}
snapshotTM :: (TreeMonad s m) => m ()
snapshotTM =
  traverseTM $ withTN $ \case
    TNFunc fn -> maybe (return ()) putTMTree (fncTempRes fn)
    _ -> return ()

{- | Call the function. It returns the result of the function.
 - This does not modify the tree, i.e. the function is not reduced.
 -
 - TODO: consider whether putting back the fn accidentally left the unwanted changes in Monad.
-}
callFunc :: (TreeMonad s m) => m (Maybe Tree)
callFunc = withTree $ \t -> case getFuncFromTree t of
  Just fn -> do
    let name = fncName fn
    dumpEntireTree ("callFunc " ++ name ++ " start")
    withDebugInfo $ \path _ ->
      logDebugStr $ printf "callFunc: path: %s, function %s, tip:\n%s" (show path) (show name) (show t)

    -- modified is not equivalent to reducible. For example, if the unification generates a new struct, it is not
    -- enough to replace the function with the new struct.
    modified <- fncFunc fn (fncArgs fn)

    res <- getTMTree
    withDebugInfo $ \path _ ->
      logDebugStr $
        printf
          "callFunc: path: %s, function %s, modified: %s, result:\n%s"
          (show path)
          (show name)
          (show modified)
          (show res)

    r <-
      if modified
        then case getFuncFromTree res of
          Just _ -> do
            -- recursively call the function until the result is not a function.
            -- the tip is already the res.
            callFunc
          Nothing -> do
            -- we need to restore the original tree with the new function result.
            putTMTree (mkFuncTree $ fn{fncTempRes = Just res})
            return (Just res)
        else return Nothing
    dumpEntireTree ("callFunc " ++ name ++ " done")
    return r
  Nothing -> throwError "callFunc: function not found"

-- Try to reduce the function by using the function result to replace the function node.
-- This should be called after the function is evaluated.
reduceFunc :: (TreeMonad s m) => Tree -> m Bool
reduceFunc val = withTree $ \t -> case getFuncFromTree t of
  Just fn ->
    if isTreeFunc val
      -- If the function returns another function, then the function is not reducible.
      then putTMTree val >> return False
      else do
        let
          -- the original function can not have references.
          hasNoRef = not (treeHasRef t)
          reducible = isTreeAtom val || isTreeBottom val || isTreeCnstr val || isTreeRefCycleTail val || hasNoRef
        withDebugInfo $ \path _ ->
          logDebugStr $
            printf
              "reduceFunc: func %s, path: %s, is reducible: %s, hasNoRef: %s, args: %s"
              (show $ fncName fn)
              (show path)
              (show reducible)
              (show hasNoRef)
              (show $ fncArgs fn)
        if reducible
          then do
            handleReduceRes val
            path <- getTMAbsPath
            -- we need to delete receiver starting with the path, not only is the path. For example, if the function is
            -- index and the first argument is a reference, then the first argument dependency should also be deleted.
            delNotifRecvs path
          -- restore the original function
          else putTMTree . mkFuncTree $ fn
        return reducible
  Nothing -> throwError "reduceFunc: focus is not a function"

dumpEntireTree :: (TreeMonad s m) => String -> m ()
dumpEntireTree msg = do
  logDebugStr "dump entire tree states:"
  notifiers <- ctxNotifiers <$> getTMContext
  logDebugStr $ printf "notifiers: %s" (show $ Map.toList notifiers)
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
        logDebugStr $ printf "\n```mermaid\n%s\n```" s
  logDebugStr "dump entire tree done ---"

{- | Convert the RefCycleTail to RefCycle if the path is the same as the cycle start path.
RefCycleTail is like Bottom.
-}
handleReduceRes :: (TreeMonad s m) => Tree -> m ()
handleReduceRes val = case treeNode val of
  TNRefCycle (RefCycleTail (cycleStartPath, _)) -> do
    path <- getTMAbsPath
    if cycleStartPath == path
      then do
        logDebugStr $ printf "handleRefCycle: path: %s, cycle head found" (show path)
        -- The ref cycle tree must record the original tree.
        withTree $ \t -> putTMTree $ convRefCycleTree t False
      else putTMTree val
  _ -> putTMTree val
