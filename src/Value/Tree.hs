{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}

module Value.Tree (
  module Value.Atom,
  module Value.Bottom,
  module Value.Bounds,
  module Value.Class,
  module Value.Constraint,
  module Value.Cursor,
  module Value.Cycle,
  module Value.Disj,
  module Value.Func,
  module Value.List,
  module Value.Struct,
  module Value.TMonad,
  module Value.Tree,
  module Value.Util,
)
where

import qualified AST
import Control.Monad (foldM, unless, when)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict (
  MonadState,
 )
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing)
import qualified Data.Set as Set
import Path
import Text.Printf (printf)
import Value.Atom
import Value.Bottom
import Value.Bounds
import Value.Class
import Value.Constraint
import Value.Cursor
import Value.Cycle
import Value.Disj
import Value.Env
import Value.Func
import Value.List
import Value.Struct
import Value.TMonad
import Value.Util

type TreeMonad s m = (CommonEnv m, MonadState s m, HasCtxVal s Tree Tree)

-- Some rules:
-- 1. If a node is a Func that contains references, then the node should not be supplanted to other places without
-- changing the dependencies.
-- 2. Evaluation is top-down. Evaluation do not go deeper unless necessary.
data Tree = Tree
  { treeNode :: TreeNode
  , treeOrig :: Maybe Tree
  , treeEvaled :: Bool
  }

-- | TreeNode represents a tree structure that contains values.
data TreeNode
  = -- | TNStruct is a struct that contains a value and a map of selectors to Tree.
    TNStruct (Struct Tree)
  | TNList (List Tree)
  | TNDisj (Disj Tree)
  | --  TNAtom contains an atom value.
    TNAtom AtomV
  | TNBounds Bounds
  | TNConstraint (Constraint Tree)
  | TNRefCycle RefCycle
  | TNFunc (Func Tree)
  | TNTop
  | TNBottom Bottom

--

instance TreeC Tree where
  goTreeSel = _goTreeSel
  setSubTree = _setSubTree
  getVarField = _getVarField

-- step down the tree with the given selector.
-- This should only be used by TreeCursor.
_goTreeSel :: Selector -> Tree -> Maybe Tree
_goTreeSel sel t =
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
    (_, TNDisj d)
      | DisjDefaultSelector <- sel -> dsjDefault d
      | DisjDisjunctSelector i <- sel -> dsjDisjuncts d `indexList` i
      -- This has to be the last case because the explicit disjunct selector has the highest priority.
      | otherwise -> dsjDefault d >>= _goTreeSel sel
    (_, TNConstraint c) | sel == unaryOpSelector -> Just (cnsValidator c)
    _ -> Nothing
 where
  indexList :: [a] -> Int -> Maybe a
  indexList xs i = if i < length xs then Just (xs !! i) else Nothing

_setSubTree :: (Env m c) => Selector -> Tree -> Tree -> m Tree
_setSubTree sel subT _parT = do
  n <- prop _parT
  return $ substTN n _parT
 where
  prop :: (Env m c) => Tree -> m TreeNode
  prop parT = case (sel, treeNode parT) of
    (StructSelector s, TNStruct _) -> updateParStruct parT s subT
    (IndexSelector i, TNList vs) ->
      let subs = lstSubs vs
          l = TNList $ vs{lstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return l
    (FuncSelector f, TNFunc fn) -> case f of
      FuncArgSelector i -> do
        let
          args = fncArgs fn
          l = TNFunc $ fn{fncArgs = take i args ++ [subT] ++ drop (i + 1) args}
        return l
      FuncResSelector -> do
        let l = TNFunc $ fn{fncRes = Just subT}
        return l
    (_, TNDisj d)
      | DisjDefaultSelector <- sel -> return (TNDisj $ d{dsjDefault = dsjDefault d})
      | DisjDisjunctSelector i <- sel ->
          return (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)})
      -- If the selector is not a disjunction selector, then the sub value must have been the default disjunction
      -- value.
      | otherwise ->
          maybe
            (throwError "propValUp: default disjunction value not found for non-disjunction selector")
            ( \dft -> do
                updatedDftT <- _setSubTree sel subT dft
                return (TNDisj $ d{dsjDefault = Just updatedDftT})
            )
            (dsjDefault d)
    (FuncSelector _, TNConstraint c) ->
      return (TNConstraint $ c{cnsValidator = subT})
    (ParentSelector, _) -> throwError "propValUp: ParentSelector is not allowed"
    (RootSelector, _) -> throwError "propValUp: RootSelector is not allowed"
    _ -> throwError insertErrMsg

  updateParStruct :: (MonadError String m) => Tree -> StructSelector -> Tree -> m TreeNode
  updateParStruct par label newSub = case treeNode par of
    TNStruct parStruct ->
      if
        | b@(TNBottom _) <- treeNode newSub -> return b
        -- the label should already exist in the parent struct.
        | Map.member label (stcSubs parStruct) ->
            let
              sf = stcSubs parStruct Map.! label
              newSF = sf{ssfField = newSub}
              newStruct = parStruct{stcSubs = Map.insert label newSF (stcSubs parStruct)}
             in
              return (TNStruct newStruct)
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
                return (TNStruct newStruct)
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
                return (TNStruct newStruct)
            _ -> throwError insertErrMsg
    _ -> throwError insertErrMsg

  insertErrMsg :: String
  insertErrMsg =
    printf
      "propValUp: cannot insert child %s to parent %s, selector: %s, child:\n%s\nparent:\n%s"
      (showTreeSymbol subT)
      (showTreeSymbol _parT)
      (show sel)
      (show subT)
      (show _parT)

_getVarField :: StructSelector -> Tree -> Maybe Tree
_getVarField ssel (Tree{treeNode = (TNStruct struct)}) = do
  sf <- Map.lookup ssel (stcSubs struct)
  if lbAttrIsVar (ssfAttr sf)
    then Just (ssfField sf)
    else Nothing
_getVarField _ _ = Nothing

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

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

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

isTreeAtom :: Tree -> Bool
isTreeAtom t = case treeNode t of
  TNAtom _ -> True
  _ -> False

isTreeBottom :: Tree -> Bool
isTreeBottom t = case treeNode t of
  TNBottom _ -> True
  _ -> False

isTreeCnstr :: Tree -> Bool
isTreeCnstr t = case treeNode t of
  TNConstraint _ -> True
  _ -> False

isTreeRefCycle :: Tree -> Bool
isTreeRefCycle t = case treeNode t of
  TNRefCycle _ -> True
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

substTN :: TreeNode -> Tree -> Tree
substTN n t = t{treeNode = n}

setTN :: TreeNode -> Tree -> Tree
setTN n t = t{treeNode = n}

setOrig :: Tree -> Tree -> Tree
setOrig t o = t{treeOrig = Just o}

setTNOrig :: TreeNode -> Tree -> Tree
setTNOrig tn o = (mkNewTree tn){treeOrig = Just o}

mkNewTree :: TreeNode -> Tree
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

mkRefCycleTree :: Path -> Tree -> Tree
mkRefCycleTree p = setTN (TNRefCycle $ RefCycle p)

withTN :: (TreeMonad s m) => (TreeNode -> m a) -> m a
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
