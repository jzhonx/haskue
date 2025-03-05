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
import Control.Monad (foldM)
import Control.Monad.State.Strict (MonadState)
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import Exception
import Path
import Text.Printf (printf)
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
  iterRepTree :: a -> TreeRepBuildOption -> TreeRep

-- Some rules:
-- 1. If a node is a Mutable that contains references, then the node should not be supplanted to other places without
-- changing the dependencies.
-- 2. Evaluation is top-down. Evaluation do not go deeper unless necessary.
data Tree = Tree
  { treeNode :: TreeNode Tree
  , treeExpr :: Maybe AST.Expression
  -- ^ treeExpr is the parsed expression.
  , treeNonCnstrExpr :: Maybe AST.Expression
  , -- If it is Nothing, then the tree has not been constrained.
    -- If it is Just, then the expression is the non-constraint expression of one of the values in the unification tree.
    treeTemp :: Maybe Tree
  -- ^ treeTemp is used to store the temporary tree node that is created during the evaluation process.
  , treeRecurClosed :: Bool
  -- ^ treeRecurClosed is used to indicate whether the sub-tree including itself is closed.
  }

newtype TreeRepBuildOption = TreeRepBuildOption {trboShowMutArgs :: Bool}

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
  subTree seg t = case seg of
    TempTASeg -> treeTemp t
    _ -> subTreeTN seg t
  setSubTree sel sub t = case sel of
    TempTASeg -> return $ t{treeTemp = Just sub}
    _ -> setSubTreeTN sel sub t

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
  iterRepTree t opt =
    let trf = buildRepTreeTN t (treeNode t) opt
     in trf
          { trMeta =
              ( if not $ isTreeAtom t
                  then
                    (if treeRecurClosed t then "t_#," else "")
                      ++ (if isJust (treeExpr t) then "" else "t_N,")
                  else []
              )
                ++ trMeta trf
          , trFields = trFields trf ++ maybe [] (\x -> [TreeRepField (show TempTASeg) "" x]) (treeTemp t)
          }

buildRepTreeTN :: Tree -> TreeNode Tree -> TreeRepBuildOption -> TreeRep
buildRepTreeTN t tn opt = case tn of
  TNAtom leaf -> consRep (mempty, show (amvAtom leaf), [], [])
  -- TODO: segment
  TNBounds b ->
    consRep
      ( mempty
      , show b
      , []
      , []
      -- , consMetas $ zipWith (\j v -> (show (j :: Int), repTree 0 v)) [0 ..] (bdsList b)
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

        slabelAttr :: Field Tree -> String
        slabelAttr sf = attr (ssfAttr sf) <> isVar (ssfAttr sf)

        dlabelAttr :: DynamicField Tree -> String
        dlabelAttr dsf = attr (dsfAttr dsf) <> isVar (dsfAttr dsf) <> ",dynf"

        -- The tuple is (field name, field meta, field value)
        fields :: [(String, String, Tree)]
        fields =
          map
            ( \k ->
                let sv = stcSubs s Map.! k
                 in case sv of
                      SField sf -> (show k, slabelAttr sf, ssfValue sf)
                      SLet lb -> (show k, printf ",let,r:%s" (show $ lbReferred lb), lbValue lb)
            )
            (structStrLabels s)
            ++ map
              ( \(j, k) -> (show (StructTASeg $ PatternTASeg j), ",v:" ++ escapedTreeSymbol (scsValue k), scsPattern k)
              )
              (IntMap.toList $ stcCnstrs s)
            ++ foldr
              ( \(j, dsf) acc ->
                  -- case a of
                  --   Just dsf ->
                  (show (StructTASeg $ PendingTASeg j), dlabelAttr dsf, dsfLabel dsf) : acc
                  -- _ -> (show (StructTASeg $ PendingTASeg j), ",pat_deleted", mkNewTree TNTop) : acc
              )
              []
              (IntMap.toList $ stcPendSubs s)

        metas :: [(String, String)]
        metas = []
     in consRep
          ( (if stcClosed s then "#" else mempty) <> symbol
          , ordLabels <> ", sid:" <> show (stcID s)
          , consFields fields
          , consMetas metas
          )
  TNList vs ->
    let fields = zipWith (\j v -> (show (IndexTASeg j), mempty, v)) [0 ..] (lstSubs vs)
     in consRep (symbol, mempty, consFields fields, [])
  TNDisj d ->
    let dfField = maybe [] (\v -> [(show DisjDefaultTASeg, mempty, v)]) (dsjDefault d)
        djFields = zipWith (\j v -> (show $ DisjDisjunctTASeg j, mempty, v)) [0 ..] (dsjDisjuncts d)
     in consRep (symbol, mempty, consFields dfField ++ consFields djFields, [])
  TNConstraint c ->
    consRep
      ( symbol
      , mempty
      , consFields
          [ ("atom", mempty, mkAtomVTree (cnsAtom c))
          -- , ("validator", mempty, mkAtomTree $ String (show $ cnsValidator c))
          ]
      , []
      )
  TNRefCycle c -> case c of
    RefCycleVert -> consRep (symbol, "vert", [], [])
    RefCycleVertMerger p -> consRep (symbol, "vert-merger: " ++ show p, [], [])
    RefCycleHori p -> consRep (symbol, "hori " ++ show p, [], [])
  TNStructuralCycle (StructuralCycle p) -> consRep (symbol, "inf: " ++ show p, [], [])
  TNMutable m -> case m of
    SFunc mut ->
      let
        args =
          if trboShowMutArgs opt
            then zipWith (\j v -> (show (MutableArgTASeg j), mempty, v)) [0 ..] (sfnArgs mut)
            else []
        val = maybe mempty (\s -> [(show MutableValTASeg, mempty, s)]) (sfnValue mut)
       in
        consRep
          ( symbol
          , sfnName mut
              <> ( printf ", args:%s" (show . length $ sfnArgs mut)
                    <> (if mutHasRef m then ", hasRef" else mempty)
                 )
          , consFields (args ++ val)
          , []
          )
    Ref ref ->
      let
        val = maybe mempty (\s -> [(show MutableValTASeg, mempty, s)]) (refValue ref)
       in
        consRep
          ( symbol
          , show (refPath ref)
              <> maybe
                mempty
                (\from -> ", from:" <> show from)
                (refOrigAddrs ref)
          , -- <> printf ", E:%s" (if isJust $ refExpr ref then "Y" else "N")
            consFields val
          , []
          )
    Index idx ->
      let
        args = zipWith (\j v -> (show (MutableArgTASeg j), mempty, v)) [0 ..] (idxSels idx)
        val = maybe mempty (\s -> [(show MutableValTASeg, mempty, s)]) (idxValue idx)
       in
        consRep (symbol, "", consFields (args ++ val), [])
    MutStub -> consRep (symbol, mempty, [], [])
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
      SFunc _ -> buildASTExpr cr mut
      Ref _ -> maybe (throwErrSt "expression not found for reference") return (treeExpr t)
      Index _ -> maybe (throwErrSt "expression not found for indexer") return (treeExpr t)
      MutStub -> throwErrSt "expression not found for stub mutable"
    TNConstraint c -> maybe (return $ cnsValidator c) return (treeExpr t)
    TNRefCycle c -> case c of
      RefCycleHori _ -> return $ AST.litCons AST.TopLit
      RefCycleVert -> maybe (throwErrSt "RefCycle: original expression not found") return (treeExpr t)
      RefCycleVertMerger _ -> throwErrSt "RefCycleVertMerger should not be used in the AST"
    TNStructuralCycle _ -> throwErrSt "StructuralCycle should not be used in the AST"

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

defaultTreeRepBuildOption :: TreeRepBuildOption
defaultTreeRepBuildOption = TreeRepBuildOption{trboShowMutArgs = True}

treeToSimpleStr :: Int -> Tree -> String
treeToSimpleStr toff t =
  let TreeRep symbol meta fields listedMetas = iterRepTree t defaultTreeRepBuildOption
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

addrToMermaidNodeID :: TreeAddr -> String
addrToMermaidNodeID (TreeAddr sels) = go (reverse sels)
 where
  mapSel :: TASeg -> String
  mapSel RootTASeg = "root"
  mapSel sel = show sel

  go :: [TASeg] -> String
  go [sel] = mapSel sel
  go (sel : xs) = mapSel sel ++ "_" ++ go xs
  go [] = "nil"

treeToMermaid :: (MonadState Int m) => TreeRepBuildOption -> String -> TreeAddr -> Tree -> m String
treeToMermaid opt msg evalTreeAddr root = do
  let w = printf "---\ntitle: %s, addr %s\n---\n" msg (show evalTreeAddr) <> "flowchart TD"
  rest <- subgraph 0 root "root"
  return $
    w <> "\n" <> rest <> printf "style %s fill:#56e,stroke:#333,stroke-width:4px" (addrToMermaidNodeID evalTreeAddr)
 where
  indent :: Int -> String
  indent n = replicate n ' '

  subgraph :: (MonadState Int m) => Int -> Tree -> String -> m String
  subgraph toff t treeID = do
    let
      (TreeRep symbol meta subReps _) = iterRepTree t opt

      writeLine :: String -> String
      writeLine content = indent toff <> content <> "\n"

      curTreeRepStr =
        writeLine
          ( printf
              "%s[\"`%s`\"]"
              treeID
              $ escape
                ( symbol
                    <> (if null meta then mempty else ", " <> meta)
                    -- <> (if isJust $ treeExpr t then mempty else ",N")
                    -- <> (if treeRecurClosed t then ",#" else mempty)
                )
          )

    foldM
      ( \acc (TreeRepField label attr sub) -> do
          let subTreeID = treeID ++ "_" ++ label
          rest <- subgraph (toff + 2) sub subTreeID
          return $
            acc
              <> writeLine (printf "%s -->|%s| %s" treeID (label <> escape attr) subTreeID)
              <> rest
      )
      curTreeRepStr
      subReps

escape :: String -> String
escape = concatMap $ \case
  '"' -> "#quot;"
  '?' -> "&#63;"
  c -> [c]

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNAtom _ -> ""
  TNBounds _ -> "bds"
  TNStruct{} -> "{}"
  TNList{} -> "[]"
  TNDisj{} -> "dj"
  TNConstraint{} -> "Cnstr"
  TNRefCycle _ -> "RC"
  TNStructuralCycle _ -> "SC"
  TNMutable m -> case m of
    SFunc _ -> "fn"
    Ref _ -> "ref"
    Index _ -> "idx"
    MutStub -> "stub"
  TNBottom _ -> "_|_"
  TNTop -> "_"

escapedTreeSymbol :: Tree -> String
escapedTreeSymbol t = case treeNode t of
  TNStruct{} -> "struct"
  TNList{} -> "list"
  TNBottom _ -> "btm"
  TNTop -> "top"
  _ -> showTreeSymbol t

escapedSimpleTreeStr :: Tree -> String
escapedSimpleTreeStr t = case treeNode t of
  TNStruct s -> escape $ "struct:" <> intercalate "," (map show $ stcOrdLabels s)
  TNAtom _ -> "a"
  _ -> escapedTreeSymbol t

subNodes :: Tree -> [(TASeg, Tree)]
subNodes t = case treeNode t of
  TNStruct struct ->
    [ ( StructTASeg s
      , case sv of
          SField sf -> ssfValue sf
          SLet lb -> lbValue lb
      )
    | (s, sv) <- Map.toList (stcSubs struct)
    ]
      ++ [(StructTASeg $ PatternTASeg i, scsPattern c) | (i, c) <- IntMap.toList $ stcCnstrs struct]
      ++ [(StructTASeg $ PendingTASeg i, dsfLabel dsf) | (i, dsf) <- IntMap.toList $ stcPendSubs struct]
  TNList l -> [(IndexTASeg i, v) | (i, v) <- zip [0 ..] (lstSubs l)]
  TNMutable (SFunc mut) -> [(MutableTASeg $ MutableArgTASeg i, v) | (i, v) <- zip [0 ..] (sfnArgs mut)]
  TNMutable (Index idx) -> [(MutableTASeg $ MutableArgTASeg i, v) | (i, v) <- zip [0 ..] (idxSels idx)]
  TNDisj d ->
    maybe [] (\x -> [(DisjDefaultTASeg, x)]) (dsjDefault d)
      ++ [(DisjDisjunctTASeg i, v) | (i, v) <- zip [0 ..] (dsjDisjuncts d)]
  _ -> []

mutHasRef :: Mutable Tree -> Bool
mutHasRef (Ref _) = True
mutHasRef (SFunc fn) = argsHaveRef (sfnArgs fn)
mutHasRef (Index idxer) = argsHaveRef (idxSels idxer)
mutHasRef MutStub = False

argsHaveRef :: [Tree] -> Bool
argsHaveRef =
  any
    ( \x -> case treeNode x of
        TNMutable subFn -> mutHasRef subFn
        _ -> False
    )

-- Helpers

emptyTree :: Tree
emptyTree =
  Tree
    { treeNode = TNTop
    , treeExpr = Nothing
    , treeNonCnstrExpr = Nothing
    , treeTemp = Nothing
    , treeRecurClosed = False
    }

setTN :: Tree -> TreeNode Tree -> Tree
setTN t n = t{treeNode = n}

setExpr :: Tree -> Maybe AST.Expression -> Tree
setExpr t eM = t{treeExpr = eM}

getAtomFromTree :: Tree -> Maybe Atom
getAtomFromTree t = case treeNode t of
  TNAtom (AtomV a) -> Just a
  TNConstraint c -> Just (amvAtom $ cnsAtom c)
  TNDisj dj -> dsjDefault dj >>= getAtomFromTree
  _ -> Nothing

getAtomVFromTree :: Tree -> Maybe AtomV
getAtomVFromTree t = case treeNode t of
  TNAtom a -> Just a
  _ -> Nothing

getBottomFromTree :: Tree -> Maybe Bottom
getBottomFromTree t = case treeNode t of
  TNBottom b -> Just b
  _ -> Nothing

getBoundsFromTree :: Tree -> Maybe Bounds
getBoundsFromTree t = case treeNode t of
  TNBounds b -> Just b
  _ -> Nothing

getCnstrFromTree :: Tree -> Maybe (Constraint Tree)
getCnstrFromTree t = case treeNode t of
  TNConstraint c -> Just c
  _ -> Nothing

getMutableFromTree :: Tree -> Maybe (Mutable Tree)
getMutableFromTree t = case treeNode t of
  TNMutable f -> Just f
  _ -> Nothing

getRefCycleFromTree :: Tree -> Maybe RefCycle
getRefCycleFromTree t = case treeNode t of
  TNRefCycle c -> Just c
  _ -> Nothing

getStructFromTree :: Tree -> Maybe (Struct Tree)
getStructFromTree t = case treeNode t of
  TNStruct s -> Just s
  _ -> Nothing

getStringFromTree :: Tree -> Maybe String
getStringFromTree t = case treeNode t of
  (TNMutable mut) -> getMutVal mut >>= getStringFromTree
  _ -> getAtomVFromTree t >>= getStringFromAtomV

-- | Check if the node is a reducible ref cycle.
isTreeRefCycleTail :: Tree -> Bool
isTreeRefCycleTail t = case treeNode t of
  TNRefCycle (RefCycleVertMerger _) -> True
  -- TNRefCycle (RefCycleHori _) -> True
  _ -> False

isTreeStructuralCycle :: Tree -> Bool
isTreeStructuralCycle t = case treeNode t of
  TNStructuralCycle _ -> True
  _ -> False

mkNewTree :: TreeNode Tree -> Tree
mkNewTree n = emptyTree{treeNode = n}

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

mutValStubTree :: Tree
mutValStubTree = mkMutableTree MutStub

treesToRef :: [Tree] -> Maybe Path.Reference
treesToRef ts = Path.Reference <$> mapM treeToSel ts
 where
  treeToSel :: Tree -> Maybe Selector
  treeToSel t = case treeNode t of
    -- TODO: Think about changing mutval.
    TNMutable mut
      | Just v <- getMutVal mut -> concreteToSel v
    _ -> concreteToSel t

  concreteToSel :: Tree -> Maybe Selector
  concreteToSel t = case treeNode t of
    TNAtom a
      | (String s) <- va -> Just (StringSel s)
      | (Int j) <- va -> Just (IntSel $ fromIntegral j)
     where
      va = amvAtom a
    -- If a disjunct has a default, then we should try to use the default.
    TNDisj dj | isJust (dsjDefault dj) -> treeToSel (fromJust $ dsjDefault dj)
    _ -> Nothing

addrToTrees :: TreeAddr -> Maybe [Tree]
addrToTrees p = mapM selToTree (addrToNormOrdList p)
 where
  selToTree :: TASeg -> Maybe Tree
  selToTree sel = case sel of
    StructTASeg (StringTASeg s) -> Just $ mkAtomTree (String s)
    IndexTASeg j -> Just $ mkAtomTree (Int (fromIntegral j))
    _ -> Nothing

getStructField :: String -> Tree -> Maybe (Tree, Bool)
getStructField name Tree{treeNode = TNStruct struct} = do
  sv <- lookupStructVal name struct
  case sv of
    SField sf ->
      if lbAttrIsVar (ssfAttr sf)
        then Just (ssfValue sf, False)
        else Nothing
    SLet lb -> Just (lbValue lb, True)
getStructField _ _ = Nothing
