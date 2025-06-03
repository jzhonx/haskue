{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Tree (
  module Value.Atom,
  module Value.Bottom,
  module Value.Bounds,
  module Value.Constraint,
  module Value.Disj,
  module Value.List,
  module Value.Struct,
  module Value.Tree,
  module Value.TreeNode,
  module Value.Mutable,
  module Value.Reference,
  module Value.Comprehension,
  module Value.DisjoinOp,
  module Value.UnifyOp,
)
where

import qualified AST
import Common (BuildASTExpr (..), Env, TreeOp (..), TreeRepBuilder (..))
import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, isJust, listToMaybe)
import qualified Data.Set as Set
import Exception (throwErrSt)
import Path (
  ComprehTASeg (..),
  Selector (..),
  StructTASeg (..),
  TASeg (..),
  TreeAddr,
  ValPath (ValPath),
  addrToNormOrdList,
 )
import Text.Printf (printf)
import Value.Atom
import Value.Bottom
import Value.Bounds
import Value.Comprehension
import Value.Constraint
import Value.Disj
import Value.DisjoinOp
import Value.List
import Value.Mutable
import Value.Reference
import Value.Struct
import Value.TreeNode
import Value.UnifyOp

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
  , treeRecurClosed :: Bool
  -- ^ treeRecurClosed is used to indicate whether the sub-tree including itself is closed.
  , treeIsRootOfSubTree :: Bool
  -- ^ treeIsRootOfSubTree is used to indicate whether the tree is the root of a sub-tree formed by parenthesis.
  , treeIsCyclic :: Bool
  -- ^ treeIsCyclic is used to indicate whether the tree is cyclic.
  -- According to the spec,
  -- If a node a references an ancestor node, we call it and any of its field values a.f cyclic. So if a is cyclic, all
  -- of its descendants are also regarded as cyclic.
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
  subTree = subTreeTN
  setSubTree = setSubTreeTN

  isTreeAtom = isJust . getAtomVFromTree
  isTreeBottom = isJust . getBottomFromTree
  isTreeCnstr = isJust . getCnstrFromTree

  isTreeMutable = isJust . getMutableFromTree

  treeHasAtom t = case treeNode t of
    TNAtom _ -> True
    TNAtomCnstr _ -> True
    TNDisj dj -> maybe False treeHasAtom (dsjDefault dj)
    _ -> False

instance TreeRepBuilder Tree where
  repTree i = treeToSubStr i True

instance TreeRepBuilderIter Tree where
  iterRepTree t opt =
    let trf = buildRepTreeTN t (treeNode t) opt
     in trf
          { trMeta =
              ( if not $ isTreeAtom t
                  then
                    (if treeRecurClosed t then "t_#," else "")
                      ++ (if isJust (treeExpr t) then "" else "t_N,")
                      ++ (if treeIsRootOfSubTree t then "t_R," else "")
                      ++ (if treeIsCyclic t then "t_C," else "")
                  else []
              )
                ++ trMeta trf
          , trFields = trFields trf
          }

buildRepTreeTN :: Tree -> TreeNode Tree -> TreeRepBuildOption -> TreeRep
buildRepTreeTN t tn opt = case tn of
  TNAtom leaf -> consRep (show (amvAtom leaf), mempty, [], [])
  -- TODO: segment
  TNBounds b ->
    consRep
      ( mempty
      , show b
      , []
      , []
      )
  TNBlock es@(Block{blkStruct = s}) ->
    let ordLabels = printf "ord:[%s]" $ intercalate ", " (map show $ stcOrdLabels s)
        attr :: LabelAttr -> String
        attr a = case lbAttrCnstr a of
          SFCRegular -> mempty
          SFCRequired -> "!"
          SFCOptional -> "?"

        isVar :: LabelAttr -> String
        isVar a =
          if lbAttrIsIdent a
            then ",v"
            else mempty

        staticlFieldAttr :: Field Tree -> String
        staticlFieldAttr sf = attr (ssfAttr sf) <> isVar (ssfAttr sf)

        staticFieldMeta :: Field Tree -> String
        staticFieldMeta sf =
          staticlFieldAttr sf
            <> maybe mempty (\raw -> ",raw:" ++ showTreeSymbol raw) (ssfBaseRaw sf)
            <> ",objs:"
            <> show (Set.toList $ ssfObjects sf)

        dlabelAttr :: DynamicField Tree -> String
        dlabelAttr dsf = attr (dsfAttr dsf) <> isVar (dsfAttr dsf) <> ",dynf"

        -- The tuple is (field name, field meta, field value)
        fields :: [(String, String, Tree)]
        fields =
          map
            ( \k ->
                maybe
                  (k, "", mkBottomTree "not found")
                  (\sf -> (k, staticFieldMeta sf, ssfValue sf))
                  (lookupStructField k s)
            )
            (stcOrdLabels s)
            ++ map
              ( \(k, lb) ->
                  (show (StructTASeg $ LetTASeg k), printf ",r:%s" (show $ lbReferred lb), lbValue lb)
              )
              (Map.toList (stcLets s))
            ++ map
              ( \(j, k) -> (show (StructTASeg $ PatternTASeg j 0), ",cns_val:" ++ showTreeSymbol (scsValue k), scsPattern k)
              )
              (IntMap.toList $ stcCnstrs s)
            ++ foldr
              ( \(j, dsf) acc ->
                  (show (StructTASeg $ DynFieldTASeg j 0), dlabelAttr dsf, dsfLabel dsf) : acc
              )
              []
              (IntMap.toList $ stcDynFields s)
            ++ map
              ( \(j, v) ->
                  ( show (StructTASeg $ EmbedTASeg j)
                  , mempty
                  , embValue v
                  )
              )
              (IntMap.toList $ blkEmbeds es)
            ++ maybe [] (\ev -> [(show SubValTASeg, mempty, ev)]) (blkNonStructValue es)

        metas :: [(String, String)]
        metas =
          [ ("idents", show $ Set.toList $ stcBlockIdents s)
          , ("perms", show $ stcPerms s)
          , ("isConcrete", show $ stcIsConcrete s)
          ]
     in consRep
          ( (if stcClosed s then "#" else mempty) <> symbol
          , ordLabels <> ",sid:" <> show (stcID s)
          , consFields fields
          , consMetas metas
          )
  TNList vs ->
    let fields = zipWith (\j v -> (show (IndexTASeg j), mempty, v)) [0 ..] (lstSubs vs)
     in consRep (symbol, mempty, consFields fields, [])
  TNDisj d ->
    let dfField = maybe [] (\v -> [(show DisjDefaultTASeg, mempty, v)]) (dsjDefault d)
        djFields = zipWith (\j v -> (show $ DisjDisjunctTASeg j, mempty, v)) [0 ..] (dsjDisjuncts d)
     in consRep (symbol, printf "dis:%s" (show $ dsjDefIndexes d), consFields dfField ++ consFields djFields, [])
  TNAtomCnstr c ->
    consRep
      ( symbol
      , mempty
      , consFields
          [ ("atom", mempty, mkAtomVTree (cnsAtom c))
          , ("validator", mempty, mkAtomTree $ String (show $ cnsValidator c))
          ]
      , []
      )
  TNRefCycle p -> consRep (symbol, printf "ref-cycle %s" (show p), [], [])
  TNMutable m -> case m of
    RegOp mut ->
      let
        args =
          if trboShowMutArgs opt
            then zipWith (\j v -> (show (MutableArgTASeg j), mempty, v)) [0 ..] (ropArgs mut)
            else []
        val = maybe mempty (\s -> [(show SubValTASeg, mempty, s)]) (ropValue mut)
       in
        consRep
          ( symbol
          , ropName mut
              <> ( printf ", args:%s" (show . length $ ropArgs mut)
                 )
          , consFields (args ++ val)
          , []
          )
    Ref ref ->
      let
        val = maybe mempty (\s -> [(show SubValTASeg, mempty, s)]) (refValue ref)
       in
        consRep
          ( symbol
          , showRefArg (refArg ref) (\x -> listToMaybe $ catMaybes [getStringFromTree x, show <$> getIntFromTree x])
              <> maybe mempty (\from -> ", from:" <> show from) (refOrigAddrs ref)
          , consFields val
          , []
          )
    Compreh cph ->
      let
        clauses =
          map
            ( \(i, cl) ->
                ( show (ComprehTASeg (ComprehIterClauseValTASeg i))
                , mempty
                , getValFromIterClause cl
                )
            )
            (zip [0 ..] (cphIterClauses cph))
        struct = [(show "struct", mempty, cphStruct cph)]
       in
        consRep
          ( symbol
          , ""
          , consFields (clauses ++ struct)
          , []
          )
    DisjOp d ->
      let
        terms =
          if trboShowMutArgs opt
            then
              zipWith
                ( \j v ->
                    (show (MutableArgTASeg j), if dstMarked v then ",*" else "", dstValue v)
                )
                [0 ..]
                (djoTerms d)
            else []
        val = maybe mempty (\s -> [(show SubValTASeg, mempty, s)]) (djoValue d)
       in
        consRep
          ( symbol
          , mempty
          , consFields (terms ++ val)
          , []
          )
    UOp u ->
      let
        conjuncts =
          if trboShowMutArgs opt
            then
              zipWith
                (\j v -> (show (MutableArgTASeg j), mempty, v))
                [0 ..]
                (ufConjuncts u)
            else []
        val = maybe mempty (\s -> [(show SubValTASeg, mempty, s)]) (ufValue u)
       in
        consRep (symbol, "", consFields (conjuncts ++ val), [])
  TNCnstredVal c -> consRep (symbol, "", consFields [(show SubValTASeg, "", cnsedVal c)], [])
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
  show = treeToSubStr 0 True

instance BuildASTExpr Tree where
  buildASTExpr cr t = case treeNode t of
    TNTop -> return $ AST.litCons (pure AST.TopLit)
    TNBottom _ -> return $ AST.litCons (pure AST.BottomLit)
    TNAtom s -> buildASTExpr cr s
    TNBounds b -> buildASTExpr cr b
    TNBlock block@(Block{blkStruct = s})
      | Just ev <- blkNonStructValue block -> buildASTExpr cr ev
      | let dynsReady = all (isJust . getNonMutFromTree . dsfLabel) (IntMap.elems $ stcDynFields s)
      , let embedsReady = all (isJust . getNonMutFromTree . embValue) (IntMap.elems $ blkEmbeds block)
      , dynsReady && embedsReady ->
          buildStructASTExpr cr block
      -- If dynamic fields or embedded values are not ready, then we need to use the original expression.
      | otherwise -> maybe (buildStructASTExpr cr block) return (treeExpr t)
    TNList l -> buildASTExpr cr l
    TNDisj d -> buildASTExpr cr d
    TNMutable mut -> case mut of
      RegOp _ -> buildASTExpr cr mut
      Ref _ -> maybe (throwErrSt $ printf "expression not found for reference: %s" (show t)) return (treeExpr t)
      Compreh cph -> do
        ce <- buildComprehASTExpr cr cph
        return $
          AST.litCons $
            AST.LitStructLit AST.<^> pure (AST.StructLit [AST.Embedding AST.<<^>> AST.EmbedComprehension AST.<^> ce])
      DisjOp _ -> maybe (throwErrSt "expression not found for disjunction") return (treeExpr t)
      UOp _ -> maybe (buildASTExpr cr mut) return (treeExpr t)
    TNAtomCnstr c -> maybe (return $ cnsValidator c) return (treeExpr t)
    TNRefCycle _ -> return $ AST.litCons (pure AST.TopLit)
    TNCnstredVal c -> maybe (throwErrSt "expression not found for cnstred value") return (cnsedOrigExpr c)

-- | Patterns are not included in the AST.
buildStructASTExpr :: (Env r s m) => Bool -> Block Tree -> m AST.Expression
buildStructASTExpr concrete block@(Block{blkStruct = s}) =
  let
    processSField :: (Env r s m) => (String, Field Tree) -> m AST.Declaration
    processSField (sel, sf) = do
      e <- buildASTExpr concrete (ssfValue sf)
      return $
        AST.FieldDecl
          AST.<^> pure
            ( AST.Field
                [ labelCons (ssfAttr sf) $
                    if lbAttrIsIdent (ssfAttr sf)
                      then AST.LabelID AST.<^> (pure sel)
                      else pure $ AST.LabelString sel
                ]
                e
            )

    processDynField :: (Env r s m) => DynamicField Tree -> m AST.Declaration
    processDynField sf = do
      e <- buildASTExpr concrete (dsfValue sf)
      return $
        AST.FieldDecl
          AST.<^> pure
            ( AST.Field
                [ labelCons (dsfAttr sf) (pure $ AST.LabelNameExpr (dsfLabelExpr sf))
                ]
                e
            )

    processEmbed :: (Env r s m) => Embedding Tree -> m AST.Declaration
    processEmbed embed = case treeNode (embValue embed) of
      TNMutable (Compreh c) -> do
        ce <- buildComprehASTExpr concrete c
        return $ AST.Embedding AST.<<^>> AST.EmbedComprehension AST.<^> ce
      _ -> do
        e <- buildASTExpr concrete (embValue embed)
        return $ AST.Embedding AST.<<^>> AST.AliasExpr AST.<^> e

    labelCons :: LabelAttr -> AST.LabelName -> AST.Label
    labelCons attr ln =
      AST.Label
        AST.<^> pure
          ( AST.LabelName
              ln
              ( case lbAttrCnstr attr of
                  SFCRegular -> AST.RegularLabel
                  SFCRequired -> AST.RequiredLabel
                  SFCOptional -> AST.OptionalLabel
              )
          )
   in
    do
      stcs <-
        mapM
          ( \l -> do
              pair <-
                maybe
                  (throwErrSt $ "struct field not found: " ++ l)
                  (\f -> return (l, f))
                  (lookupStructField l s)
              processSField pair
          )
          (stcOrdLabels s)
      dyns <-
        foldM
          ( \acc dsf ->
              -- If the label can be evaluated to an atom, then the dynamic field should be already in the static
              -- fields.
              maybe
                ( do
                    decl <- processDynField dsf
                    return (decl : acc)
                )
                (const $ return acc)
                (getAtomFromTree $ dsfLabel dsf)
          )
          []
          (IntMap.elems $ stcDynFields s)
      embeds <- mapM processEmbed (IntMap.elems $ blkEmbeds block)

      return $ AST.litCons $ AST.LitStructLit AST.<^> pure (AST.StructLit (stcs ++ dyns ++ embeds))

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

defaultTreeRepBuildOption :: TreeRepBuildOption
defaultTreeRepBuildOption = TreeRepBuildOption{trboShowMutArgs = True}

treeFullStr :: Int -> Tree -> String
treeFullStr toff t =
  let TreeRep symbol meta fields listedMetas = iterRepTree t defaultTreeRepBuildOption
   in "("
        <> ( if
              | null symbol -> meta
              | null meta -> symbol
              | otherwise -> symbol <> " " <> meta
           )
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
                              <> treeFullStr (length pre) sub
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

escape :: String -> String
escape = concatMap $ \case
  '"' -> "#quot;"
  '?' -> "&#63;"
  c -> [c]

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNAtom _ -> "a"
  TNBounds _ -> "bds"
  TNBlock{} -> "{}"
  TNList{} -> "[]"
  TNDisj{} -> "dj"
  TNAtomCnstr{} -> "Cnstr"
  TNRefCycle _ -> "RC"
  TNMutable m -> case m of
    RegOp _ -> "fn"
    Ref _ -> "ref"
    Compreh _ -> "compreh"
    DisjOp _ -> "disjoin"
    UOp _ -> "unify"
  TNCnstredVal _ -> "cnstred"
  TNBottom _ -> "_|_"
  TNTop -> "_"

showValueType :: (Env r s m) => Tree -> m String
showValueType t = case treeNode t of
  TNAtom (AtomV a) -> case a of
    String _ -> return "string"
    Int _ -> return "int"
    Float _ -> return "float"
    Bool _ -> return "bool"
    Null -> return "null"
  TNBounds b -> return $ show b
  TNBottom _ -> return "_|_"
  TNBlock _ -> return "struct"
  TNList _ -> return "list"
  TNTop -> return "_"
  _ -> throwErrSt $ "not a value type: " ++ show t

treeToSubStr :: Int -> Bool -> Tree -> String
treeToSubStr toff moreSub t =
  let TreeRep symbol meta fields listedMetas = iterRepTree t defaultTreeRepBuildOption
   in "("
        <> ( if
              | null symbol -> meta
              | null meta -> symbol
              | otherwise -> symbol <> " " <> meta
           )
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
                              <> ( if moreSub
                                    then
                                      treeToSubStr
                                        (length pre)
                                        -- Some nodes can have one more level of sub-tree.
                                        ( case treeNode sub of
                                            TNCnstredVal _ -> True
                                            TNMutable _ -> True
                                            TNAtomCnstr _ -> True
                                            _ -> False
                                        )
                                        sub
                                    else showTreeSymbol sub
                                 )
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

-- | Generate a list of sub-trees that have values to reduce, not the values that have been reduced.
subNodes :: Tree -> [(TASeg, Tree)]
subNodes t = case treeNode t of
  TNBlock (Block{blkStruct = struct}) ->
    [(StructTASeg $ StringTASeg s, ssfValue field) | (s, field) <- Map.toList (stcFields struct)]
      ++ [(StructTASeg $ PatternTASeg i 0, scsPattern c) | (i, c) <- IntMap.toList $ stcCnstrs struct]
      ++ [(StructTASeg $ DynFieldTASeg i 0, dsfLabel dsf) | (i, dsf) <- IntMap.toList $ stcDynFields struct]
  TNList l -> [(IndexTASeg i, v) | (i, v) <- zip [0 ..] (lstSubs l)]
  TNMutable mut -> [(MutableArgTASeg i, v) | (i, v) <- zip [0 ..] (getMutArgs mut)]
  TNDisj d ->
    maybe [] (\x -> [(DisjDefaultTASeg, x)]) (dsjDefault d)
      ++ [(DisjDisjunctTASeg i, v) | (i, v) <- zip [0 ..] (dsjDisjuncts d)]
  _ -> []

-- | TODO: comprehension struct
rawNodes :: Tree -> [(Path.TASeg, Tree)]
rawNodes t = case treeNode t of
  TNBlock block@(Block{blkStruct = struct}) ->
    [(Path.StructTASeg $ Path.PatternTASeg i 1, scsValue c) | (i, c) <- IntMap.toList $ stcCnstrs struct]
      ++ [(Path.StructTASeg $ Path.DynFieldTASeg i 1, dsfValue dsf) | (i, dsf) <- IntMap.toList $ stcDynFields struct]
      ++ [(Path.StructTASeg $ Path.LetTASeg s, lbValue lb) | (s, lb) <- Map.toList $ stcLets struct]
      ++ [(Path.StructTASeg $ Path.EmbedTASeg i, embValue emb) | (i, emb) <- IntMap.toList $ blkEmbeds block]
  TNMutable (Compreh c) ->
    [ (Path.ComprehTASeg (Path.ComprehIterClauseValTASeg i), getValFromIterClause v)
    | (i, v) <- zip [0 ..] (cphIterClauses c)
    ]
  _ -> []

-- Helpers

emptyTree :: Tree
emptyTree =
  Tree
    { treeNode = TNTop
    , treeExpr = Nothing
    , treeRecurClosed = False
    , treeIsRootOfSubTree = False
    , treeIsCyclic = False
    }

setTN :: Tree -> TreeNode Tree -> Tree
setTN t n = t{treeNode = n}

setExpr :: Tree -> Maybe AST.Expression -> Tree
setExpr t eM = t{treeExpr = eM}

getCUEValTree :: Tree -> Maybe Tree
getCUEValTree t = case treeNode t of
  TNAtom _ -> Just t
  TNBottom _ -> Just t
  TNTop -> Just t
  TNBounds _ -> Just t
  TNList _ -> Just t
  TNDisj _ -> Just t
  TNBlock block
    | let v = blkNonStructValue block
    , Just ev <- v ->
        getCUEValTree ev
    | otherwise -> Just t
  TNRefCycle _ -> Nothing
  TNAtomCnstr c -> Just $ mkAtomVTree (cnsAtom c)
  TNCnstredVal c -> getCUEValTree $ cnsedVal c
  TNMutable mut -> getMutVal mut >>= getCUEValTree

getConcreteValue :: Tree -> Maybe Tree
getConcreteValue t = case treeNode t of
  TNAtom _ -> Just t
  TNAtomCnstr _ -> Just t
  TNDisj dj -> dsjDefault dj >>= getConcreteValue
  TNMutable mut -> getMutVal mut >>= getConcreteValue
  TNCnstredVal c -> getConcreteValue $ cnsedVal c
  TNBlock block@(Block{blkStruct = s})
    | let v = blkNonStructValue block
    , Just ev <- v ->
        getConcreteValue ev
    | otherwise -> if stcIsConcrete s then Just t else Nothing
  _ -> Nothing

getNonMutFromTree :: Tree -> Maybe Tree
getNonMutFromTree t = case treeNode t of
  TNMutable mut -> getMutVal mut >>= getNonMutFromTree
  _ -> return t

-- | TODO: make all get calling helper functions to deal with default, cnstred and mutable.
getAtomFromTree :: Tree -> Maybe Atom
getAtomFromTree t = case treeNode t of
  TNAtom (AtomV a) -> Just a
  TNAtomCnstr c -> Just (amvAtom $ cnsAtom c)
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

getCnstrFromTree :: Tree -> Maybe (AtomCnstr Tree)
getCnstrFromTree t = case treeNode t of
  TNAtomCnstr c -> Just c
  _ -> Nothing

{- | Get the disjunction from the tree.

It stops at the first disjunction found. It does not go deeper to the default value of the disjunction.
-}
getDisjFromTree :: Tree -> Maybe (Disj Tree)
getDisjFromTree t = case treeNode t of
  TNMutable mut -> getMutVal mut >>= getDisjFromTree
  TNDisj d -> Just d
  _ -> Nothing

getMutableFromTree :: Tree -> Maybe (Mutable Tree)
getMutableFromTree t = case treeNode t of
  TNMutable f -> Just f
  _ -> Nothing

getRefFromTree :: Tree -> Maybe (Reference Tree)
getRefFromTree t = case treeNode t of
  TNMutable (Ref r) -> Just r
  _ -> Nothing

getBlockFromTree :: Tree -> Maybe (Block Tree)
getBlockFromTree t = case treeNode t of
  TNBlock b -> Just b
  _ -> Nothing

getListFromTree :: Tree -> Maybe (List Tree)
getListFromTree t = case treeNode t of
  TNList l -> Just l
  _ -> Nothing

getCnstredValFromTree :: Tree -> Maybe Tree
getCnstredValFromTree t = case treeNode t of
  TNCnstredVal c -> Just $ cnsedVal c
  _ -> Nothing

-- | TODO: default and cnstred?
getStringFromTree :: Tree -> Maybe String
getStringFromTree t = case treeNode t of
  (TNMutable mut) -> getMutVal mut >>= getStringFromTree
  _ -> getAtomVFromTree t >>= getStringFromAtomV

getIntFromTree :: Tree -> Maybe Int
getIntFromTree t = case treeNode t of
  (TNMutable mut) -> getMutVal mut >>= getIntFromTree
  _ -> getAtomVFromTree t >>= getIntFromAtomV

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
mkCnstrTree a e = mkNewTree . TNAtomCnstr $ AtomCnstr a e

mkDisjTree :: Disj Tree -> Tree
mkDisjTree d = mkNewTree (TNDisj d)

mkMutableTree :: Mutable Tree -> Tree
mkMutableTree fn = mkNewTree (TNMutable fn)

mkListTree :: [Tree] -> Tree
mkListTree ts = mkNewTree (TNList $ List{lstSubs = ts})

mkBlockTree :: Block Tree -> Tree
mkBlockTree b = mkNewTree (TNBlock b)

mkStructTree :: Struct Tree -> Tree
mkStructTree s = mkNewTree (TNBlock (emptyBlock{blkStruct = s}))

mkCnstredValTree :: Tree -> Maybe AST.Expression -> Tree
mkCnstredValTree v m = mkNewTree (TNCnstredVal $ CnstredVal v m)

-- | Create an index function node.
appendSelToRefTree :: Tree -> Tree -> Tree
appendSelToRefTree oprnd selArg = case treeNode oprnd of
  TNMutable m
    | Just ref <- getRefFromMutable m ->
        mkMutableTree $ Ref $ ref{refArg = appendRefArg selArg (refArg ref)}
  _ -> mkMutableTree $ Ref $ mkIndexRef [oprnd, selArg]

treesToValPath :: [Tree] -> Maybe Path.ValPath
treesToValPath ts = Path.ValPath <$> mapM treeToSel ts

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
