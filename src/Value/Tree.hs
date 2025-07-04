{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Value.Tree where

import qualified AST
import Common (Env)
import Control.Monad.Except (MonadError)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, isJust, listToMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import Path (
  ComprehTASeg (..),
  Selector (..),
  StructTASeg (..),
  TASeg (..),
  TreeAddr,
  ValPath (ValPath),
  addrToList,
 )
import Text.Printf (printf)
import Value.Atom
import Value.Bottom
import Value.Bounds
import Value.Comprehension
import Value.Constraint
import Value.Disj
import Value.DisjoinOp
import Value.Interpolation
import Value.List
import Value.Mutable
import Value.Reference
import Value.Struct
import Value.UnifyOp

-- | TreeNode represents a tree structure that contains values.
data TreeNode
  = -- | TNAtom contains an atom value.
    TNAtom Atom
  | TNBottom Bottom
  | TNBounds Bounds
  | TNTop
  | TNBlock Block
  | TNList List
  | TNDisj Disj
  | TNAtomCnstr AtomCnstr
  | -- | TNRefCycle represents the result of a field referencing itself or its sub field.
    -- It also represents recursion, which is mostly disallowed in the CUE.
    -- If a field references itself, the address is the same as the field reference. For example: x: x.
    -- If a field references its sub field, the address is the sub field address. For example: x: x.a.
    TNRefCycle TreeAddr
  | TNMutable Mutable
  | TNCnstredVal CnstredVal
  deriving (Generic)

-- Some rules:
-- 1. If a node is a Mutable that contains references, then the node should not be supplanted to other places without
-- changing the dependencies.
-- 2. Evaluation is top-down. Evaluation do not go deeper unless necessary.
data Tree = Tree
  { treeNode :: TreeNode
  , treeExpr :: Maybe AST.Expression
  -- ^ treeExpr is the parsed expression.
  , treeRecurClosed :: !Bool
  -- ^ treeRecurClosed is used to indicate whether the sub-tree including itself is closed.
  , treeIsRootOfSubTree :: !Bool
  -- ^ treeIsRootOfSubTree is used to indicate whether the tree is the root of a sub-tree formed by parenthesis.
  , treeIsCyclic :: !Bool
  -- ^ treeIsCyclic is used to indicate whether the tree is cyclic.
  -- According to the spec,
  -- If a node a references an ancestor node, we call it and any of its field values a.f cyclic. So if a is cyclic, all
  -- of its descendants are also regarded as cyclic.
  , treeVersion :: !Int
  }
  deriving (Generic)

pattern TN :: TreeNode -> Tree
pattern TN tn <- Tree{treeNode = tn}

pattern IsAtom :: Atom -> Tree
pattern IsAtom a <- TN (TNAtom a)

pattern IsBottom :: Bottom -> Tree
pattern IsBottom b <- TN (TNBottom b)

pattern IsBounds :: Bounds -> Tree
pattern IsBounds b <- TN (TNBounds b)

pattern IsTop :: Tree
pattern IsTop <- TN TNTop

pattern IsBlock :: Block -> Tree
pattern IsBlock block <- TN (TNBlock block)

pattern IsList :: List -> Tree
pattern IsList lst <- TN (TNList lst)

pattern IsDisj :: Disj -> Tree
pattern IsDisj d <- TN (TNDisj d)

pattern IsAtomCnstr :: AtomCnstr -> Tree
pattern IsAtomCnstr c <- TN (TNAtomCnstr c)

pattern IsRefCycle :: TreeAddr -> Tree
pattern IsRefCycle addr <- TN (TNRefCycle addr)

pattern IsCnstredVal :: CnstredVal -> Tree
pattern IsCnstredVal cv <- TN (TNCnstredVal cv)

pattern IsMutable :: Mutable -> Tree
pattern IsMutable mut <- TN (TNMutable mut)

pattern IsRef :: Reference -> Tree
pattern IsRef ref <- IsMutable (Ref ref)

pattern IsRegOp :: RegularOp -> Tree
pattern IsRegOp rop <- IsMutable (RegOp rop)

{- | descend into the tree with the given segment.

This should only be used by TreeCursor.
-}
subTree :: (HasCallStack) => TASeg -> Tree -> Maybe Tree
subTree seg t = case (seg, treeNode t) of
  (RootTASeg, _) -> Just t
  (StructTASeg s, TNBlock estruct@(Block{blkStruct = struct})) -> case s of
    StringTASeg name
      | Just sf <- lookupStructField (TE.decodeUtf8 name) struct -> Just $ ssfValue sf
    PatternTASeg i j -> (if j == 0 then scsPattern else scsValue) <$> stcCnstrs struct IntMap.!? i
    DynFieldTASeg i j ->
      (if j == 0 then dsfLabel else dsfValue) <$> stcDynFields struct IntMap.!? i
    LetTASeg name
      | Just lb <- lookupStructLet (TE.decodeUtf8 name) struct -> Just (lbValue lb)
    EmbedTASeg i -> embValue <$> blkEmbeds estruct IntMap.!? i
    _ -> Nothing
  (SubValTASeg, TNBlock estruct) -> blkNonStructValue estruct
  (IndexTASeg i, TNList vs) -> lstSubs vs `indexList` i
  (_, TNMutable mut)
    | MutArgTASeg i <- seg -> getMutArgs mut Seq.!? i
    | (ComprehTASeg (ComprehIterClauseValTASeg i), Compreh c) <- (seg, mut) ->
        getValFromIterClause <$> (cphIterClauses c `indexList` i)
    | (ComprehTASeg ComprehIterValTASeg, Compreh c) <- (seg, mut) -> cphIterVal c
    | SubValTASeg <- seg -> getMutVal mut
  (_, TNDisj d)
    | DisjDefTASeg <- seg -> dsjDefault d
    | DisjRegTASeg i <- seg -> dsjDisjuncts d `indexList` i
  -- CnstredVal is just a wrapper of a value. If we have additional segments, we should descend into the value.
  (_, TNCnstredVal cv)
    | SubValTASeg <- seg -> Just (cnsedVal cv)
  _ -> Nothing

-- | Set the sub tree with the given segment and new tree.
setSubTree :: (Env r s m) => TASeg -> Tree -> Tree -> m Tree
setSubTree seg subT parT = do
  n <- case (seg, treeNode parT) of
    (StructTASeg s, TNBlock estruct) -> updateParStruct estruct s
    (SubValTASeg, TNBlock estruct) -> return $ TNBlock estruct{blkNonStructValue = Just subT}
    (IndexTASeg i, TNList vs) ->
      let subs = lstSubs vs
          l = TNList $ vs{lstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return l
    (_, TNMutable mut)
      | MutArgTASeg i <- seg -> return $ TNMutable $ updateMutArg i subT mut
      | ComprehTASeg ComprehIterValTASeg <- seg
      , Compreh c <- mut ->
          return $ TNMutable $ Compreh c{cphIterVal = Just subT}
      | ComprehTASeg (ComprehIterClauseValTASeg i) <- seg
      , Compreh c <- mut -> do
          let clauses = cphIterClauses c
              clause = setValInIterClause subT (clauses !! i)
          return $ TNMutable $ Compreh c{cphIterClauses = take i clauses ++ [clause] ++ drop (i + 1) clauses}
      | SubValTASeg <- seg -> return . TNMutable $ setMutVal (Just subT) mut
    (_, TNDisj d)
      | DisjDefTASeg <- seg -> return (TNDisj $ d{dsjDefault = dsjDefault d})
      | DisjRegTASeg i <- seg ->
          return (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)})
    (_, TNCnstredVal cv)
      | SubValTASeg <- seg -> return $ TNCnstredVal cv{cnsedVal = subT}
    (ParentTASeg, _) -> throwErrSt "setSubTreeTN: ParentTASeg is not allowed"
    (RootTASeg, _) -> throwErrSt "setSubTreeT: RootTASeg is not allowed"
    _ -> throwErrSt insertErrMsg
  return $ parT{treeNode = n}
 where
  structToTN :: Struct -> Block -> TreeNode
  structToTN s est = TNBlock est{blkStruct = s}

  updateParStruct :: (MonadError String m, HasCallStack) => Block -> StructTASeg -> m TreeNode
  updateParStruct parEStruct@(Block{blkStruct = parStruct}) labelSeg
    -- The label segment should already exist in the parent struct. Otherwise the description of the field will not be
    -- found.
    | StringTASeg name <- labelSeg
    , Just field <- lookupStructField (TE.decodeUtf8 name) parStruct =
        let
          newField = subT `updateFieldValue` field
          newStruct = updateStructField (TE.decodeUtf8 name) newField parStruct
         in
          return (structToTN newStruct parEStruct)
    | LetTASeg name <- labelSeg
    , Just oldLet <- lookupStructLet (TE.decodeUtf8 name) parStruct =
        let
          newLet = oldLet{lbValue = subT}
          newStruct = updateStructLet (TE.decodeUtf8 name) newLet parStruct
         in
          return (structToTN newStruct parEStruct)
    | PatternTASeg i j <- labelSeg =
        let
          psf = stcCnstrs parStruct IntMap.! i
          newPSF = if j == 0 then psf{scsPattern = subT} else psf{scsValue = subT}
          newStruct = parStruct{stcCnstrs = IntMap.insert i newPSF (stcCnstrs parStruct)}
         in
          return (structToTN newStruct parEStruct)
    | DynFieldTASeg i j <- labelSeg =
        let
          pends = stcDynFields parStruct
          psf = pends IntMap.! i
          newPSF = if j == 0 then psf{dsfLabel = subT} else psf{dsfValue = subT}
          newStruct = parStruct{stcDynFields = IntMap.insert i newPSF pends}
         in
          return (structToTN newStruct parEStruct)
    | EmbedTASeg i <- labelSeg =
        let
          oldEmbeds = blkEmbeds parEStruct
          newEmbed = (oldEmbeds IntMap.! i){embValue = subT}
         in
          return $ TNBlock parEStruct{blkEmbeds = IntMap.insert i newEmbed oldEmbeds}
  updateParStruct _ _ = throwErrSt insertErrMsg

  insertErrMsg :: String
  insertErrMsg =
    printf
      "setSubTreeTN: cannot insert child to parent, segment: %s, child:\n%s\nparent:\n%s"
      (show seg)
      (show subT)
      (show parT)

indexList :: [a] -> Int -> Maybe a
indexList xs i = if i < length xs then Just (xs !! i) else Nothing

-- = TreeNode getters and setters =

setTN :: Tree -> TreeNode -> Tree
setTN t n = t{treeNode = n}

setExpr :: Tree -> Maybe AST.Expression -> Tree
setExpr t eM = t{treeExpr = eM}

-- | Retrieve the basic value from the tree.
rtrBase :: Tree -> Maybe Tree
rtrBase t = case treeNode t of
  TNAtom _ -> Just t
  TNBottom _ -> Just t
  TNTop -> Just t
  TNBounds _ -> Just t
  TNList _ -> Just t
  TNDisj _ -> Just t
  TNBlock block
    | Just ev <- blkNonStructValue block -> rtrBase ev
    | otherwise -> Just t
  TNAtomCnstr c -> Just $ mkAtomTree (cnsAtom c)
  TNCnstredVal c -> rtrBase $ cnsedVal c
  TNMutable mut -> getMutVal mut >>= rtrBase
  TNRefCycle _ -> Nothing

-- | Retrieve the singular value which is not a disjunction.
rtrCUESingular :: Tree -> Maybe Tree
rtrCUESingular t = do
  v <- rtrBase t
  case treeNode v of
    TNAtom _ -> Just v
    TNBottom _ -> Just v
    TNTop -> Just v
    TNList _ -> Just v
    TNBlock _ -> Just v
    TNDisj d | Just df <- dsjDefault d -> rtrCUESingular df
    _ -> Nothing

-- | Retrieve the concrete value from the tree.
rtrConcrete :: Tree -> Maybe Tree
rtrConcrete t = do
  v <- rtrCUESingular t
  case v of
    IsAtom _ -> Just v
    -- There is only struct value after retrieving concrete value.
    IsBlock (Block{blkStruct = s}) -> if stcIsConcrete s then Just v else Nothing
    _ -> Nothing

rtrNonMut :: Tree -> Maybe Tree
rtrNonMut (IsMutable mut) = getMutVal mut >>= rtrNonMut
rtrNonMut t = return t

rtrAtom :: Tree -> Maybe Atom
rtrAtom t = do
  v <- rtrCUESingular t
  case v of
    IsAtom a -> Just a
    _ -> Nothing

rtrString :: Tree -> Maybe T.Text
rtrString (rtrAtom -> Just (String s)) = Just s
rtrString _ = Nothing

rtrInt :: Tree -> Maybe Int
rtrInt (rtrAtom -> Just (Int i)) = Just (fromIntegral i)
rtrInt _ = Nothing

rtrBool :: Tree -> Maybe Bool
rtrBool (rtrAtom -> Just (Bool b)) = Just b
rtrBool _ = Nothing

rtrFloat :: Tree -> Maybe Float
rtrFloat (rtrAtom -> Just (Float f)) = Just (fromRational (toRational f))
rtrFloat _ = Nothing

rtrBottom :: Tree -> Maybe Bottom
rtrBottom t = do
  v <- rtrCUESingular t
  case v of
    IsBottom b -> Just b
    _ -> Nothing

{- | Get the disjunction from the tree.

It stops at the first disjunction found. It does not go deeper to the default value of the disjunction.
-}
rtrDisj :: Tree -> Maybe Disj
rtrDisj t = do
  v <- rtrBase t
  case v of
    IsDisj d -> Just d
    _ -> Nothing

rtrList :: Tree -> Maybe List
rtrList t = do
  v <- rtrCUESingular t
  case v of
    IsList l -> Just l
    _ -> Nothing

rtrStruct :: Tree -> Maybe Struct
rtrStruct t = do
  v <- rtrCUESingular t
  case v of
    IsBlock Block{blkStruct = struct} -> Just struct
    _ -> Nothing

-- = Traversal =

-- | Generate a list of sub-trees that have values to reduce, not the values that have been reduced.
subNodes :: Tree -> [(TASeg, Tree)]
subNodes t = case treeNode t of
  TNBlock (Block{blkStruct = struct}) ->
    [(StructTASeg $ StringTASeg (TE.encodeUtf8 s), ssfValue field) | (s, field) <- Map.toList (stcFields struct)]
      ++ [(StructTASeg $ PatternTASeg i 0, scsPattern c) | (i, c) <- IntMap.toList $ stcCnstrs struct]
      ++ [(StructTASeg $ DynFieldTASeg i 0, dsfLabel dsf) | (i, dsf) <- IntMap.toList $ stcDynFields struct]
  TNList l -> [(IndexTASeg i, v) | (i, v) <- zip [0 ..] (lstSubs l)]
  TNMutable mut -> [(MutArgTASeg i, v) | (i, v) <- zip [0 ..] (toList $ getMutArgs mut)]
  TNDisj d ->
    maybe [] (\x -> [(DisjDefTASeg, x)]) (dsjDefault d)
      ++ [(DisjRegTASeg i, v) | (i, v) <- zip [0 ..] (dsjDisjuncts d)]
  _ -> []

-- | TODO: comprehension struct
rawNodes :: Tree -> [(TASeg, Tree)]
rawNodes t = case treeNode t of
  TNBlock block@(Block{blkStruct = struct}) ->
    [(StructTASeg $ PatternTASeg i 1, scsValue c) | (i, c) <- IntMap.toList $ stcCnstrs struct]
      ++ [(StructTASeg $ DynFieldTASeg i 1, dsfValue dsf) | (i, dsf) <- IntMap.toList $ stcDynFields struct]
      ++ [(StructTASeg $ LetTASeg (TE.encodeUtf8 s), lbValue lb) | (s, lb) <- Map.toList $ stcLets struct]
      ++ [(StructTASeg $ EmbedTASeg i, embValue emb) | (i, emb) <- IntMap.toList $ blkEmbeds block]
  TNMutable (Compreh c) ->
    [ (ComprehTASeg (ComprehIterClauseValTASeg i), getValFromIterClause v)
    | (i, v) <- zip [0 ..] (cphIterClauses c)
    ]
  _ -> []

-- = Helpers =

emptyTree :: Tree
emptyTree =
  Tree
    { treeNode = TNTop
    , treeExpr = Nothing
    , treeRecurClosed = False
    , treeIsRootOfSubTree = False
    , treeIsCyclic = False
    , treeVersion = 0
    }

mkNewTree :: TreeNode -> Tree
mkNewTree n = emptyTree{treeNode = n}

mkAtomTree :: Atom -> Tree
mkAtomTree a = mkNewTree (TNAtom a)

mkBottomTree :: String -> Tree
mkBottomTree msg = mkNewTree (TNBottom $ Bottom{btmMsg = msg})

mkBoundsTree :: [Bound] -> Tree
mkBoundsTree bs = mkNewTree (TNBounds $ Bounds{bdsList = bs})

mkCnstrTree :: Atom -> AST.Expression -> Tree
mkCnstrTree a e = mkNewTree . TNAtomCnstr $ AtomCnstr a e

mkDisjTree :: Disj -> Tree
mkDisjTree d = mkNewTree (TNDisj d)

mkMutableTree :: Mutable -> Tree
mkMutableTree fn = mkNewTree (TNMutable fn)

mkListTree :: [Tree] -> Tree
mkListTree ts = mkNewTree (TNList $ List{lstSubs = ts})

mkBlockTree :: Block -> Tree
mkBlockTree b = mkNewTree (TNBlock b)

mkStructTree :: Struct -> Tree
mkStructTree s = mkNewTree (TNBlock (emptyBlock{blkStruct = s}))

mkCnstredValTree :: Tree -> Maybe AST.Expression -> Tree
mkCnstredValTree v m = mkNewTree (TNCnstredVal $ CnstredVal v m)

-- | Create an index function node.
appendSelToRefTree :: Tree -> Tree -> Tree
appendSelToRefTree oprnd selArg = case treeNode oprnd of
  TNMutable m
    | Just ref <- getRefFromMutable m ->
        mkMutableTree $ Ref $ ref{refArg = appendRefArg selArg (refArg ref)}
  _ -> mkMutableTree $ Ref $ mkIndexRef (Seq.fromList [oprnd, selArg])

treesToValPath :: [Tree] -> Maybe ValPath
treesToValPath ts = ValPath <$> mapM treeToSel ts

treeToSel :: Tree -> Maybe Selector
treeToSel t = case treeNode t of
  -- TODO: Think about changing mutval.
  TNMutable mut
    | Just v <- getMutVal mut -> concreteToSel v
  _ -> concreteToSel t

concreteToSel :: Tree -> Maybe Selector
concreteToSel t = case treeNode t of
  TNAtom a
    | (String s) <- a -> Just (StringSel (TE.encodeUtf8 s))
    | (Int j) <- a -> Just (IntSel $ fromIntegral j)
   where

  -- If a disjunct has a default, then we should try to use the default.
  TNDisj dj | isJust (dsjDefault dj) -> treeToSel (fromJust $ dsjDefault dj)
  _ -> Nothing

addrToTrees :: TreeAddr -> Maybe [Tree]
addrToTrees p = mapM selToTree (addrToList p)
 where
  selToTree :: TASeg -> Maybe Tree
  selToTree sel = case sel of
    StructTASeg (StringTASeg s) -> Just $ mkAtomTree (String (TE.decodeUtf8 s))
    IndexTASeg j -> Just $ mkAtomTree (Int (fromIntegral j))
    _ -> Nothing

-- built-in functions
builtinMutableTable :: [(String, Tree)]
builtinMutableTable =
  [
    ( "close"
    , mkMutableTree . RegOp $
        -- built-in close does not recursively close the struct.
        emptyRegularOp
          { ropName = "close"
          , ropArgs = Seq.fromList [mkNewTree TNTop]
          , ropOpType = CloseFunc
          }
    )
  ]

-- = TreeRep =

instance Show Tree where
  show = treeToSubStr 0 True

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

newtype TreeRepBuildOption = TreeRepBuildOption {trboShowMutArgs :: Bool}

defaultTreeRepBuildOption :: TreeRepBuildOption
defaultTreeRepBuildOption = TreeRepBuildOption{trboShowMutArgs = True}

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

iterRepTree :: Tree -> TreeRepBuildOption -> TreeRep
iterRepTree t opt =
  let trf = buildRepTreeTN t (treeNode t) opt
   in trf
        { trMeta =
            ( case t of
                IsAtom _ -> []
                _ ->
                  (if treeRecurClosed t then "t_#," else "")
                    ++ (if isJust (treeExpr t) then "" else "t_N,")
                    ++ (if treeIsRootOfSubTree t then "t_R," else "")
                    ++ (if treeIsCyclic t then "t_C," else "")
                    ++ printf "t_v:%d," (treeVersion t)
            )
              ++ trMeta trf
        , trFields = trFields trf
        }

buildRepTreeTN :: Tree -> TreeNode -> TreeRepBuildOption -> TreeRep
buildRepTreeTN t tn opt = case tn of
  TNAtom leaf -> consRep (show leaf, mempty, [], [])
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

        staticlFieldAttr :: Field -> String
        staticlFieldAttr sf = attr (ssfAttr sf) <> isVar (ssfAttr sf)

        staticFieldMeta :: Field -> String
        staticFieldMeta sf =
          staticlFieldAttr sf
            <> maybe mempty (\raw -> ",raw:" ++ showTreeSymbol raw) (ssfBaseRaw sf)
            <> ",objs:"
            <> show (Set.toList $ ssfObjects sf)

        dlabelAttr :: DynamicField -> String
        dlabelAttr dsf = attr (dsfAttr dsf) <> isVar (dsfAttr dsf) <> ",dynf"

        -- The tuple is (field name, field meta, field value)
        fields :: [(String, String, Tree)]
        fields =
          map
            ( \k ->
                maybe
                  (T.unpack k, "", mkBottomTree "not found")
                  (\sf -> (T.unpack k, staticFieldMeta sf, ssfValue sf))
                  (lookupStructField k s)
            )
            (stcOrdLabels s)
            ++ map
              ( \(k, lb) ->
                  (show (StructTASeg $ LetTASeg (TE.encodeUtf8 k)), printf ",r:%s" (show $ lbReferred lb), lbValue lb)
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
    let dfField = maybe [] (\v -> [(show DisjDefTASeg, mempty, v)]) (dsjDefault d)
        djFields = zipWith (\j v -> (show $ DisjRegTASeg j, mempty, v)) [0 ..] (dsjDisjuncts d)
     in consRep (symbol, printf "dis:%s" (show $ dsjDefIndexes d), consFields dfField ++ consFields djFields, [])
  TNAtomCnstr c ->
    consRep
      ( symbol
      , mempty
      , consFields
          [ ("atom", mempty, mkAtomTree (cnsAtom c))
          , ("validator", mempty, mkAtomTree $ String (T.pack $ show $ cnsValidator c))
          ]
      , []
      )
  TNRefCycle p -> consRep (symbol, printf "ref-cycle %s" (show p), [], [])
  TNMutable m -> case m of
    RegOp mut ->
      let
        args =
          if trboShowMutArgs opt
            then zipWith (\j v -> (show (MutArgTASeg j), mempty, v)) [0 ..] (toList $ ropArgs mut)
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
          , showRefArg
              (refArg ref)
              (\x -> listToMaybe $ catMaybes [T.unpack <$> rtrString x, show <$> rtrInt x])
              <> maybe mempty (\from -> ", from:" <> show from) (refOrigAddrs ref)
              <> (", vers:" <> maybe "N" show (refVers ref))
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
                    (show (MutArgTASeg j), if dstMarked v then ",*" else "", dstValue v)
                )
                [0 ..]
                (toList $ djoTerms d)
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
                (\j v -> (show (MutArgTASeg j), mempty, v))
                [0 ..]
                (toList $ ufConjuncts u)
            else []
        val = maybe mempty (\s -> [(show SubValTASeg, mempty, s)]) (ufValue u)
       in
        consRep (symbol, "", consFields (conjuncts ++ val), [])
    Itp itp ->
      let
        exprs =
          if trboShowMutArgs opt
            then
              zipWith
                (\j v -> (show (MutArgTASeg j), mempty, v))
                [0 ..]
                (toList $ itpExprs itp)
            else []
        val = maybe mempty (\s -> [(show SubValTASeg, mempty, s)]) (itpValue itp)
       in
        consRep (symbol, "", consFields (exprs ++ val), [])
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
    Itp _ -> "inter"
  TNCnstredVal _ -> "cnstred"
  TNBottom _ -> "_|_"
  TNTop -> "_"

showValueType :: (Env r s m) => Tree -> m String
showValueType t = case treeNode t of
  TNAtom a -> case a of
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