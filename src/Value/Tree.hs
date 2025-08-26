{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Value.Tree where

import AST (exprToOneLinerStr)
import qualified AST
import Common (EnvIO, ErrorEnv)
import Control.Monad (foldM)
import Control.Monad.Except (runExcept)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import Path (
  BlockTASeg (..),
  FieldPath (FieldPath),
  Selector (..),
  TASeg (..),
  TreeAddr,
  addrToList,
 )
import Text.Printf (printf)
import Value.Atom
import Value.Block
import Value.Bottom
import Value.Bounds
import Value.Constraint
import Value.Disj
import Value.List
import Value.Mutable
import Value.Reference
import {-# SOURCE #-} Value.Util.BuildASTExpr (buildASTExprDebug)

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
  | -- | TNRefCycle is used to represent a reference cycle, which should be resolved in a field value node.
    TNRefCycle
  | -- | TNUnifyWithRC represents the result of a unification operation with a reference cycle.
    -- It contains the address of the target pointed by the reference cycle and the tree value.
    TNUnifyWithRC Tree
  | -- | TNRefCycle represents the result of a field referencing its sub field.
    TNRefSubCycle TreeAddr
  | TNMutable Mutable
  | -- | TNNoValRef is used to represent a reference that is copied from another expression but has no value
    -- yet.
    TNNoValRef
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

instance Show Tree where
  show = oneLinerStringOfCurTreeState

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

pattern IsMutable :: Mutable -> Tree
pattern IsMutable mut <- TN (TNMutable mut)

pattern IsRef :: Mutable -> Reference -> Tree
pattern IsRef mut ref <- IsMutable mut@(MutOp (Ref ref))

pattern IsRefCycle :: Tree
pattern IsRefCycle <- TN TNRefCycle

pattern IsUnifyWithRC :: Tree
pattern IsUnifyWithRC <- TN (TNUnifyWithRC _)

pattern IsRegOp :: Mutable -> RegularOp -> Tree
pattern IsRegOp mut rop <- IsMutable mut@(MutOp (RegOp rop))

{- | Descend into the tree with the given segment.

This should only be used by TreeCursor.
-}
subTree :: (HasCallStack) => TASeg -> Tree -> Maybe Tree
subTree seg t = case (seg, treeNode t) of
  (RootTASeg, _) -> Just t
  (BlockTASeg s, TNBlock blk@(IsBlockStruct struct)) -> case s of
    StringTASeg name
      | Just sf <- lookupStructField (TE.decodeUtf8 name) struct -> Just $ ssfValue sf
    PatternTASeg i j -> (if j == 0 then scsPattern else scsValue) <$> blkCnstrs blk IntMap.!? i
    DynFieldTASeg i j ->
      (if j == 0 then dsfLabel else dsfValue) <$> blkDynFields blk IntMap.!? i
    LetTASeg name
      | Just lb <- lookupBlockLet (TE.decodeUtf8 name) blk -> Just (lbValue lb)
    EmbedTASeg i -> embValue <$> blkEmbeds blk IntMap.!? i
    _ -> Nothing
  (SubValTASeg, TNBlock (IsBlockEmbed ev)) -> Just ev
  (IndexTASeg i, TNList vs) -> lstSubs vs `indexList` i
  (_, TNMutable mut)
    | MutArgTASeg i <- seg -> getMutArgs mut Seq.!? i
    | SubValTASeg <- seg -> getMutVal mut
  (_, TNDisj d)
    | DisjDefTASeg <- seg -> dsjDefault d
    | DisjRegTASeg i <- seg -> dsjDisjuncts d `indexList` i
  _ -> Nothing

{- | Set the sub tree with the given segment and new tree.

It ensures that the version of the parent node is always greater than or equal to any of its children.
-}
setSubTree :: (ErrorEnv m) => TASeg -> Tree -> Tree -> m Tree

-- | If the segment is EphemeralTASeg, we do not set the sub-tree.
setSubTree EphemeralTASeg _ parT = return parT
setSubTree seg subT@Tree{treeVersion = vers} parT = do
  n <- case (seg, treeNode parT) of
    (BlockTASeg s, TNBlock blk) -> updateParStruct blk s
    (SubValTASeg, TNBlock blk) -> return $ TNBlock blk{blkValue = BlockEmbed subT}
    (IndexTASeg i, TNList vs) ->
      let subs = lstSubs vs
          l = TNList $ vs{lstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return l
    (_, TNMutable mut)
      | MutArgTASeg i <- seg -> return $ TNMutable $ updateMutArg i subT mut
      | SubValTASeg <- seg -> return . TNMutable $ setMutVal (Just subT) mut
    (_, TNDisj d)
      | DisjDefTASeg <- seg -> return (TNDisj $ d{dsjDefault = dsjDefault d})
      | DisjRegTASeg i <- seg ->
          return (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)})
    (RootTASeg, _) -> throwErrSt "setSubTreeT: RootTASeg is not allowed"
    _ -> throwErrSt insertErrMsg
  return $ parT{treeNode = n, treeVersion = max vers (treeVersion parT)}
 where
  structToTN :: Struct -> Block -> TreeNode
  structToTN s blk = TNBlock blk{blkValue = BlockStruct s}

  updateParStruct :: (ErrorEnv m) => Block -> BlockTASeg -> m TreeNode
  updateParStruct parBlock@(IsBlockStruct parStruct) labelSeg
    -- The label segment should already exist in the parent struct. Otherwise the description of the field will not be
    -- found.
    | StringTASeg name <- labelSeg
    , Just field <- lookupStructField (TE.decodeUtf8 name) parStruct =
        let
          newField = subT `updateFieldValue` field
          newStruct = updateStructField (TE.decodeUtf8 name) newField parStruct
         in
          return (structToTN newStruct parBlock)
    | LetTASeg name <- labelSeg
    , Just _ <- lookupBlockLet (TE.decodeUtf8 name) parBlock =
        let
          newBlock = updateBlockLet (TE.decodeUtf8 name) subT parBlock
         in
          return (TNBlock newBlock)
    | PatternTASeg i j <- labelSeg =
        let
          psf = blkCnstrs parBlock IntMap.! i
          newPSF = if j == 0 then psf{scsPattern = subT} else psf{scsValue = subT}
         in
          return $ TNBlock parBlock{blkCnstrs = IntMap.insert i newPSF (blkCnstrs parBlock)}
    | DynFieldTASeg i j <- labelSeg =
        let
          pends = blkDynFields parBlock
          psf = pends IntMap.! i
          newPSF = if j == 0 then psf{dsfLabel = subT} else psf{dsfValue = subT}
         in
          return $ TNBlock parBlock{blkDynFields = IntMap.insert i newPSF (blkDynFields parBlock)}
    | EmbedTASeg i <- labelSeg =
        let
          oldEmbeds = blkEmbeds parBlock
          newEmbed = (oldEmbeds IntMap.! i){embValue = subT}
         in
          return $ TNBlock parBlock{blkEmbeds = IntMap.insert i newEmbed oldEmbeds}
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

{- | Retrieve the deterministic value from the tree.

A deterministic value is a value that can not be interpreted as multiple kinds of values.

For example, a mutalbe that has cached value is not deterministic, because it contains two kinds of values: the cached
value and the mutable value itself.
-}
rtrDeterministic :: Tree -> Maybe Tree
rtrDeterministic t = case treeNode t of
  TNAtom _ -> Just t
  TNBottom _ -> Just t
  TNTop -> Just t
  TNBounds _ -> Just t
  TNList _ -> Just t
  TNDisj _ -> Just t
  TNRefCycle -> Just t
  TNUnifyWithRC _ -> Just t
  TNRefSubCycle _ -> Just t
  TNNoValRef -> Just t
  TNBlock block
    | IsBlockEmbed ev <- block -> rtrDeterministic ev
    | otherwise -> Just t
  TNAtomCnstr c -> Just $ mkAtomTree (cnsAtom c)
  TNMutable mut -> getMutVal mut >>= rtrDeterministic

{- | Retrieve the value of non-union type.

Union type represents an incomplete value, such as a disjunction or bounds.
-}
rtrNonUnion :: Tree -> Maybe Tree
rtrNonUnion t = do
  v <- rtrDeterministic t
  case treeNode v of
    TNAtom _ -> Just v
    TNBottom _ -> Just v
    TNTop -> Just v
    TNList _ -> Just v
    TNBlock _ -> Just v
    TNRefCycle -> Just v
    TNUnifyWithRC _ -> Just v
    TNDisj d | Just df <- dsjDefault d -> rtrNonUnion df
    _ -> Nothing

-- | Retrieve the concrete value from the tree.
rtrConcrete :: Tree -> Maybe Tree
rtrConcrete t = do
  v <- rtrNonUnion t
  case v of
    IsAtom _ -> Just v
    -- There is only struct value after retrieving concrete value.
    IsBlock (IsBlockStruct s) -> if stcIsConcrete s then Just v else Nothing
    _ -> Nothing

rtrNonMut :: Tree -> Maybe Tree
rtrNonMut (IsMutable mut) = getMutVal mut >>= rtrNonMut
rtrNonMut t = return t

rtrAtom :: Tree -> Maybe Atom
rtrAtom t = do
  v <- rtrNonUnion t
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
  v <- rtrNonUnion t
  case v of
    IsBottom b -> Just b
    _ -> Nothing

rtrBounds :: Tree -> Maybe Bounds
rtrBounds t = do
  v <- rtrDeterministic t
  case v of
    IsBounds b -> Just b
    _ -> Nothing

{- | Get the disjunction from the tree.

It stops at the first disjunction found. It does not go deeper to the default value of the disjunction.
-}
rtrDisj :: Tree -> Maybe Disj
rtrDisj t = do
  v <- rtrDeterministic t
  case v of
    IsDisj d -> Just d
    _ -> Nothing

rtrList :: Tree -> Maybe List
rtrList t = do
  v <- rtrNonUnion t
  case v of
    IsList l -> Just l
    _ -> Nothing

rtrStruct :: Tree -> Maybe Struct
rtrStruct t = do
  v <- rtrNonUnion t
  case v of
    IsBlock (IsBlockStruct struct) -> Just struct
    _ -> Nothing

rtrBlock :: Tree -> Maybe Block
rtrBlock t = do
  v <- rtrNonUnion t
  case v of
    IsBlock b -> Just b
    _ -> Nothing

-- = Traversal =

-- | Generate a list of sub-trees that have values to reduce, not the values that have been reduced.
subNodes :: Tree -> [(TASeg, Tree)]
subNodes t = case treeNode t of
  TNBlock blk@(IsBlockStruct struct) ->
    [(BlockTASeg $ StringTASeg (TE.encodeUtf8 s), ssfValue field) | (s, field) <- Map.toList (stcFields struct)]
      ++ [(BlockTASeg $ PatternTASeg i 0, scsPattern c) | (i, c) <- IntMap.toList $ blkCnstrs blk]
      ++ [(BlockTASeg $ DynFieldTASeg i 0, dsfLabel dsf) | (i, dsf) <- IntMap.toList $ blkDynFields blk]
  TNList l -> [(IndexTASeg i, v) | (i, v) <- zip [0 ..] (lstSubs l)]
  TNMutable mut -> [(MutArgTASeg i, v) | (i, v) <- zip [0 ..] (toList $ getMutArgs mut)]
  TNDisj d ->
    maybe [] (\x -> [(DisjDefTASeg, x)]) (dsjDefault d)
      ++ [(DisjRegTASeg i, v) | (i, v) <- zip [0 ..] (dsjDisjuncts d)]
  _ -> []

-- | TODO: comprehension struct
rawNodes :: Tree -> [(TASeg, Tree)]
rawNodes t = case treeNode t of
  TNBlock block ->
    [(BlockTASeg $ PatternTASeg i 1, scsValue c) | (i, c) <- IntMap.toList $ blkCnstrs block]
      ++ [(BlockTASeg $ DynFieldTASeg i 1, dsfValue dsf) | (i, dsf) <- IntMap.toList $ blkDynFields block]
      ++ [(BlockTASeg $ LetTASeg (TE.encodeUtf8 s), lbValue lb) | (s, lb) <- Map.toList $ blkBindings block]
      ++ [(BlockTASeg $ EmbedTASeg i, embValue emb) | (i, emb) <- IntMap.toList $ blkEmbeds block]
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

mkAtomCnstrTree :: AtomCnstr -> Tree
mkAtomCnstrTree c = mkNewTree (TNAtomCnstr c)

mkBottomTree :: String -> Tree
mkBottomTree msg = mkNewTree (TNBottom $ Bottom{btmMsg = msg})

mkBoundsTree :: Bounds -> Tree
mkBoundsTree bs = mkNewTree (TNBounds bs)

mkBoundsTreeFromList :: [Bound] -> Tree
mkBoundsTreeFromList bs = mkBoundsTree (Bounds{bdsList = bs})

mkCnstrTree :: Atom -> Tree -> Tree
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
mkStructTree s = mkNewTree (TNBlock (emptyBlock{blkValue = BlockStruct s}))

-- | Create an index function node.
appendSelToRefTree :: Tree -> Tree -> Tree
appendSelToRefTree oprnd selArg = case treeNode oprnd of
  TNMutable mut@(MutOp (Ref ref)) ->
    mkMutableTree $ setMutOp (Ref $ ref{refArg = appendRefArg selArg (refArg ref)}) mut
  _ -> mkMutableTree $ withEmptyMutFrame $ Ref $ mkIndexRef (Seq.fromList [oprnd, selArg])

treesToFieldPath :: [Tree] -> Maybe FieldPath
treesToFieldPath ts = FieldPath <$> mapM treeToSel ts

treeToSel :: Tree -> Maybe Selector
treeToSel t = case rtrNonMut t of
  -- TODO: Think about changing mutval.
  Just v -> concreteToSel v
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
    BlockTASeg (StringTASeg s) -> Just $ mkAtomTree (String (TE.decodeUtf8 s))
    IndexTASeg j -> Just $ mkAtomTree (Int (fromIntegral j))
    _ -> Nothing

-- built-in functions
builtinMutableTable :: [(String, Tree)]
builtinMutableTable =
  [
    ( "close"
    , mkMutableTree $
        withEmptyMutFrame $
          RegOp $
            -- built-in close does not recursively close the struct.
            emptyRegularOp
              { ropName = "close"
              , ropArgs = Seq.fromList [mkNewTree TNTop]
              , ropOpType = CloseFunc
              }
    )
  ]

-- | Create a one-liner string representation of the snapshot of the tree.
oneLinerStringOfCurTreeState :: Tree -> String
oneLinerStringOfCurTreeState t =
  let astE = do
        s <- snapshotTree t
        buildASTExprDebug s
   in case runExcept astE of
        Left err -> error (show err)
        Right expr -> exprToOneLinerStr expr

-- | Create a snapshot of the tree by consolidating all mutable values to their cached values.
snapshotTree :: (ErrorEnv m) => Tree -> m Tree
snapshotTree t = case treeNode t of
  TNMutable mut
    | Just v <- getMutVal mut -> snapshotTree v
  _ -> do
    let subTs = subNodes t ++ rawNodes t
    newSubTs <-
      mapM
        ( \(seg, st) -> do
            r <- snapshotTree st
            return (seg, r)
        )
        subTs
    foldM
      (\acc (seg, st) -> setSubTree seg st acc)
      t
      newSubTs

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNAtom _ -> "a"
  TNBounds _ -> "bds"
  TNBlock{} -> "{}"
  TNList{} -> "[]"
  TNDisj{} -> "dj"
  TNAtomCnstr{} -> "Cnstr"
  TNRefCycle -> "RC"
  TNUnifyWithRC _ -> "URC"
  TNRefSubCycle _ -> "RSC"
  TNMutable (Mutable op _) -> case op of
    RegOp _ -> "fn"
    Ref _ -> "ref"
    Compreh _ -> "compreh"
    DisjOp _ -> "disjoin"
    UOp _ -> "unify"
    Itp _ -> "inter"
  TNBottom _ -> "_|_"
  TNTop -> "_"
  TNNoValRef -> "pref"

showValueType :: (EnvIO r s m) => Tree -> m String
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