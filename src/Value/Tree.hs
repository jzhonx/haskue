{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Value.Tree where

import AST (exprToOneLinerStr)
import qualified AST
import Common (ErrorEnv)
import Control.Monad.Except (runExceptT)
import Data.Maybe (fromJust, isJust)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Exception (throwErrSt)
import GHC.Generics (Generic)
import Path (
  BlockTASeg (..),
  FieldPath (FieldPath),
  Selector (..),
  TASeg (..),
  TreeAddr,
  addrToList,
 )
import StringIndex (ShowWithTextIndexer (..), TextIndexerMonad, textToTextIndex)
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
  | TNStruct Struct
  | TNList List
  | TNDisj Disj
  | TNAtomCnstr AtomCnstr
  | -- | TNRefCycle is used to represent a reference cycle, which should be resolved in a field value node.
    TNRefCycle
  | -- | TNRefSubCycle represents the result of a field referencing its sub field.
    TNRefSubCycle TreeAddr
  | -- | TNNoVal is used to represent a reference that is copied from another expression but has no value
    -- yet.
    TNNoVal
  deriving (Generic)

data TreeValGenEnv
  = TGenOp Mutable
  | TGenImmutable
  deriving (Generic)

data EmbedType
  = ETNone
  | ETEnclosing
  | ETEmbedded !Int
  deriving (Eq, Show, Generic)

-- Some rules:
-- 1. If a node is a Mutable that contains references, then the node should not be supplanted to other places without
-- changing the dependencies.
-- 2. Evaluation is top-down. Evaluation do not go deeper unless necessary.
data Tree = Tree
  { treeNode :: TreeNode
  , treeExpr :: Maybe AST.Expression
  -- ^ treeExpr is the parsed expression.
  , valGenEnv :: TreeValGenEnv
  , isRecurClosed :: !Bool
  -- ^ isRecurClosed is used to indicate whether the sub-tree including itself is closed.
  , isRootOfSubTree :: !Bool
  -- ^ isRootOfSubTree is used to indicate whether the tree is the root of a sub-tree formed by parentheses.
  , isUnifiedWithRC :: !Bool
  -- ^ isUnifiedWithRC is used to indicate whether the tree has been unified with a reference cycle.
  , isSCyclic :: !Bool
  -- ^ isSCyclic is used to indicate whether the tree is cyclic.
  -- According to the spec,
  -- If a node a references an ancestor node, we call it and any of its field values a.f cyclic. So if a is cyclic, all
  -- of its descendants are also regarded as cyclic.
  , embType :: EmbedType
  -- ^ embType is used to indicate whether the tree is embedded in a struct. If it is, by convention, the first
  -- argument of a mutable should be the struct itself.
  , tmpSub :: Maybe Tree
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

pattern IsStruct :: Struct -> Tree
pattern IsStruct struct <- TN (TNStruct struct)

pattern IsFullStruct :: Struct -> Tree
pattern IsFullStruct struct <- TN (TNStruct struct@Struct{stcEmbedVal = Nothing})

pattern IsEmbedVal :: Tree -> Tree
pattern IsEmbedVal v <- TN (TNStruct Struct{stcEmbedVal = Just v})

pattern IsList :: List -> Tree
pattern IsList lst <- TN (TNList lst)

pattern IsDisj :: Disj -> Tree
pattern IsDisj d <- TN (TNDisj d)

pattern IsAtomCnstr :: AtomCnstr -> Tree
pattern IsAtomCnstr c <- TN (TNAtomCnstr c)

pattern IsRefCycle :: Tree
pattern IsRefCycle <- TN TNRefCycle

pattern IsNoVal :: Tree
pattern IsNoVal <- TN TNNoVal

pattern IsUnifiedWithRC :: Bool -> Tree
pattern IsUnifiedWithRC b <- Tree{isUnifiedWithRC = b}

pattern IsTGenOp :: Mutable -> Tree
pattern IsTGenOp mut <- Tree{valGenEnv = TGenOp mut}

pattern IsTGenImmutable :: Tree
pattern IsTGenImmutable <- Tree{valGenEnv = TGenImmutable}

pattern IsRef :: Mutable -> Reference -> Tree
pattern IsRef mut ref <- IsTGenOp mut@(MutOp (Ref ref))

pattern IsRegOp :: Mutable -> RegularOp -> Tree
pattern IsRegOp mut rop <- IsTGenOp mut@(MutOp (RegOp rop))

pattern IsSCycle :: Tree
pattern IsSCycle <- Tree{isSCyclic = True}

-- = TreeNode getters and setters =

setTN :: Tree -> TreeNode -> Tree
setTN t n = t{treeNode = n}

setExpr :: Tree -> Maybe AST.Expression -> Tree
setExpr t eM = t{treeExpr = eM}

setTValGenEnv :: TreeValGenEnv -> Tree -> Tree
setTValGenEnv f t = t{valGenEnv = f}

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
  TNRefSubCycle _ -> Just t
  TNNoVal -> Just t
  TNStruct _ -> Just t
  TNAtomCnstr c -> Just $ mkAtomTree c.value

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
    TNStruct _ -> Just v
    TNRefCycle -> Just v
    TNDisj d | Just df <- rtrDisjDefVal d -> rtrNonUnion df
    _ -> Nothing

-- | Retrieve the concrete value from the tree.
rtrConcrete :: Tree -> Maybe Tree
rtrConcrete t = do
  v <- rtrNonUnion t
  case v of
    IsAtom _ -> Just v
    -- There is only struct value after retrieving concrete value.
    IsStruct s -> if stcIsConcrete s then Just v else Nothing
    _ -> Nothing

rtrNonMut :: Tree -> Maybe Tree
rtrNonMut IsNoVal = Nothing
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
    IsStruct s
      | Just ev <- stcEmbedVal s -> rtrBottom ev
      | Just err <- stcPermErr s -> rtrBottom err
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
    IsStruct s -> Just s
    _ -> Nothing

-- | Convert the default disjuncts to a tree.
rtrDisjDefVal :: Disj -> Maybe Tree
rtrDisjDefVal d =
  let dfs = defDisjunctsFromDisj d
   in if
        | null dfs -> Nothing
        | length dfs == 1 -> Just (head dfs)
        | otherwise -> Just $ mkDisjTree $ emptyDisj{dsjDisjuncts = dfs}

isEmbedded :: Tree -> Bool
isEmbedded t = case embType t of
  ETEmbedded _ -> True
  _ -> False

-- = Helpers =

emptyTree :: Tree
emptyTree =
  Tree
    { treeNode = TNTop
    , valGenEnv = TGenImmutable
    , treeExpr = Nothing
    , isRecurClosed = False
    , isRootOfSubTree = False
    , isUnifiedWithRC = False
    , isSCyclic = False
    , embType = ETNone
    , tmpSub = Nothing
    }

makeTreeImmutable :: Tree -> Tree
makeTreeImmutable t = t{valGenEnv = TGenImmutable}

mkNewTree :: TreeNode -> Tree
mkNewTree n = emptyTree{treeNode = n}

mkNewTreeWithTGen :: TreeNode -> TreeValGenEnv -> Tree
mkNewTreeWithTGen n g = (mkNewTree n){valGenEnv = g}

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
mkMutableTree fn = (mkNewTree TNNoVal){valGenEnv = TGenOp fn}

mkListTree :: [Tree] -> Tree
mkListTree ts = mkNewTree (TNList $ List{lstSubs = ts})

mkStructTree :: Struct -> Tree
mkStructTree s = mkNewTree (TNStruct s)

singletonNoVal :: Tree
singletonNoVal = mkNewTree TNNoVal

-- | Create an index function node.
appendSelToRefTree :: Tree -> Tree -> Tree
appendSelToRefTree oprnd selArg = case oprnd of
  IsTGenOp mut@(MutOp (Ref ref)) ->
    mkMutableTree $ setMutOp (Ref $ ref{refArg = appendRefArg selArg (refArg ref)}) mut
  _ -> mkMutableTree $ withEmptyMutFrame $ Ref $ mkIndexRef (Seq.fromList [oprnd, selArg])

treesToFieldPath :: (TextIndexerMonad s m) => [Tree] -> m (Maybe FieldPath)
treesToFieldPath ts = do
  xs <- mapM treeToSel ts
  return $ FieldPath <$> sequence xs

treeToSel :: (TextIndexerMonad s m) => Tree -> m (Maybe Selector)
treeToSel t = case treeNode t of
  TNAtom a
    | (String s) <- a -> do
        tIdx <- textToTextIndex s
        return $ Just (StringSel tIdx)
    | (Int j) <- a -> return $ Just (IntSel $ fromIntegral j)
  -- If a disjunct has a default, then we should try to use the default.
  TNDisj dj | isJust (rtrDisjDefVal dj) -> treeToSel (fromJust $ rtrDisjDefVal dj)
  _ -> return Nothing

addrToTrees :: (TextIndexerMonad s m) => TreeAddr -> m (Maybe [Tree])
addrToTrees p = do
  xs <- mapM selToTree (addrToList p)
  return $ sequence xs
 where
  selToTree sel = case sel of
    (BlockTASeg (StringTASeg s)) -> do
      str <- tshow s
      return $ Just $ mkAtomTree (String (T.pack str))
    IndexTASeg j -> return $ Just $ mkAtomTree (Int (fromIntegral j))
    _ -> return Nothing

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
oneLinerStringOfTree :: (TextIndexerMonad s m) => Tree -> m String
oneLinerStringOfTree t = do
  let m = buildASTExprDebug t
  e <- runExceptT m
  case e of
    Left err -> return err
    Right expr -> return $ exprToOneLinerStr expr

invalidateMutable :: Tree -> Tree
invalidateMutable t@(IsTGenOp _) = t{treeNode = TNNoVal}
invalidateMutable t = t

showTreeSymbol :: Tree -> String
showTreeSymbol t = case treeNode t of
  TNAtom _ -> "a"
  TNBounds _ -> "bds"
  TNStruct{} -> "{}"
  TNList{} -> "[]"
  TNDisj{} -> "dj"
  TNAtomCnstr{} -> "Cnstr"
  TNRefCycle -> "RC"
  TNRefSubCycle _ -> "RSC"
  TNBottom _ -> "_|_"
  TNTop -> "_"
  TNNoVal -> "noval"

showValueType :: (ErrorEnv m) => Tree -> m String
showValueType t = case treeNode t of
  TNAtom a -> case a of
    String _ -> return "string"
    Int _ -> return "int"
    Float _ -> return "float"
    Bool _ -> return "bool"
    Null -> return "null"
  TNBounds b -> return $ show b
  TNBottom _ -> return "_|_"
  TNStruct _ -> return "struct"
  TNList _ -> return "list"
  TNTop -> return "_"
  _ -> throwErrSt $ "not a value type: " ++ showTreeSymbol t