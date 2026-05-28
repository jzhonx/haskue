{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Value.Val where

import Control.Monad.Except (runExcept)
import Control.Monad.Identity
import Control.Monad.State.Strict (gets, modify')
import qualified Data.ByteString.Char8 as BC
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromJust, isJust)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Env (ErrorEnv)
import Exception (throwErrSt)
import Feature (
  Selector (..),
  ValAddr,
  appendSeg,
  mkStringFeature,
  universalValAddr,
 )
import GHC.Generics (Generic)
import StringIndex (HasTextIndexer (..), TextIndex, TextIndexerMonad, getTextIndexer, strToTextIndex, textToTextIndex)
import Syntax.AST (exprToOneLinerStr)
import qualified Syntax.AST as AST
import Value.Atom
import Value.Bottom
import Value.Bounds
import Value.Disj
import {-# SOURCE #-} Value.Export.AST (buildExprDebug)
import Value.Func
import Value.List
import Value.Op
import Value.Reference
import Value.Struct

class VTerm a where
  vtmapT :: (ValAddr -> VTermNode -> VTermNode) -> ValAddr -> a -> a
  vtmapT f p v = runIdentity $ vtmapM (\np nv -> return $ f np nv) p v
  vtmapQ :: (ValAddr -> VTermNode -> r) -> ValAddr -> a -> [r]

  -- It does mapM on the immediate children of the term.
  -- If there is no child, no mapping is performed and the original term is returned.
  vtmapM :: (Monad m) => (ValAddr -> VTermNode -> m VTermNode) -> ValAddr -> a -> m a

data VTermNode
  = VTVal Val
  | VTOp Op
  | VTVNode VNode
  deriving (Generic)

pattern IsRef :: Op -> Reference -> VTermNode
pattern IsRef op ref <- VTOp op@(Ref ref)

vtValOr :: (Val -> a) -> a -> VTermNode -> a
vtValOr f _ (VTVal vn) = f vn
vtValOr _ a _ = a

vtOpOr :: (Op -> a) -> a -> VTermNode -> a
vtOpOr f _ (VTOp op) = f op
vtOpOr _ a _ = a

vtVNodeOr :: (VNode -> a) -> a -> VTermNode -> a
vtVNodeOr f _ (VTVNode v) = f v
vtVNodeOr _ a _ = a

applyAddrFOnVN :: (Applicative f) => (ValAddr -> VNode -> f VNode) -> ValAddr -> VTermNode -> f VTermNode
applyAddrFOnVN f p (VTVNode v) = VTVNode <$> f p v
applyAddrFOnVN _ _ x = pure x

applyAddrFOnVal :: (Applicative f) => (ValAddr -> Val -> f Val) -> ValAddr -> VTermNode -> f VTermNode
applyAddrFOnVal f p (VTVal v) = VTVal <$> f p v
applyAddrFOnVal _ _ x = pure x

-- | Val represents a tree structure that contains values.
data Val
  = -- | VAtom contains an atom value.
    VAtom Atom
  | VBottom Bottom
  | VBounds Bounds
  | VTop
  | VStruct Struct
  | VList List
  | VDisj Disj
  | VUnknown
  | -- | VFuncAddr is a variant of Unknown but it represents a function address.
    VFuncAddr ValAddr
  deriving (Generic)

data Constraint
  = ValCnstr Val
  | OpCnstr Op
  | StructEmbedCnstr ConstraintSeq
  deriving (Generic)

type ConstraintSeq = Seq.Seq Constraint

data ConstraintsSet = ConstraintsSet
  { static :: Seq.Seq Constraint
  , dynamic :: IntMap.IntMap ConstraintSeq
  , allResolved :: !Bool
  }
  deriving (Generic)

emptyConstraintsSet :: ConstraintsSet
emptyConstraintsSet = ConstraintsSet{static = Seq.empty, dynamic = IntMap.empty, allResolved = False}

mergeConstraintsSet :: ConstraintsSet -> ConstraintsSet -> ConstraintsSet
mergeConstraintsSet c1 c2 =
  ConstraintsSet
    { static = static c1 Seq.>< static c2
    , dynamic = IntMap.union (dynamic c1) (dynamic c2)
    , allResolved = allResolved c1 && allResolved c2
    }

hasEmptyCnstrs :: ConstraintsSet -> Bool
hasEmptyCnstrs c = Seq.null (static c) && IntMap.null (dynamic c)

removeDynCnstr :: Int -> ConstraintsSet -> ConstraintsSet
removeDynCnstr idx c = c{dynamic = IntMap.delete idx (dynamic c)}

insertDynCnstr :: Int -> ConstraintSeq -> ConstraintsSet -> ConstraintsSet
insertDynCnstr idx v c = c{dynamic = IntMap.insert idx v (dynamic c)}

memberDynCnstr :: Int -> ConstraintsSet -> Bool
memberDynCnstr idx c = IntMap.member idx (dynamic c)

data VNode = VNode
  { value :: Val
  , version :: !Int
  , origExpr :: Maybe AST.Expression
  -- ^ origExpr is the parsed expression.
  -- If the op is not Nothing, then origExpr represents the op expression.
  -- If the op is Nothing, then origExpr represents the value expression.
  , constraints :: ConstraintsSet
  }
  deriving (Generic)

pattern VNVal :: Val -> VNode
pattern VNVal tn <- VNode{value = tn}

pattern IsAtom :: Atom -> VNode
pattern IsAtom a <- VNVal (VAtom a)

pattern IsBottom :: Bottom -> VNode
pattern IsBottom b <- VNVal (VBottom b)

pattern IsBounds :: Bounds -> VNode
pattern IsBounds b <- VNVal (VBounds b)

pattern IsStruct :: Struct -> VNode
pattern IsStruct struct <- VNVal (VStruct struct)

pattern IsEmbedVal :: Val -> Val
pattern IsEmbedVal v <- (VStruct Struct{stcEmbedVal = Just v})

pattern IsList :: List -> VNode
pattern IsList lst <- VNVal (VList lst)

pattern IsDisj :: Disj -> VNode
pattern IsDisj d <- VNVal (VDisj d)

pattern IsUnknown :: VNode
pattern IsUnknown <- VNVal VUnknown

pattern StaticConstraints :: Seq.Seq Constraint -> VNode
pattern StaticConstraints cs <- VNode{constraints = ConstraintsSet{static = cs}}

pattern IsValSoleOp :: Op -> VNode
pattern IsValSoleOp op <- StaticConstraints (OpCnstr op Seq.:<| Seq.Empty)

-- = Val getters and setters =

setVNodeValue :: Val -> VNode -> VNode
setVNodeValue n v = v{value = n}

setExpr :: Maybe AST.Expression -> VNode -> VNode
setExpr eM v = v{origExpr = eM}

mapConstraints :: (ConstraintsSet -> ConstraintsSet) -> VNode -> VNode
mapConstraints f v = v{constraints = f (constraints v)}

removeConstraints :: VNode -> VNode
removeConstraints t = t{constraints = emptyConstraintsSet}

appendStaticCnstrs :: Seq.Seq Constraint -> VNode -> VNode
appendStaticCnstrs c v = v{constraints = (constraints v){static = static (constraints v) Seq.>< c}}

{- | Retrieve the value of non-union type.

Union type represents an incomplete value, such as a disjunction or bounds.
-}
rtrNonUnion :: Val -> Maybe Val
rtrNonUnion v = do
  case v of
    VAtom _ -> Just v
    VBottom _ -> Just v
    VTop -> Just v
    VList _ -> Just v
    VStruct _ -> Just v
    VDisj d | Just df <- rtrDisjDefVal d -> rtrNonUnion df
    _ -> Nothing

rtrValue :: Val -> Maybe Val
rtrValue VUnknown = Nothing
rtrValue t = return t

rtrAtom :: Val -> Maybe Atom
rtrAtom t = do
  v <- rtrNonUnion t
  case v of
    VAtom a -> Just a
    _ -> Nothing

rtrString :: Val -> Maybe BC.ByteString
rtrString (rtrAtom -> Just (String s)) = Just s
rtrString _ = Nothing

rtrInt :: Val -> Maybe Int
rtrInt (rtrAtom -> Just (Int i)) = Just (fromIntegral i)
rtrInt _ = Nothing

rtrBool :: Val -> Maybe Bool
rtrBool (rtrAtom -> Just (Bool b)) = Just b
rtrBool _ = Nothing

rtrFloat :: Val -> Maybe Float
rtrFloat (rtrAtom -> Just (Float f)) = Just (fromRational (toRational f))
rtrFloat _ = Nothing

rtrBottom :: Val -> Maybe Bottom
rtrBottom t = do
  v <- rtrNonUnion t
  case v of
    VBottom b -> Just b
    VStruct s
      | Just ev <- stcEmbedVal s -> rtrBottom ev
      | Just err <- stcPermErr s -> Just err
    _ -> Nothing

rtrBounds :: VNode -> Maybe Bounds
rtrBounds v = case v of
  IsBounds b -> Just b
  _ -> Nothing

{- | Get the disjunction from the tree.

It stops at the first disjunction found. It does not go deeper to the default value of the disjunction.
-}
rtrDisj :: Val -> Maybe Disj
rtrDisj v = case v of
  VDisj d -> Just d
  _ -> Nothing

rtrList :: Val -> Maybe List
rtrList t = do
  v <- rtrNonUnion t
  case v of
    VList l -> Just l
    _ -> Nothing

rtrStruct :: Val -> Maybe Struct
rtrStruct t = do
  v <- rtrNonUnion t
  case v of
    VStruct s -> Just s
    _ -> Nothing

-- | Convert the default disjuncts to a tree.
rtrDisjDefVal :: Disj -> Maybe Val
rtrDisjDefVal d =
  let dfs = defDisjunctsFromDisj d
   in if
        | null dfs -> Nothing
        | length dfs == 1 -> Just (head dfs)
        | otherwise -> Just $ VDisj $ emptyDisj{dsjDisjuncts = Seq.fromList dfs}

-- = Helpers =

emptyVNode :: VNode
emptyVNode =
  VNode
    { value = VUnknown
    , version = 0
    , origExpr = Nothing
    , constraints = emptyConstraintsSet
    }

mkValVN :: Val -> VNode
mkValVN n = emptyVNode{value = n}

mkAtomVN :: Atom -> VNode
mkAtomVN a = mkValVN (VAtom a)

mkBottomVN :: String -> VNode
mkBottomVN msg = mkValVN (VBottom $ Bottom{btmMsg = msg})

mkBottomVal :: String -> Val
mkBottomVal msg = VBottom $ Bottom{btmMsg = msg}

mkBoundsVN :: Bounds -> VNode
mkBoundsVN bs = mkValVN (VBounds bs)

mkBoundsVNFromList :: [Bound] -> VNode
mkBoundsVNFromList bs = mkBoundsVN (Bounds{bdsList = bs})

mkBottomValueFromList :: [Bound] -> Val
mkBottomValueFromList bs = VBounds (Bounds{bdsList = bs})

mkDisjVN :: Disj -> VNode
mkDisjVN d = mkValVN (VDisj d)

mkOpVN :: Op -> VNode
mkOpVN fn = emptyVNode{constraints = emptyConstraintsSet{static = Seq.singleton (OpCnstr fn)}}

mkListVN :: [VNode] -> [VNode] -> VNode
mkListVN x y = mkValVN (VList $ mkList x y)

mkStructVN :: Struct -> VNode
mkStructVN s = mkValVN (VStruct s)

mkValCnstrVN :: Val -> VNode
mkValCnstrVN n = emptyVNode{constraints = emptyConstraintsSet{static = Seq.singleton (ValCnstr n)}}

mergeValCnstrs :: [VNode] -> VNode
mergeValCnstrs vs =
  let
    mergedStatic = foldl (\acc v -> acc Seq.>< v.constraints.static) Seq.empty vs
    mergedDynamic = foldl (\acc v -> IntMap.union acc (dynamic $ constraints v)) IntMap.empty vs
   in
    emptyVNode{constraints = emptyConstraintsSet{static = mergedStatic, dynamic = mergedDynamic}}

vnToSel :: (TextIndexerMonad s m) => VNode -> m (Maybe Selector)
vnToSel t = case value t of
  VAtom a
    | (String s) <- a -> do
        tIdx <- textToTextIndex s
        return $ Just (StringSel tIdx)
    | (Int j) <- a -> return $ Just (IntSel $ fromIntegral j)
  -- If a disjunct has a default, then we should try to use the default.
  VDisj dj | isJust (rtrDisjDefVal dj) -> vnToSel (mkValVN $ fromJust $ rtrDisjDefVal dj)
  _ -> return Nothing

-- | Create a one-liner string representation of the snapshot of the tree.
oneLinerStringOfVNode :: (TextIndexerMonad s m) => VNode -> m T.Text
oneLinerStringOfVNode t = do
  tier <- gets getTextIndexer
  let m = buildExprDebug t tier
      e = runExcept m
  case e of
    Left err -> return $ T.pack err
    Right (expr, newTier) -> do
      modify' $ setTextIndexer newTier
      return $ T.pack $ exprToOneLinerStr expr

showValType :: Val -> String
showValType t = case t of
  VAtom _ -> "atom"
  VBounds _ -> "bds"
  VStruct{} -> "struct"
  VList{} -> "list"
  VDisj{} -> "disj"
  VBottom _ -> "_|_"
  VTop -> "_"
  VUnknown -> "unknown"
  VFuncAddr _ -> "fnAddr"

showValueType :: (ErrorEnv m) => Val -> m String
showValueType t = case t of
  VAtom a -> case a of
    String _ -> return "string"
    Int _ -> return "int"
    Float _ -> return "float"
    Bool _ -> return "bool"
    Null -> return "null"
  VBounds b -> return $ show b
  VBottom _ -> return "_|_"
  VStruct _ -> return "struct"
  VList _ -> return "list"
  VTop -> return "_"
  _ -> throwErrSt $ "not a value type: " ++ showValType t

builtinValues :: (TextIndexerMonad s m) => m [(TextIndex, Val)]
builtinValues = do
  let builtins =
        ("_", VTop)
          : map (\b -> (show b, VBounds $ Bounds{bdsList = [BdType b]})) [minBound :: BdType .. maxBound :: BdType]
  mapM f builtins
 where
  f (k, v) = do
    nameTI <- strToTextIndex k
    return (nameTI, v)

-- | built-in functions
builtinFuncAddrTable :: (TextIndexerMonad s m) => m [(TextIndex, ValAddr)]
builtinFuncAddrTable = do
  let builtins = ["close"]
  mapM gen builtins
 where
  gen name = do
    nameTI <- strToTextIndex name
    return (nameTI, appendSeg universalValAddr (mkStringFeature nameTI))