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
  LabelType (..),
  Selector (..),
  ValAddr,
  addrToList,
  fetchIndex,
  fetchLabelType,
  getTextFromFeature,
 )
import GHC.Generics (Generic)
import StringIndex (HasTextIndexer (..), TextIndexerMonad, getTextIndexer, textToTextIndex)
import Syntax.AST (exprToOneLinerStr)
import qualified Syntax.AST as AST
import Value.Atom
import Value.Bottom
import Value.Bounds
import Value.Disj
import {-# SOURCE #-} Value.Export.AST (buildExprDebug)
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

applyAddrFOnVal :: (Applicative f) => (ValAddr -> VNode -> f VNode) -> ValAddr -> VTermNode -> f VTermNode
applyAddrFOnVal f p (VTVNode v) = VTVNode <$> f p v
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
  | -- | VNoVal is used to represent a reference that is copied from another expression but has no value
    -- yet.
    VNoVal
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
  , origExpr :: Maybe AST.Expression
  -- ^ origExpr is the parsed expression.
  -- If the op is not Nothing, then origExpr represents the op expression.
  -- If the op is Nothing, then origExpr represents the value expression.
  , constraints :: ConstraintsSet
  -- TODO: Feature
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

pattern IsTop :: VNode
pattern IsTop <- VNVal VTop

pattern IsStruct :: Struct -> VNode
pattern IsStruct struct <- VNVal (VStruct struct)

pattern IsFullStruct :: Struct -> VNode
pattern IsFullStruct struct <- VNVal (VStruct struct@Struct{stcEmbedVal = Nothing})

pattern IsEmbedVal :: Val -> Val
pattern IsEmbedVal v <- (VStruct Struct{stcEmbedVal = Just v})

pattern IsList :: List -> VNode
pattern IsList lst <- VNVal (VList lst)

pattern IsDisj :: Disj -> VNode
pattern IsDisj d <- VNVal (VDisj d)

pattern IsNoVal :: VNode
pattern IsNoVal <- VNVal VNoVal

pattern StaticConstraints :: Seq.Seq Constraint -> VNode
pattern StaticConstraints cs <- VNode{constraints = ConstraintsSet{static = cs}}

pattern IsValSoleOp :: Op -> VNode
pattern IsValSoleOp op <- StaticConstraints (OpCnstr op Seq.:<| Seq.Empty)

pattern IsValImmutable :: VNode
pattern IsValImmutable <- VNode{constraints = ConstraintsSet{static = Seq.Empty}}

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

-- | Retrieve the concrete value from the tree.
rtrConcrete :: Val -> Maybe Val
rtrConcrete t = do
  v <- rtrNonUnion t
  case v of
    VAtom _ -> Just v
    -- There is only struct value after retrieving concrete value.
    VStruct s -> if stcIsConcrete s then Just v else Nothing
    _ -> Nothing

rtrValue :: Val -> Maybe Val
rtrValue VNoVal = Nothing
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
        | length dfs == 1 -> Just (value $ head dfs)
        | otherwise -> Just $ VDisj $ emptyDisj{dsjDisjuncts = Seq.fromList dfs}

-- = Helpers =

emptyVNode :: VNode
emptyVNode =
  VNode
    { value = VNoVal
    , origExpr = Nothing
    , constraints = emptyConstraintsSet
    }

mkValVN :: Val -> VNode
mkValVN n = emptyVNode{value = n}

mkAtomVN :: Atom -> VNode
mkAtomVN a = mkValVN (VAtom a)

mkBottomVal :: String -> VNode
mkBottomVal msg = mkValVN (VBottom $ Bottom{btmMsg = msg})

mkBoundsVal :: String -> Val
mkBoundsVal msg = VBottom $ Bottom{btmMsg = msg}

mkBoundsVN :: Bounds -> VNode
mkBoundsVN bs = mkValVN (VBounds bs)

mkBoundsVNFromList :: [Bound] -> VNode
mkBoundsVNFromList bs = mkBoundsVN (Bounds{bdsList = bs})

mkBoundsValueFromList :: [Bound] -> Val
mkBoundsValueFromList bs = VBounds (Bounds{bdsList = bs})

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

addrToVNodes :: (TextIndexerMonad s m) => ValAddr -> m (Maybe [VNode])
addrToVNodes p = do
  xs <- mapM selToVal (addrToList p)
  return $ sequence xs
 where
  selToVal sel = case fetchLabelType sel of
    StringLabelType -> do
      str <- getTextFromFeature sel
      return $ Just $ mkAtomVN (String str)
    ListStoreIdxLabelType -> do
      let j = fetchIndex sel
      return $ Just $ mkAtomVN (Int (fromIntegral j))
    _ -> return Nothing

-- built-in functions
builtinFuncTable :: [(String, Op)]
builtinFuncTable =
  [
    ( "close"
    , RegOp $
        -- built-in close does not recursively close the struct.
        emptyRegularOp
          { ropName = "close"
          , ropArgs = Seq.fromList [mkValVN VTop]
          , ropOpType = CloseFunc
          }
    )
  ]

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
  VNoVal -> "noval"

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

{- | Check whether tree t1 subsumes tree t2.

According to spec,
A value a is an instance of a value b, denoted a ⊑ b, if b == a or b is more general than a, that is if a orders before
b in the partial order (⊑ is not a CUE operator). We also say that b subsumes a in this case. In graphical terms, b is
“above” a in the lattice.
-}
subsume :: VNode -> VNode -> VNode
subsume t1 t2 = undefined