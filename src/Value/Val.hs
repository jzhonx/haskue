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
import Control.Monad.State.Strict (gets, modify')
import Data.Maybe (fromJust, isJust)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Env (ErrorEnv)
import Exception (throwErrSt)
import Feature (
  FieldPath (FieldPath),
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
import Value.Comprehension
import Value.Constraint
import Value.Disj
import {-# SOURCE #-} Value.Export.AST (buildExprDebug)
import Value.Fix
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.UnifyOp (UnifyOp (..))

-- | ValNode represents a tree structure that contains values.
data ValNode
  = -- | VNAtom contains an atom value.
    VNAtom Atom
  | VNBottom Bottom
  | VNBounds Bounds
  | VNTop
  | VNStruct Struct
  | VNList List
  | VNDisj Disj
  | VNAtomCnstr AtomCnstr
  | VNFix Fix
  | -- | VNNoVal is used to represent a reference that is copied from another expression but has no value
    -- yet.
    VNNoVal
  deriving (Generic)

data Val = Val
  { valNode :: ValNode
  , wrappedBy :: ValNode
  -- ^ wrappedBy is used to indicate which tree node wraps this tree node.
  -- This is used by preserving wrapping information when going into a wrapped node.
  -- By default, it is noval.
  , origExpr :: Maybe AST.Expression
  -- ^ origExpr is the parsed expression.
  -- If the op is not Nothing, then origExpr represents the op expression.
  -- If the op is Nothing, then origExpr represents the value expression.
  , op :: Maybe SOp
  , isRecurClosed :: !Bool
  -- ^ isRecurClosed is used to indicate whether the sub-tree including itself is closed.
  , isRootOfSubVal :: !Bool
  -- ^ isRootOfSubVal is used to indicate whether the tree is the root of a sub-tree formed by parentheses.
  }
  deriving (Generic)

pattern VN :: ValNode -> Val
pattern VN tn <- Val{valNode = tn}

pattern WrappedBy :: ValNode -> Val
pattern WrappedBy w <- Val{wrappedBy = w}

pattern IsAtom :: Atom -> Val
pattern IsAtom a <- VN (VNAtom a)

pattern IsBottom :: Bottom -> Val
pattern IsBottom b <- VN (VNBottom b)

pattern IsBounds :: Bounds -> Val
pattern IsBounds b <- VN (VNBounds b)

pattern IsTop :: Val
pattern IsTop <- VN VNTop

pattern IsStruct :: Struct -> Val
pattern IsStruct struct <- VN (VNStruct struct)

pattern IsFullStruct :: Struct -> Val
pattern IsFullStruct struct <- VN (VNStruct struct@Struct{stcEmbedVal = Nothing})

pattern IsEmbedVal :: Val -> Val
pattern IsEmbedVal v <- VN (VNStruct Struct{stcEmbedVal = Just v})

pattern IsList :: List -> Val
pattern IsList lst <- VN (VNList lst)

pattern IsDisj :: Disj -> Val
pattern IsDisj d <- VN (VNDisj d)

pattern IsAtomCnstr :: AtomCnstr -> Val
pattern IsAtomCnstr c <- VN (VNAtomCnstr c)

pattern IsFix :: Fix -> Val
pattern IsFix r <- VN (VNFix r)

pattern IsNoVal :: Val
pattern IsNoVal <- VN VNNoVal

pattern IsValMutable :: SOp -> Val
pattern IsValMutable op <- Val{op = Just op}

pattern IsValImmutable :: Val
pattern IsValImmutable <- Val{op = Nothing}

pattern IsRef :: SOp -> Reference -> Val
pattern IsRef mut ref <- IsValMutable mut@(Op (Ref ref))

pattern IsIndex :: SOp -> InplaceIndex -> Val
pattern IsIndex mut idx <- IsValMutable mut@(Op (Index idx))

pattern IsRegOp :: SOp -> RegularOp -> Val
pattern IsRegOp mut rop <- IsValMutable mut@(Op (RegOp rop))

pattern IsCompreh :: SOp -> Comprehension -> Val
pattern IsCompreh mut comp <- IsValMutable mut@(Op (Compreh comp))

pattern IsEmbedUnifyOp :: SOp -> UnifyOp -> Val
pattern IsEmbedUnifyOp sop u <- IsValMutable sop@(Op (UOp u@UnifyOp{isEmbedUnify = True}))

pattern IsRegularUnifyOp :: SOp -> UnifyOp -> Val
pattern IsRegularUnifyOp sop u <- IsValMutable sop@(Op (UOp u@UnifyOp{isEmbedUnify = False}))

-- = ValNode getters and setters =

setVN :: ValNode -> Val -> Val
setVN n v = v{valNode = n}

setExpr :: Maybe AST.Expression -> Val -> Val
setExpr eM v = v{origExpr = eM}

setTOp :: SOp -> Val -> Val
setTOp f t = t{op = Just f}

supersedeVN :: ValNode -> Val -> Val
supersedeVN tn t = t{valNode = tn, wrappedBy = valNode t}

unwrapVN :: (Val -> ValNode) -> Val -> Val
unwrapVN f t = t{valNode = f t, wrappedBy = VNNoVal}

setValImmutable :: Val -> Val
setValImmutable t = t{op = Nothing}

invalidateMutable :: Val -> Val
invalidateMutable t@(IsValMutable _) = t{valNode = VNNoVal}
invalidateMutable t = t

{- | Retrieve the value of non-union type.

Union type represents an incomplete value, such as a disjunction or bounds.
-}
rtrNonUnion :: Val -> Maybe Val
rtrNonUnion v = do
  case valNode v of
    VNAtom _ -> Just v
    VNBottom _ -> Just v
    VNTop -> Just v
    VNList _ -> Just v
    VNStruct _ -> Just v
    VNFix{} -> Just v
    VNDisj d | Just df <- rtrDisjDefVal d -> rtrNonUnion df
    _ -> Nothing

-- | Retrieve the concrete value from the tree.
rtrConcrete :: Val -> Maybe Val
rtrConcrete t = do
  v <- rtrNonUnion t
  case v of
    IsAtom _ -> Just v
    -- There is only struct value after retrieving concrete value.
    IsStruct s -> if stcIsConcrete s then Just v else Nothing
    _ -> Nothing

rtrVal :: Val -> Maybe Val
rtrVal IsNoVal = Nothing
rtrVal t = return t

rtrAtom :: Val -> Maybe Atom
rtrAtom t = do
  v <- rtrNonUnion t
  case v of
    IsAtom a -> Just a
    _ -> Nothing

rtrString :: Val -> Maybe T.Text
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
    IsBottom b -> Just b
    IsStruct s
      | Just ev <- stcEmbedVal s -> rtrBottom ev
      | Just err <- stcPermErr s -> rtrBottom err
    _ -> Nothing

rtrBounds :: Val -> Maybe Bounds
rtrBounds v = case v of
  IsBounds b -> Just b
  _ -> Nothing

{- | Get the disjunction from the tree.

It stops at the first disjunction found. It does not go deeper to the default value of the disjunction.
-}
rtrDisj :: Val -> Maybe Disj
rtrDisj v = case v of
  IsDisj d -> Just d
  _ -> Nothing

rtrList :: Val -> Maybe List
rtrList t = do
  v <- rtrNonUnion t
  case v of
    IsList l -> Just l
    _ -> Nothing

rtrStruct :: Val -> Maybe Struct
rtrStruct t = do
  v <- rtrNonUnion t
  case v of
    IsStruct s -> Just s
    _ -> Nothing

-- | Convert the default disjuncts to a tree.
rtrDisjDefVal :: Disj -> Maybe Val
rtrDisjDefVal d =
  let dfs = defDisjunctsFromDisj d
   in if
        | null dfs -> Nothing
        | length dfs == 1 -> Just (head dfs)
        | otherwise -> Just $ mkDisjVal $ emptyDisj{dsjDisjuncts = dfs}

-- = Helpers =

emptyVal :: Val
emptyVal =
  Val
    { valNode = VNTop
    , wrappedBy = VNNoVal
    , op = Nothing
    , origExpr = Nothing
    , isRecurClosed = False
    , isRootOfSubVal = False
    }

mkNewVal :: ValNode -> Val
mkNewVal n = emptyVal{valNode = n}

mkNewValWithOp :: ValNode -> SOp -> Val
mkNewValWithOp n g = (mkNewVal n){op = Just g}

mkAtomVal :: Atom -> Val
mkAtomVal a = mkNewVal (VNAtom a)

mkAtomCnstrVal :: AtomCnstr -> Val
mkAtomCnstrVal c = mkNewVal (VNAtomCnstr c)

mkBottomVal :: String -> Val
mkBottomVal msg = mkNewVal (VNBottom $ Bottom{btmMsg = msg})

mkBoundsVal :: Bounds -> Val
mkBoundsVal bs = mkNewVal (VNBounds bs)

mkBoundsValFromList :: [Bound] -> Val
mkBoundsValFromList bs = mkBoundsVal (Bounds{bdsList = bs})

mkCnstrVal :: Atom -> Val -> Val
mkCnstrVal a e = mkNewVal . VNAtomCnstr $ AtomCnstr a e

mkDisjVal :: Disj -> Val
mkDisjVal d = mkNewVal (VNDisj d)

mkMutableVal :: SOp -> Val
mkMutableVal fn = (mkNewVal VNNoVal){op = Just fn}

mkListVal :: [Val] -> [Val] -> Val
mkListVal x y = mkNewVal (VNList $ mkList x y)

mkStructVal :: Struct -> Val
mkStructVal s = mkNewVal (VNStruct s)

singletonNoVal :: Val
singletonNoVal = mkNewVal VNNoVal

-- | Create an index or reference to select val from an operand.
selectValFromVal :: Val -> Val -> Val
selectValFromVal oprnd selArg = case oprnd of
  IsValMutable sop@(Op (Ref ref)) ->
    mkMutableVal $ setOpInSOp (Ref $ appendRefArg selArg ref) sop
  IsValMutable sop@(Op (Index index)) ->
    mkMutableVal $ setOpInSOp (Index $ appendInplaceIndexArg selArg index) sop
  _ -> mkMutableVal $ withEmptyOpFrame $ Index $ InplaceIndex (Seq.fromList [oprnd, selArg])

valsToFieldPath :: (TextIndexerMonad s m) => [Val] -> m (Maybe FieldPath)
valsToFieldPath ts = do
  xs <- mapM valToSel ts
  return $ FieldPath <$> sequence xs

valToSel :: (TextIndexerMonad s m) => Val -> m (Maybe Selector)
valToSel t = case valNode t of
  VNAtom a
    | (String s) <- a -> do
        tIdx <- textToTextIndex s
        return $ Just (StringSel tIdx)
    | (Int j) <- a -> return $ Just (IntSel $ fromIntegral j)
  -- If a disjunct has a default, then we should try to use the default.
  VNDisj dj | isJust (rtrDisjDefVal dj) -> valToSel (fromJust $ rtrDisjDefVal dj)
  _ -> return Nothing

addrToVals :: (TextIndexerMonad s m) => ValAddr -> m (Maybe [Val])
addrToVals p = do
  xs <- mapM selToVal (addrToList p)
  return $ sequence xs
 where
  selToVal sel = case fetchLabelType sel of
    StringLabelType -> do
      str <- getTextFromFeature sel
      return $ Just $ mkAtomVal (String str)
    ListStoreIdxLabelType -> do
      let j = fetchIndex sel
      return $ Just $ mkAtomVal (Int (fromIntegral j))
    _ -> return Nothing

-- built-in functions
builtinFuncTable :: [(String, Val)]
builtinFuncTable =
  [
    ( "close"
    , mkMutableVal $
        withEmptyOpFrame $
          RegOp $
            -- built-in close does not recursively close the struct.
            emptyRegularOp
              { ropName = "close"
              , ropArgs = Seq.fromList [mkNewVal VNTop]
              , ropOpType = CloseFunc
              }
    )
  ]

-- | Create a one-liner string representation of the snapshot of the tree.
oneLinerStringOfVal :: (TextIndexerMonad s m) => Val -> m T.Text
oneLinerStringOfVal t = do
  tier <- gets getTextIndexer
  let m = buildExprDebug t tier
      e = runExcept m
  case e of
    Left err -> return $ T.pack err
    Right (expr, newTier) -> do
      modify' $ setTextIndexer newTier
      return $ T.pack $ exprToOneLinerStr expr

showValSymbol :: Val -> String
showValSymbol t = case valNode t of
  VNAtom _ -> "atom"
  VNBounds _ -> "bds"
  VNStruct{} -> "{}"
  VNList{} -> "[]"
  VNDisj{} -> "dj"
  VNAtomCnstr{} -> "Cnstr"
  VNFix{} -> "Fix"
  VNBottom _ -> "_|_"
  VNTop -> "_"
  VNNoVal -> "noval"

showValueType :: (ErrorEnv m) => Val -> m String
showValueType t = case valNode t of
  VNAtom a -> case a of
    String _ -> return "string"
    Int _ -> return "int"
    Float _ -> return "float"
    Bool _ -> return "bool"
    Null -> return "null"
  VNBounds b -> return $ show b
  VNBottom _ -> return "_|_"
  VNStruct _ -> return "struct"
  VNList _ -> return "list"
  VNTop -> return "_"
  _ -> throwErrSt $ "not a value type: " ++ showValSymbol t

{- | Check whether tree t1 subsumes tree t2.

According to spec,
A value a is an instance of a value b, denoted a ⊑ b, if b == a or b is more general than a, that is if a orders before
b in the partial order (⊑ is not a CUE operator). We also say that b subsumes a in this case. In graphical terms, b is
“above” a in the lattice.
-}
subsume :: Val -> Val -> Val
subsume t1 t2 = undefined