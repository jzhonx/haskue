{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Cursor where

import Control.DeepSeq (NFData)
import Control.Monad (foldM)
import Data.Aeson (ToJSON (..))
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Feature
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (..), getTextIndex)
import Text.Printf (printf)
import Value

{- | Set the sub tree with the given segment and new tree.

The sub tree should already exist in the parent tree.
-}
setSubVal :: (HasCallStack) => Feature -> Val -> Val -> Maybe Val
setSubVal f@(fetchLabelType -> MutArgLabelType) subT parT@(IsValMutable mut) =
  return $ setTOp (updateSOpArg (fst (getMutArgInfoFromFeature f)) subT mut) parT
setSubVal f subT parT = case (fetchLabelType f, parT) of
  (StringLabelType, IsStruct parStruct)
    -- The label segment should already exist in the parent struct. Otherwise the description of the field will not be
    -- found.
    | Just field <- lookupStructField (getTextIndexFromFeature f) parStruct ->
        let
          newField = subT `updateFieldValue` field
          newStruct = updateStructField (getTextIndexFromFeature f) newField parStruct
         in
          ret $ VNStruct newStruct
  (PatternLabelType, IsStruct parStruct) ->
    let (i, j) = getPatternIndexesFromFeature f
     in ret $ VNStruct (updateStructCnstrByID i (j == 0) subT parStruct)
  (DynFieldLabelType, IsStruct parStruct) ->
    let (i, j) = getDynFieldIndexesFromFeature f
     in ret $ VNStruct (updateStructDynFieldByID i (j == 0) subT parStruct)
  (StubFieldLabelType, IsStruct parStruct) ->
    ret $ VNStruct (updateStructStaticFieldBase (getTextIndexFromFeature f) subT parStruct)
  (LetLabelType, IsStruct parStruct) ->
    ret $ VNStruct (insertStructLet (getTextIndexFromFeature f) subT parStruct)
  (EmbedValueLabelType, IsStruct parStruct) -> ret $ VNStruct (parStruct{stcEmbedVal = Just subT})
  (ListStoreIdxLabelType, IsList l) ->
    let i = fetchIndex f in ret $ VNList $ updateListStoreAt i subT l
  (ListIdxLabelType, IsList l) ->
    let i = fetchIndex f in ret $ VNList $ updateListFinalAt i subT l
  (DisjLabelType, IsDisj d) ->
    let i = fetchIndex f
     in ret (VNDisj $ d{dsjDisjuncts = Seq.update i subT (dsjDisjuncts d)})
  (VSelectBaseLabelType, IsValMutable mut@(Op (VSelect (ValueSelect{iSelectors})))) -> do
    return $ setTOp (setOpInSOp (VSelect (ValueSelect subT iSelectors)) mut) parT
  (RootLabelType, _) -> Nothing
  _ -> Nothing
 where
  ret tn = Just $ parT{valNode = tn}

getSubVal :: (HasCallStack) => Feature -> Val -> Maybe Val
getSubVal = go
 where
  go f t = case (fetchLabelType f, t) of
    -- Root segment always returns the same tree.
    (RootLabelType, _) -> Just t
    (MutArgLabelType, IsValMutable mut) -> snd <$> (getSOpArgs mut Seq.!? fst (getMutArgInfoFromFeature f))
    (StringLabelType, IsStruct struct)
      | Just sf <- lookupStructField (getTextIndexFromFeature f) struct -> Just $ ssfValue sf
    (LetLabelType, IsStruct struct) -> lookupStructLet (getTextIndexFromFeature f) struct
    (PatternLabelType, IsStruct struct) ->
      let (i, j) = getPatternIndexesFromFeature f
       in (if j == 0 then scsPattern else scsValue) <$> stcCnstrs struct IntMap.!? i
    (DynFieldLabelType, IsStruct struct) ->
      let (i, j) = getDynFieldIndexesFromFeature f
       in (if j == 0 then dsfLabel else dsfValue) <$> stcDynFields struct IntMap.!? i
    (StubFieldLabelType, IsStruct struct)
      | Just sf <- lookupStructStaticFieldBase (getTextIndexFromFeature f) struct ->
          Just $ ssfValue sf
    (EmbedValueLabelType, IsStruct struct) -> stcEmbedVal struct
    (ListStoreIdxLabelType, IsList l) -> getListStoreAt (fetchIndex f) l
    (ListIdxLabelType, IsList l) -> getListFinalAt (fetchIndex f) l
    (DisjLabelType, IsDisj d) -> dsjDisjuncts d Seq.!? fetchIndex f
    (VSelectBaseLabelType, IsValMutable (Op (VSelect (ValueSelect{base})))) -> Just base
    _ -> Nothing

getSubValByAddr :: ValAddr -> Val -> Maybe Val
getSubValByAddr addr = go (addrToList addr)
 where
  go [] v = Just v
  go (f : fs) v = do
    subV <- getSubVal f v
    go fs subV

{- | VCur is a pair of a value and a list of crumbs.
For example,
{
a: {
  b: {
    c: 42
  } // struct_c
} // struct_b
} // struct_a
Suppose the cursor is at the struct that contains the value 42. The cursor is
(struct_c, [("b", struct_b), ("a", struct_a)]).
-}
data VCur = VCur
  { focus :: !Val
  , crumbs :: [(Feature, Val)]
  }
  deriving (Eq, Generic, NFData)

-- | By default, only show the focus of the cursor.
instance Show VCur where
  show = show . focus

instance ToJSON VCur where
  toJSON = toJSON . focus

instance ShowWTIndexer VCur where
  tshow vc = tshow (focus vc)

instance ToJSONWTIndexer VCur where
  ttoJSON vc = ttoJSON (focus vc)

pattern VCFocus :: Val -> VCur
pattern VCFocus t <- VCur{focus = t}

addrFromCrumbs :: [(Feature, Val)] -> ValAddr
addrFromCrumbs crumbs = addrFromList $ go crumbs []
 where
  go [] acc = acc
  go ((n, _) : cs) acc = go cs (n : acc)

setVCFocus :: Val -> VCur -> VCur
setVCFocus t (VCur _ cs) = VCur t cs

mapVCFocus :: (Val -> Val) -> VCur -> VCur
mapVCFocus f (VCur t cs) = VCur (f t) cs

-- | Generate tree address from the tree cursor.
vcAddr :: VCur -> ValAddr
vcAddr c = addrFromCrumbs (crumbs c)

isVCTop :: VCur -> Bool
isVCTop (VCur _ []) = True
isVCTop _ = False

isVCRoot :: VCur -> Bool
isVCRoot (VCur _ [(IsRootFeature, _)]) = True
isVCRoot _ = False

-- showCursor :: VCur -> String
-- showCursor vc = LBS.unpack $ toLazyByteString $ prettyBldr vc
--  where
--   prettyBldr :: VCur -> Builder
--   prettyBldr (VCur t cs) =
--     string7 "-- ():\n"
--       <> string7 (show t)
--       <> char7 '\n'
--       <> foldl
--         ( \b (seg, n) ->
--             b
--               <> string7 "-- "
--               <> string7 (show seg)
--               <> char7 ':'
--               <> char7 '\n'
--               <> string7 (show n)
--               <> char7 '\n'
--         )
--         mempty
--         cs

-- | Create a sub cursor with the given segment and tree, and the updated parent tree from the current cursor.
mkSubVC :: Val -> Feature -> Val -> [(Feature, Val)] -> VCur
mkSubVC t seg parT crumbs = VCur t ((seg, parT) : crumbs)

modifyVCFocus :: (Val -> Val) -> VCur -> VCur
modifyVCFocus f (VCur t cs) = VCur (f t) cs

{- | Go down the TreeCursor with the given segment and return the new cursor.

It handles the cases when a node can be accessed without segments, such as the default value of a disjunction.
-}
goDownVCSeg :: Feature -> VCur -> Maybe VCur
goDownVCSeg seg vc@VCur{focus} = do
  case subVal seg focus of
    Just (nextTree, updatedParT) -> return $ mkSubVC nextTree seg updatedParT (crumbs vc)
    Nothing -> do
      nextVC <- case valNode focus of
        VNDisj d
          -- If the disjunction has one default disjunct, we can go to the default value without a segment.
          | [i] <- dsjDefIndexes d -> do
              dft <- rtrDisjDefVal d
              let updatedParT =
                    focus
                      { valNode = VNDisj $ d{dsjDisjuncts = Seq.update i singletonNoVal (dsjDisjuncts d)}
                      }
              return $ mkSubVC dft (mkDisjFeature i) updatedParT (crumbs vc)
        _ -> Nothing
      goDownVCSeg seg nextVC
 where
  subVal s t = do
    sub <- getSubVal s t
    updatedParT <- setSubVal s singletonNoVal t
    return (sub, updatedParT)

goDownVCSegMust :: Feature -> VCur -> VCur
goDownVCSegMust seg vc = case goDownVCSeg seg vc of
  Nothing ->
    error $
      printf "cannot go to sub (%s) tree from path: %s, parent: %s" (show seg) (show $ vcAddr vc) (show $ focus vc)
  Just nextVC -> nextVC

propUpVC :: VCur -> VCur
propUpVC (VCur _ []) = error "already on the top"
propUpVC vc@(VCur _ [(IsRootFeature, _)]) = vc
propUpVC (VCur subT ((seg, parT) : cs)) = do
  let tM = setSubVal seg subT parT
  case tM of
    Nothing -> error $ printf "cannot set sub tree (%s) to parent tree %s" (show seg) (show parT)
    Just t -> VCur t cs

data SubNodeSeg = SubNodeSegNormal Feature | SubNodeSegEmbed Feature deriving (Eq)

-- | Generate a list of immediate sub-trees that have values to reduce, not the values that have been reduced.
subNodes :: Bool -> VCur -> [Feature]
subNodes withStub (VCFocus t@(IsValMutable mut)) =
  let xs = [f | (f, _) <- toList $ getSOpArgs mut]
      ys = subVNSegsOpt withStub t
   in xs ++ ys
subNodes withStub vc = subVNSegsOpt withStub (focus vc)

subVNSegsOpt :: Bool -> Val -> [Feature]
subVNSegsOpt withStub t = subVNSegs t ++ if withStub then subStubSegs t else []

subVNSegs :: Val -> [Feature]
subVNSegs t = case valNode t of
  VNStruct s ->
    [mkStringFeature i | i <- Map.keys (stcFields s)]
      ++ [mkFeature (getTextIndex i) LetLabelType | i <- Map.keys (stcBindings s)]
      ++ [mkPatternFeature i 0 | i <- IntMap.keys $ stcCnstrs s]
      ++ [mkDynFieldFeature i 0 | i <- IntMap.keys $ stcDynFields s]
  VNList l -> [mkListStoreIdxFeature i | (i, _) <- zip [0 ..] (toList l.store)]
  VNDisj d ->
    [mkDisjFeature i | (i, _) <- zip [0 ..] (toList $ dsjDisjuncts d)]
  _ -> []

{- | Generate a list of sub-trees that are stubs.
x
-}
subStubSegs :: Val -> [Feature]
subStubSegs (IsStruct s) =
  [mkPatternFeature i 1 | i <- IntMap.keys $ stcCnstrs s]
    ++ [mkDynFieldFeature i 1 | i <- IntMap.keys $ stcDynFields s]
    ++ [mkStubFieldFeature i | i <- Map.keys (stcStaticFieldBases s)]
subStubSegs _ = []

{- | Visit every node in the tree in post-order and apply the function.

It does not re-constrain struct fields.
-}
postVisitVal ::
  (Monad m) =>
  (VCur -> [Feature]) ->
  ((VCur, a) -> m (VCur, a)) ->
  (VCur, a) ->
  m (VCur, a)
postVisitVal subs f x = do
  y <-
    foldM
      ( \acc subSeg -> do
          (seg, pre, post) <- return (subSeg, return, return)
          subTC <- do
            cur' <- pre (fst acc)
            return $ goDownVCSegMust seg cur'
          z <- postVisitVal subs f (subTC, snd acc)
          nextTC <- post (propUpVC (fst z))
          return (nextTC, snd z)
      )
      x
      (subs $ fst x)
  f y

postVisitValSimple ::
  (Monad m) =>
  (VCur -> [Feature]) ->
  (VCur -> m VCur) ->
  VCur ->
  m VCur
postVisitValSimple subs f vc = do
  (r, _) <-
    postVisitVal
      subs
      ( \(x, _) -> do
          r <- f x
          return (r, ())
      )
      (vc, ())
  return r
