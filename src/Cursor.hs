{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module Cursor where

import Control.DeepSeq (NFData)
import Data.Aeson (ToJSON (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Sequence as Seq
import Feature
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (..))
import Value

{- | Set the sub tree with the given segment and new tree.

The sub tree should already exist in the parent tree.
-}
setSubVal :: (HasCallStack) => Feature -> Val -> VNode -> Maybe VNode
setSubVal f subT parT = case (fetchLabelType f, parT) of
  (StringLabelType, IsStruct parStruct)
    -- The label segment should already exist in the parent struct. Otherwise the description of the field will not be
    -- found.
    | Just field <- lookupStructField (getTextIndexFromFeature f) parStruct ->
        let
          newField = mapFieldValue (setVNodeValue subT) field
          newStruct = updateStructField (getTextIndexFromFeature f) newField parStruct
         in
          ret $ VStruct newStruct
  (PatternLabelType, IsStruct parStruct) ->
    let (i, j) = getPatternIndexesFromFeature f
     in ret $ VStruct (mapStructCnstrByID i (setVNodeValue subT) parStruct)
  (DynFieldLabelType, IsStruct parStruct) ->
    let (i, j) = getDynFieldIndexesFromFeature f
     in ret $ VStruct (mapStructDynFieldByID i (setVNodeValue subT) parStruct)
  (LetLabelType, IsStruct parStruct) ->
    ret $ VStruct (mapStructLet (getTextIndexFromFeature f) (setVNodeValue subT) parStruct)
  (EmbedValueLabelType, IsStruct parStruct) -> ret $ VStruct (parStruct{stcEmbedVal = Just subT})
  (ListStoreIdxLabelType, IsList l) ->
    let i = fetchIndex f in ret $ VList $ updateListStoreAt i (setVNodeValue subT) l
  (ListIdxLabelType, IsList l) ->
    let i = fetchIndex f in ret $ VList $ updateListFinalAt i (setVNodeValue subT) l
  (DisjLabelType, IsDisj d) ->
    let i = fetchIndex f
     in ret (VDisj $ d{dsjDisjuncts = Seq.update i (mkValVN subT) (dsjDisjuncts d)})
  (RootLabelType, _) -> Nothing
  _ -> Nothing
 where
  ret tn = Just $ parT{value = tn}

getSubVal :: (HasCallStack) => Feature -> VNode -> Maybe VNode
getSubVal = go
 where
  go f t = case (fetchLabelType f, t) of
    -- Root segment always returns the same tree.
    (RootLabelType, _) -> Just t
    (StringLabelType, IsStruct struct)
      | Just sf <- lookupStructField (getTextIndexFromFeature f) struct -> Just $ ssfValue sf
    (LetLabelType, IsStruct struct) -> lookupStructLet (getTextIndexFromFeature f) struct
    (PatternLabelType, IsStruct struct) ->
      let (i, j) = getPatternIndexesFromFeature f
       in scsPattern <$> stcCnstrs struct IntMap.!? i
    (DynFieldLabelType, IsStruct struct) ->
      let (i, j) = getDynFieldIndexesFromFeature f
       in dsfLabel <$> stcDynFields struct IntMap.!? i
    (EmbedValueLabelType, IsStruct struct) -> mkValVN <$> stcEmbedVal struct
    (ListStoreIdxLabelType, IsList l) -> getListStoreAt (fetchIndex f) l
    (ListIdxLabelType, IsList l) -> getListFinalAt (fetchIndex f) l
    (DisjLabelType, IsDisj d) -> dsjDisjuncts d Seq.!? fetchIndex f
    _ -> Nothing

getSubValByAddr :: ValAddr -> VNode -> Maybe VNode
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
  { focus :: !VNode
  , crumbs :: [(Feature, VNode)]
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

pattern VCFocus :: VNode -> VCur
pattern VCFocus t <- VCur{focus = t}

addrFromCrumbs :: [(Feature, VNode)] -> ValAddr
addrFromCrumbs crumbs = addrFromList $ go crumbs []
 where
  go [] acc = acc
  go ((n, _) : cs) acc = go cs (n : acc)

setVCFocus :: VNode -> VCur -> VCur
setVCFocus t (VCur _ cs) = VCur t cs

mapVCFocus :: (VNode -> VNode) -> VCur -> VCur
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

-- -- | Create a sub cursor with the given segment and tree, and the updated parent tree from the current cursor.
-- mkSubVC :: VNode -> Feature -> VNode -> [(Feature, VNode)] -> VCur
-- mkSubVC t seg parT crumbs = VCur t ((seg, parT) : crumbs)

-- modifyVCFocus :: (VNode -> VNode) -> VCur -> VCur
-- modifyVCFocus f (VCur t cs) = VCur (f t) cs

-- {- | Go down the TreeCursor with the given segment and return the new cursor.

-- It handles the cases when a node can be accessed without segments, such as the default value of a disjunction.
-- -}
-- goDownVCSeg :: Feature -> VCur -> Maybe VCur
-- goDownVCSeg seg vc@VCur{focus} = do
--   case subVal seg focus of
--     Just (nextTree, updatedParT) -> return $ mkSubVC nextTree seg updatedParT (crumbs vc)
--     Nothing -> do
--       nextVC <- case value focus of
--         VDisj d
--           -- If the disjunction has one default disjunct, we can go to the default value without a segment.
--           | [i] <- dsjDefIndexes d -> do
--               dft <- rtrDisjDefVal d
--               let updatedParT =
--                     focus
--                       { value = VDisj $ d{dsjDisjuncts = Seq.update i VNoVal (dsjDisjuncts d)}
--                       }
--               return $ mkSubVC dft (mkDisjFeature i) updatedParT (crumbs vc)
--         _ -> Nothing
--       goDownVCSeg seg nextVC
--  where
--   subVal s t = do
--     sub <- getSubVal s t
--     updatedParT <- setSubVal s emptyVNode t
--     return (sub, updatedParT)

-- goDownVCSegMust :: Feature -> VCur -> VCur
-- goDownVCSegMust seg vc = case goDownVCSeg seg vc of
--   Nothing ->
--     error $
--       printf "cannot go to sub (%s) tree from path: %s, parent: %s" (show seg) (show $ vcAddr vc) (show $ focus vc)
--   Just nextVC -> nextVC

-- propUpVC :: VCur -> VCur
-- propUpVC (VCur _ []) = error "already on the top"
-- propUpVC vc@(VCur _ [(IsRootFeature, _)]) = vc
-- propUpVC (VCur subT ((seg, parT) : cs)) = do
--   let tM = setSubVal seg subT parT
--   case tM of
--     Nothing -> error $ printf "cannot set sub tree (%s) to parent tree %s" (show seg) (show parT)
--     Just t -> VCur t cs

-- data SubNodeSeg = SubNodeSegNormal Feature | SubNodeSegEmbed Feature deriving (Eq)

-- -- | Generate a list of immediate sub-trees that have values to reduce, not the values that have been reduced.
-- subNodes :: Bool -> VCur -> [Feature]
-- -- subNodes withStub (VCFocus t@(IsValMutable mut)) =
-- --   let xs = [f | (f, _) <- toList $ getSOpArgs mut]
-- --       ys = subVNSegsOpt withStub t
-- --    in xs ++ ys
-- subNodes withStub vc = subVNSegsOpt withStub (focus vc)

-- subVNSegsOpt :: Bool -> VNode -> [Feature]
-- subVNSegsOpt withStub t = subVNSegs t ++ if withStub then subStubSegs t else []

-- subVNSegs :: VNode -> [Feature]
-- subVNSegs t = case value t of
--   VStruct s ->
--     [mkStringFeature i | i <- Map.keys (stcFields s)]
--       ++ [mkFeature (getTextIndex i) LetLabelType | i <- Map.keys (stcBindings s)]
--       ++ [mkPatternFeature i 0 | i <- IntMap.keys $ stcCnstrs s]
--       ++ [mkDynFieldFeature i 0 | i <- IntMap.keys $ stcDynFields s]
--   VList l -> [mkListStoreIdxFeature i | (i, _) <- zip [0 ..] (toList l.store)]
--   VDisj d ->
--     [mkDisjFeature i | (i, _) <- zip [0 ..] (toList $ dsjDisjuncts d)]
--   _ -> []

-- {- | Generate a list of sub-trees that are stubs.
-- x
-- -}
-- subStubSegs :: VNode -> [Feature]
-- subStubSegs (IsStruct s) =
--   [mkPatternFeature i 1 | i <- IntMap.keys $ stcCnstrs s]
--     ++ [mkDynFieldFeature i 1 | i <- IntMap.keys $ stcDynFields s]
-- subStubSegs _ = []

-- {- | Visit every node in the tree in post-order and apply the function.

-- It does not re-constrain struct fields.
-- -}
-- postVisitVal ::
--   (Monad m) =>
--   (VCur -> [Feature]) ->
--   ((VCur, a) -> m (VCur, a)) ->
--   (VCur, a) ->
--   m (VCur, a)
-- postVisitVal subs f x = do
--   y <-
--     foldM
--       ( \acc subSeg -> do
--           (seg, pre, post) <- return (subSeg, return, return)
--           subTC <- do
--             cur' <- pre (fst acc)
--             return $ goDownVCSegMust seg cur'
--           z <- postVisitVal subs f (subTC, snd acc)
--           nextTC <- post (propUpVC (fst z))
--           return (nextTC, snd z)
--       )
--       x
--       (subs $ fst x)
--   f y

-- postVisitValSimple ::
--   (Monad m) =>
--   (VCur -> [Feature]) ->
--   (VCur -> m VCur) ->
--   VCur ->
--   m VCur
-- postVisitValSimple subs f vc = do
--   (r, _) <-
--     postVisitVal
--       subs
--       ( \(x, _) -> do
--           r <- f x
--           return (r, ())
--       )
--       (vc, ())
--   return r
