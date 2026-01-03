{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Cursor where

import Control.DeepSeq (NFData (..))
import Control.Monad (when)
import Data.Aeson (ToJSON (..))
import Data.ByteString.Builder (
  Builder,
  char7,
  string7,
  toLazyByteString,
 )
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence as Seq
import Feature
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (..), getTextIndex)
import Text.Printf (printf)
import Value

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

-- | Get the segment paired with the focus of the cursor.
vcFocusSeg :: VCur -> Maybe Feature
vcFocusSeg (VCur _ []) = Nothing
vcFocusSeg vc = return $ fst . head $ crumbs vc

-- | Get the segment paired with the focus of the cursor.
vcFocusSegMust :: VCur -> Either String Feature
vcFocusSegMust vc = maybe (Left "already top") return (vcFocusSeg vc)

isVCTop :: VCur -> Bool
isVCTop (VCur _ []) = True
isVCTop _ = False

isVCRoot :: VCur -> Bool
isVCRoot (VCur _ [(IsRootFeature, _)]) = True
isVCRoot _ = False

showCursor :: VCur -> String
showCursor vc = LBS.unpack $ toLazyByteString $ prettyBldr vc
 where
  prettyBldr :: VCur -> Builder
  prettyBldr (VCur t cs) =
    string7 "-- ():\n"
      <> string7 (show t)
      <> char7 '\n'
      <> foldl
        ( \b (seg, n) ->
            b
              <> string7 "-- "
              <> string7 (show seg)
              <> char7 ':'
              <> char7 '\n'
              <> string7 (show n)
              <> char7 '\n'
        )
        mempty
        cs

-- | Create a sub cursor with the given segment and tree, and the updated parent tree from the current cursor.
mkSubVC :: Val -> Feature -> Val -> [(Feature, Val)] -> VCur
mkSubVC t seg parT crumbs = VCur t ((seg, parT) : crumbs)

modifyVCFocus :: (Val -> Val) -> VCur -> VCur
modifyVCFocus f (VCur t cs) = VCur (f t) cs

setVCFocusVN :: ValNode -> VCur -> VCur
setVCFocusVN tn = modifyVCFocus (setVN tn)

setVCFocusMut :: SOp -> VCur -> VCur
setVCFocusMut f = modifyVCFocus (setTOp f)

goDownVCAddr :: ValAddr -> VCur -> Maybe VCur
goDownVCAddr a = go (addrToList a)
 where
  go :: [Feature] -> VCur -> Maybe VCur
  go [] cursor = Just cursor
  go (x : xs) cursor = do
    nextCur <- goDownVCSeg x cursor
    go xs nextCur

goDownTAddr :: ValAddr -> Val -> Maybe VCur
goDownTAddr addr starT = goDownVCAddr addr (VCur starT [])

goDownVCAddrMust :: ValAddr -> VCur -> Either String VCur
goDownVCAddrMust addr vc =
  maybe
    (Left $ printf "cannot go to addr (%s) tree from %s" (show addr) (show $ vcAddr vc))
    return
    (goDownVCAddr addr vc)

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
                      { valNode =
                          VNDisj $
                            d
                              { dsjDisjuncts =
                                  take i (dsjDisjuncts d) ++ [singletonNoVal] ++ drop (i + 1) (dsjDisjuncts d)
                              }
                      }
              return $ mkSubVC dft (mkDisjFeature i) updatedParT (crumbs vc)
        _ -> Nothing
      goDownVCSeg seg nextVC

goDownVCSegMust :: Feature -> VCur -> Either String VCur
goDownVCSegMust seg vc =
  maybe
    ( Left $
        printf "cannot go to sub (%s) tree from path: %s, parent: %s" (show seg) (show $ vcAddr vc) (show $ focus vc)
    )
    return
    $ goDownVCSeg seg vc

{- | Propagates the changes made to the focus to the parent nodes.

It stops at the root.
-}
propUpVC :: VCur -> Either String VCur
propUpVC (VCur _ []) = Left "already at the top"
propUpVC vc@(VCur _ [(IsRootFeature, _)]) = return vc
propUpVC (VCur subT ((seg, parT) : cs)) = do
  let tM = setSubVal seg subT parT
  case tM of
    Nothing -> Left $ printf "cannot set sub tree (%s) to parent tree %s" (show seg) (show parT)
    Just t -> return $ VCur t cs

{- | Propagates the changes made to the focus to the parent nodes.

If the cursor is at Root, it returns Nothing too through setSubVal.
-}
propUpVCMaybe :: VCur -> Maybe VCur
propUpVCMaybe (VCur _ []) = Nothing
propUpVCMaybe (VCur subT ((seg, parT) : cs)) = do
  t <- setSubVal seg subT parT
  return $ VCur t cs

{- | Descend into the tree with the given segment.

It returns the sub tree and the updated parent tree.

This should only be used by TreeCursor.
-}
subVal :: (HasCallStack) => Feature -> Val -> Maybe (Val, Val)
subVal seg parentT = do
  sub <- go seg parentT
  updatedParT <- setSubVal seg singletonNoVal parentT
  return (sub, updatedParT)
 where
  go f t = case (fetchLabelType f, t) of
    -- Root segment always returns the same tree.
    (RootLabelType, _) -> Just t
    -- go into withRCs will immediately go into its inner tree.
    (_, IsFix r) -> go f (supersedeVN r.val t)
    (MutArgLabelType, IsValMutable mut) -> snd <$> (getSOpArgs mut Seq.!? fst (getMutArgInfoFromFeature f))
    (TempLabelType, _) -> tmpSub t
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
    (ListStoreIdxLabelType, IsList l) -> getListStoreAt (fetchIndex f) l
    (ListIdxLabelType, IsList l) -> getListFinalAt (fetchIndex f) l
    (DisjLabelType, IsDisj d) -> dsjDisjuncts d `indexList` fetchIndex f
    _ -> Nothing

{- | Set the sub tree with the given segment and new tree.

The sub tree should already exist in the parent tree.
-}
setSubVal :: (HasCallStack) => Feature -> Val -> Val -> Maybe Val
setSubVal f@(fetchLabelType -> MutArgLabelType) subT parT@(IsValMutable mut) =
  return $ setTOp (updateSOpArg (fst (getMutArgInfoFromFeature f)) subT mut) parT
setSubVal (fetchLabelType -> TempLabelType) subT parT = return $ parT{tmpSub = Just subT}
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
    ret $ VNStruct (updateStructLetBinding (getTextIndexFromFeature f) subT parStruct)
  (ListStoreIdxLabelType, IsList l) ->
    let i = fetchIndex f in ret $ VNList $ updateListStoreAt i subT l
  (ListIdxLabelType, IsList l) ->
    let i = fetchIndex f in ret $ VNList $ updateListFinalAt i subT l
  (DisjLabelType, IsDisj d) ->
    let i = fetchIndex f
     in ret (VNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)})
  (RootLabelType, _) -> Nothing
  -- parT is wrapped by withRCs, so we need to reconstruct the withRCs node.
  (_, WrappedBy (VNFix r)) ->
    setSubVal f subT (unwrapVN (\x -> VNFix (r{val = valNode x})) parT)
  _ -> Nothing
 where
  ret tn = Just $ parT{valNode = tn}

indexList :: [a] -> Int -> Maybe a
indexList xs i = if i < length xs then Just (xs !! i) else Nothing

setSubValMust :: Feature -> Val -> Val -> Either String Val
setSubValMust seg subT parT =
  maybe
    (Left $ printf "cannot set sub tree (%s) to parent tree %s" (show seg) (show parT))
    return
    (setSubVal seg subT parT)

-- | Go to the top of the tree cursor.
topVC :: VCur -> Either String VCur
topVC (VCur _ []) = Left "already at the top"
topVC vc@(VCur _ ((IsRootFeature, _) : _)) = return vc
topVC vc = do
  parVC <- propUpVC vc
  topVC parVC

-- = Traversal =

data SubNodeSeg = SubNodeSegNormal Feature | SubNodeSegEmbed Feature deriving (Eq)

-- | Generate a list of immediate sub-trees that have values to reduce, not the values that have been reduced.
subNodes :: Bool -> VCur -> [SubNodeSeg]
subNodes withStub (VCFocus t@(IsValMutable mut)) =
  let xs = [SubNodeSegNormal f | (f, _) <- toList $ getSOpArgs mut]
      ys = subVNSegsOpt withStub t
   in xs ++ ys
subNodes withStub vc = subVNSegsOpt withStub (focus vc)

subVNSegsOpt :: Bool -> Val -> [SubNodeSeg]
subVNSegsOpt withStub t = map SubNodeSegNormal $ subVNSegs t ++ if withStub then subStubSegs t else []

subVNSegs :: Val -> [Feature]
subVNSegs t = case valNode t of
  VNStruct s ->
    [mkStringFeature i | i <- Map.keys (stcFields s)]
      ++ [mkFeature (getTextIndex i) LetLabelType | i <- Map.keys (stcBindings s)]
      ++ [mkPatternFeature i 0 | i <- IntMap.keys $ stcCnstrs s]
      ++ [mkDynFieldFeature i 0 | i <- IntMap.keys $ stcDynFields s]
  VNList l -> [mkListStoreIdxFeature i | (i, _) <- zip [0 ..] (toList l.store)]
  VNDisj d ->
    [mkDisjFeature i | (i, _) <- zip [0 ..] (dsjDisjuncts d)]
  _ -> []

{- | Generate a list of sub-trees that are stubs.

TODO: comprehension struct
-}
subStubSegs :: Val -> [Feature]
subStubSegs (IsStruct s) =
  [mkPatternFeature i 1 | i <- IntMap.keys $ stcCnstrs s]
    ++ [mkDynFieldFeature i 1 | i <- IntMap.keys $ stcDynFields s]
    ++ [mkStubFieldFeature i | i <- Map.keys (stcStaticFieldBases s)]
subStubSegs _ = []

{- | Go to the absolute addr in the tree. No propagation is involved.

The tree must have all the latest changes.
-}
goVCAbsAddr :: ValAddr -> VCur -> Either String (Maybe VCur)
goVCAbsAddr dst vc = do
  when (headSeg dst /= Just rootFeature) $
    Left (printf "the addr %s should start with the root segment" (show dst))
  top <- topVC vc
  let dstNoRoot = fromJust $ tailValAddr dst
  return $ goDownVCAddr dstNoRoot top

goVCAbsAddrMust :: ValAddr -> VCur -> Either String VCur
goVCAbsAddrMust dst vc = do
  tarM <- goVCAbsAddr dst vc
  maybe (Left $ printf "failed to go to the addr %s" (show dst)) return tarM
