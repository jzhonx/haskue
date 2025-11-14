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

class HasTreeCursor s where
  getTreeCursor :: s -> TrCur
  setTreeCursor :: s -> TrCur -> s

{- | TreeCursor is a pair of a value and a list of crumbs.
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
data TrCur = TrCur
  { tcFocus :: !Tree
  , tcCrumbs :: [(Feature, Tree)]
  }
  deriving (Eq, Generic, NFData)

-- | By default, only show the focus of the cursor.
instance Show TrCur where
  show = show . tcFocus

instance ToJSON TrCur where
  toJSON = toJSON . tcFocus

instance ShowWTIndexer TrCur where
  tshow tc = tshow (tcFocus tc)

instance ToJSONWTIndexer TrCur where
  ttoJSON tc = ttoJSON (tcFocus tc)

pattern TCFocus :: Tree -> TrCur
pattern TCFocus t <- TrCur{tcFocus = t}

addrFromCrumbs :: [(Feature, Tree)] -> TreeAddr
addrFromCrumbs crumbs = addrFromList $ go crumbs []
 where
  go [] acc = acc
  go ((n, _) : cs) acc = go cs (n : acc)

setTCFocus :: Tree -> TrCur -> TrCur
setTCFocus t (TrCur _ cs) = TrCur t cs

-- | Generate tree address from the tree cursor.
tcAddr :: TrCur -> TreeAddr
tcAddr c = addrFromCrumbs (tcCrumbs c)

-- | Get the segment paired with the focus of the cursor.
tcFocusSeg :: TrCur -> Maybe Feature
tcFocusSeg (TrCur _ []) = Nothing
tcFocusSeg tc = return $ fst . head $ tcCrumbs tc

-- | Get the segment paired with the focus of the cursor.
tcFocusSegMust :: TrCur -> Either String Feature
tcFocusSegMust tc = maybe (Left "already top") return (tcFocusSeg tc)

isTCTop :: TrCur -> Bool
isTCTop (TrCur _ []) = True
isTCTop _ = False

isTCRoot :: TrCur -> Bool
isTCRoot (TrCur _ [(IsRootFeature, _)]) = True
isTCRoot _ = False

showCursor :: TrCur -> String
showCursor tc = LBS.unpack $ toLazyByteString $ prettyBldr tc
 where
  prettyBldr :: TrCur -> Builder
  prettyBldr (TrCur t cs) =
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
mkSubTC :: Tree -> Feature -> Tree -> [(Feature, Tree)] -> TrCur
mkSubTC t seg parT crumbs = TrCur t ((seg, parT) : crumbs)

modifyTCFocus :: (Tree -> Tree) -> TrCur -> TrCur
modifyTCFocus f (TrCur t cs) = TrCur (f t) cs

setTCFocusTN :: TreeNode -> TrCur -> TrCur
setTCFocusTN tn = modifyTCFocus (`setTN` tn)

setTCFocusMut :: Mutable -> TrCur -> TrCur
setTCFocusMut mut = modifyTCFocus (setTValGenEnv (TGenOp mut))

goDownTCAddr :: TreeAddr -> TrCur -> Maybe TrCur
goDownTCAddr a = go (addrToList a)
 where
  go :: [Feature] -> TrCur -> Maybe TrCur
  go [] cursor = Just cursor
  go (x : xs) cursor = do
    nextCur <- goDownTCSeg x cursor
    go xs nextCur

goDownTAddr :: TreeAddr -> Tree -> Maybe TrCur
goDownTAddr addr starT = goDownTCAddr addr (TrCur starT [])

goDownTCAddrMust :: TreeAddr -> TrCur -> Either String TrCur
goDownTCAddrMust addr tc =
  maybe
    (Left $ printf "cannot go to addr (%s) tree from %s" (show addr) (show $ tcAddr tc))
    return
    (goDownTCAddr addr tc)

{- | Go down the TreeCursor with the given segment and return the new cursor.

It handles the cases when a node can be accessed without segments, such as the default value of a disjunction.
-}
goDownTCSeg :: Feature -> TrCur -> Maybe TrCur
goDownTCSeg seg tc = do
  let focus = tcFocus tc
  case subTree seg focus of
    Just (nextTree, updatedParT) -> return $ mkSubTC nextTree seg updatedParT (tcCrumbs tc)
    Nothing -> do
      nextTC <- case treeNode focus of
        TNDisj d
          -- If the disjunction has one default disjunct, we can go to the default value without a segment.
          | [i] <- dsjDefIndexes d -> do
              dft <- rtrDisjDefVal d
              let updatedParT =
                    focus
                      { treeNode =
                          TNDisj $
                            d
                              { dsjDisjuncts =
                                  take i (dsjDisjuncts d) ++ [singletonNoVal] ++ drop (i + 1) (dsjDisjuncts d)
                              }
                      }
              return $ mkSubTC dft (mkDisjFeature i) updatedParT (tcCrumbs tc)
        _ -> Nothing
      goDownTCSeg seg nextTC

goDownTCSegMust :: Feature -> TrCur -> Either String TrCur
goDownTCSegMust seg tc =
  maybe
    ( Left $
        printf "cannot go to sub (%s) tree from path: %s, parent: %s" (show seg) (show $ tcAddr tc) (show $ tcFocus tc)
    )
    return
    $ goDownTCSeg seg tc

{- | Propagates the changes made to the focus to the parent nodes.

It stops at the root.
-}
propUpTC :: TrCur -> Either String TrCur
propUpTC (TrCur _ []) = Left "already at the top"
propUpTC tc@(TrCur _ [(IsRootFeature, _)]) = return tc
propUpTC (TrCur subT ((seg, parT) : cs)) = do
  let tM = setSubTree seg subT parT
  case tM of
    Nothing -> Left $ printf "cannot set sub tree (%s) to parent tree %s" (show seg) (show parT)
    Just t -> return $ TrCur t cs

{- | Propagates the changes made to the focus to the parent nodes.

If the cursor is at Root, it returns Nothing too through setSubTree.
-}
propUpTCMaybe :: TrCur -> Maybe TrCur
propUpTCMaybe (TrCur _ []) = Nothing
propUpTCMaybe (TrCur subT ((seg, parT) : cs)) = do
  t <- setSubTree seg subT parT
  return $ TrCur t cs

{- | Descend into the tree with the given segment.

It returns the sub tree and the updated parent tree with

This should only be used by TreeCursor.
-}
subTree :: (HasCallStack) => Feature -> Tree -> Maybe (Tree, Tree)
subTree seg parentT = do
  sub <- go seg parentT
  updatedParT <- setSubTree seg singletonNoVal parentT
  return (sub, updatedParT)
 where
  go f t = case (fetchLabelType f, t) of
    (RootLabelType, _) -> Just t
    (MutArgLabelType, IsTGenOp mut) -> snd <$> (getMutArgs mut Seq.!? fst (getMutArgInfoFromFeature f))
    (TempLabelType, _) -> tmpSub t
    (StringLabelType, IsStruct struct)
      | Just sf <- lookupStructField (getTextIndexFromFeature f) struct -> Just $ ssfValue sf
    (LetLabelType, IsStruct struct) -> lookupStructLet (getTextIndexFromFeature f) struct
    (PatternLabelType, IsStruct struct) ->
      let
        (i, j) = getPatternIndexesFromFeature f
       in
        (if j == 0 then scsPattern else scsValue) <$> stcCnstrs struct IntMap.!? i
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
setSubTree :: (HasCallStack) => Feature -> Tree -> Tree -> Maybe Tree
setSubTree f@(fetchLabelType -> MutArgLabelType) subT parT@(IsTGenOp mut) =
  return $ setTValGenEnv (TGenOp $ updateMutArg (fst (getMutArgInfoFromFeature f)) subT mut) parT
setSubTree (fetchLabelType -> TempLabelType) subT parT = return $ parT{tmpSub = Just subT}
setSubTree f subT parT = do
  n <- case (fetchLabelType f, parT) of
    (StringLabelType, IsStruct parStruct)
      -- The label segment should already exist in the parent struct. Otherwise the description of the field will not be
      -- found.
      | Just field <- lookupStructField (getTextIndexFromFeature f) parStruct ->
          let
            newField = subT `updateFieldValue` field
            newStruct = updateStructField (getTextIndexFromFeature f) newField parStruct
           in
            return $ TNStruct newStruct
    (PatternLabelType, IsStruct parStruct) ->
      let (i, j) = getPatternIndexesFromFeature f
       in return $ TNStruct (updateStructCnstrByID i (j == 0) subT parStruct)
    (DynFieldLabelType, IsStruct parStruct) ->
      let (i, j) = getDynFieldIndexesFromFeature f
       in return $ TNStruct (updateStructDynFieldByID i (j == 0) subT parStruct)
    (StubFieldLabelType, IsStruct parStruct) ->
      return $ TNStruct (updateStructStaticFieldBase (getTextIndexFromFeature f) subT parStruct)
    (LetLabelType, IsStruct parStruct) ->
      return $ TNStruct (updateStructLetBinding (getTextIndexFromFeature f) subT parStruct)
    (ListStoreIdxLabelType, IsList l) ->
      let i = fetchIndex f in return $ TNList $ updateListStoreAt i subT l
    (ListIdxLabelType, IsList l) ->
      let i = fetchIndex f in return $ TNList $ updateListFinalAt i subT l
    (DisjLabelType, IsDisj d) ->
      let i = fetchIndex f
       in return (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)})
    (RootLabelType, _) -> Nothing
    _ -> Nothing
  return parT{treeNode = n}

indexList :: [a] -> Int -> Maybe a
indexList xs i = if i < length xs then Just (xs !! i) else Nothing

setSubTreeMust :: Feature -> Tree -> Tree -> Either String Tree
setSubTreeMust seg subT parT =
  maybe
    (Left $ printf "cannot set sub tree (%s) to parent tree %s" (show seg) (show parT))
    return
    (setSubTree seg subT parT)

-- | Go to the top of the tree cursor.
topTC :: TrCur -> Either String TrCur
topTC (TrCur _ []) = Left "already at the top"
topTC tc@(TrCur _ ((IsRootFeature, _) : _)) = return tc
topTC tc = do
  parTC <- propUpTC tc
  topTC parTC

-- = Traversal =

data SubNodeSeg = SubNodeSegNormal Feature | SubNodeSegEmbed Feature deriving (Eq)

-- | Generate a list of immediate sub-trees that have values to reduce, not the values that have been reduced.
subNodes :: Bool -> TrCur -> [SubNodeSeg]
subNodes withStub (TCFocus t@(IsTGenOp mut)) =
  let xs = [SubNodeSegNormal f | (f, _) <- toList $ getMutArgs mut]
      ys = subTNSegsOpt withStub t
   in xs ++ ys
subNodes withStub tc = subTNSegsOpt withStub (tcFocus tc)

subTNSegsOpt :: Bool -> Tree -> [SubNodeSeg]
subTNSegsOpt withStub t = map SubNodeSegNormal $ subTNSegs t ++ if withStub then subStubSegs t else []

subTNSegs :: Tree -> [Feature]
subTNSegs t = case treeNode t of
  TNStruct s ->
    [mkStringFeature i | i <- Map.keys (stcFields s)]
      ++ [mkFeature (getTextIndex i) LetLabelType | i <- Map.keys (stcBindings s)]
      ++ [mkPatternFeature i 0 | i <- IntMap.keys $ stcCnstrs s]
      ++ [mkDynFieldFeature i 0 | i <- IntMap.keys $ stcDynFields s]
  TNList l -> [mkListStoreIdxFeature i | (i, _) <- zip [0 ..] (toList l.store)]
  TNDisj d ->
    [mkDisjFeature i | (i, _) <- zip [0 ..] (dsjDisjuncts d)]
  _ -> []

{- | Generate a list of sub-trees that are stubs.

TODO: comprehension struct
-}
subStubSegs :: Tree -> [Feature]
subStubSegs (IsStruct s) =
  [mkPatternFeature i 1 | i <- IntMap.keys $ stcCnstrs s]
    ++ [mkDynFieldFeature i 1 | i <- IntMap.keys $ stcDynFields s]
    ++ [mkStubFieldFeature i | i <- Map.keys (stcStaticFieldBases s)]
subStubSegs _ = []

{- | Go to the absolute addr in the tree. No propagation is involved.

The tree must have all the latest changes.
-}
goTCAbsAddr :: TreeAddr -> TrCur -> Either String (Maybe TrCur)
goTCAbsAddr dst tc = do
  when (headSeg dst /= Just rootFeature) $
    Left (printf "the addr %s should start with the root segment" (show dst))
  top <- topTC tc
  let dstNoRoot = fromJust $ tailTreeAddr dst
  return $ goDownTCAddr dstNoRoot top

goTCAbsAddrMust :: TreeAddr -> TrCur -> Either String TrCur
goTCAbsAddrMust dst tc = do
  tarM <- goTCAbsAddr dst tc
  maybe (Left $ printf "failed to go to the addr %s" (show dst)) return tarM
