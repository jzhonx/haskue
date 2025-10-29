{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module Cursor where

import Common (ErrorEnv)
import Control.DeepSeq (NFData (..))
import Control.Monad (when)
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
import Exception (throwErrSt)
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import Path
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
  { tcFocus :: Tree
  , tcCrumbs :: [(TASeg, Tree)]
  }
  deriving (Eq, Generic, NFData)

-- | By default, only show the focus of the cursor.
instance Show TrCur where
  show = show . tcFocus

pattern TCFocus :: Tree -> TrCur
pattern TCFocus t <- TrCur{tcFocus = t}

addrFromCrumbs :: [(TASeg, Tree)] -> TreeAddr
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
tcFocusSeg :: TrCur -> Maybe TASeg
tcFocusSeg (TrCur _ []) = Nothing
tcFocusSeg tc = return $ fst . head $ tcCrumbs tc

-- | Get the segment paired with the focus of the cursor.
tcFocusSegMust :: (ErrorEnv m) => TrCur -> m TASeg
tcFocusSegMust tc = maybe (throwErrSt "already top") return (tcFocusSeg tc)

isTCTop :: TrCur -> Bool
isTCTop (TrCur _ []) = True
isTCTop _ = False

isTCRoot :: TrCur -> Bool
isTCRoot (TrCur _ [(RootTASeg, _)]) = True
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
mkSubTC :: Tree -> TASeg -> Tree -> [(TASeg, Tree)] -> TrCur
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
  go :: [TASeg] -> TrCur -> Maybe TrCur
  go [] cursor = Just cursor
  go (x : xs) cursor = do
    nextCur <- goDownTCSeg x cursor
    go xs nextCur

goDownTAddr :: TreeAddr -> Tree -> Maybe TrCur
goDownTAddr addr starT = goDownTCAddr addr (TrCur starT [])

goDownTCAddrMust :: (ErrorEnv m) => TreeAddr -> TrCur -> m TrCur
goDownTCAddrMust addr tc =
  maybe
    (throwErrSt $ printf "cannot go to addr (%s) tree from %s" (show addr) (show $ tcAddr tc))
    return
    (goDownTCAddr addr tc)

{- | Go down the TreeCursor with the given segment and return the new cursor.

It handles the cases when a node can be accessed without segments, such as the default value of a disjunction.
-}
goDownTCSeg :: TASeg -> TrCur -> Maybe TrCur
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
              return $ mkSubTC dft (DisjTASeg i) updatedParT (tcCrumbs tc)
        _ -> Nothing
      goDownTCSeg seg nextTC

goDownTCSegMust :: (ErrorEnv m) => TASeg -> TrCur -> m TrCur
goDownTCSegMust seg tc =
  maybe
    ( throwErrSt $
        printf "cannot go to sub (%s) tree from path: %s, parent: %s" (show seg) (show $ tcAddr tc) (show $ tcFocus tc)
    )
    return
    $ goDownTCSeg seg tc

{- | Propagates the changes made to the focus to the parent nodes.

It stops at the root.
-}
propUpTC :: (ErrorEnv m) => TrCur -> m TrCur
propUpTC (TrCur _ []) = throwErrSt "already at the top"
propUpTC tc@(TrCur _ [(RootTASeg, _)]) = return tc
propUpTC (TrCur subT ((seg, parT) : cs)) = do
  let tM = setSubTree seg subT parT
  case tM of
    Nothing -> throwErrSt $ printf "cannot set sub tree (%s) to parent tree %s" (show seg) (show parT)
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
subTree :: (HasCallStack) => TASeg -> Tree -> Maybe (Tree, Tree)
subTree seg parentT = do
  sub <- go seg parentT
  updatedParT <- setSubTree seg singletonNoVal parentT
  return (sub, updatedParT)
 where
  go (MutArgTASeg i) (IsTGenOp mut) = getMutArgs mut Seq.!? i
  go TempTASeg t = tmpSub t
  go _ t = case (seg, t) of
    (RootTASeg, _) -> Just t
    (BlockTASeg bseg, IsStruct struct) -> case bseg of
      StringTASeg name
        | Just sf <- lookupStructField name struct ->
            Just $ ssfValue sf
      LetTASeg name i -> lookupStructLet (letTASegToRefIdent name i) struct
      PatternTASeg i j -> (if j == 0 then scsPattern else scsValue) <$> stcCnstrs struct IntMap.!? i
      DynFieldTASeg i j ->
        (if j == 0 then dsfLabel else dsfValue) <$> stcDynFields struct IntMap.!? i
      StubFieldTASeg name
        | Just sf <- lookupStructStaticFieldBase name struct ->
            Just $ ssfValue sf
      _ -> Nothing
    (IndexTASeg i, IsList vs) -> lstSubs vs `indexList` i
    (_, IsDisj d) | DisjTASeg i <- seg -> dsjDisjuncts d `indexList` i
    _ -> Nothing

{- | Set the sub tree with the given segment and new tree.

The sub tree should already exist in the parent tree.
-}
setSubTree :: TASeg -> Tree -> Tree -> Maybe Tree
setSubTree (MutArgTASeg i) subT parT@(IsTGenOp mut) = return $ setTValGenEnv (TGenOp $ updateMutArg i subT mut) parT
setSubTree TempTASeg subT parT = return $ parT{tmpSub = Just subT}
setSubTree seg subT parT = do
  n <- case (seg, parT) of
    (BlockTASeg (StringTASeg name), IsStruct parStruct)
      -- The label segment should already exist in the parent struct. Otherwise the description of the field will not be
      -- found.
      | Just field <- lookupStructField name parStruct ->
          let
            newField = subT `updateFieldValue` field
            newStruct = updateStructField name newField parStruct
           in
            return $ TNStruct newStruct
    (BlockTASeg (PatternTASeg i j), IsStruct parStruct) ->
      return $ TNStruct (updateStructCnstrByID i (j == 0) subT parStruct)
    (BlockTASeg (DynFieldTASeg i j), IsStruct parStruct) ->
      return $ TNStruct (updateStructDynFieldByID i (j == 0) subT parStruct)
    (BlockTASeg (StubFieldTASeg name), IsStruct parStruct) ->
      return $ TNStruct (updateStructStaticFieldBase name subT parStruct)
    (BlockTASeg (LetTASeg name i), IsStruct parStruct) ->
      return $ TNStruct (updateStructLetBinding (letTASegToRefIdent name i) subT parStruct)
    (IndexTASeg i, IsList vs) ->
      let subs = lstSubs vs
          l = TNList $ vs{lstSubs = take i subs ++ [subT] ++ drop (i + 1) subs}
       in return l
    (_, IsDisj d)
      | DisjTASeg i <- seg ->
          return (TNDisj $ d{dsjDisjuncts = take i (dsjDisjuncts d) ++ [subT] ++ drop (i + 1) (dsjDisjuncts d)})
    (RootTASeg, _) -> Nothing
    _ -> Nothing
  return parT{treeNode = n}

indexList :: [a] -> Int -> Maybe a
indexList xs i = if i < length xs then Just (xs !! i) else Nothing

setSubTreeMust :: (ErrorEnv m) => TASeg -> Tree -> Tree -> m Tree
setSubTreeMust seg subT parT =
  maybe
    (throwErrSt $ printf "cannot set sub tree (%s) to parent tree %s" (show seg) (show parT))
    return
    (setSubTree seg subT parT)

-- | Go to the top of the tree cursor.
topTC :: (ErrorEnv m) => TrCur -> m TrCur
topTC (TrCur _ []) = throwErrSt "already at the top"
topTC tc@(TrCur _ ((RootTASeg, _) : _)) = return tc
topTC tc = do
  parTC <- propUpTC tc
  topTC parTC

-- = Traversal =

data SubNodeSeg = SubNodeSegNormal TASeg | SubNodeSegEmbed TASeg deriving (Eq)

-- | Generate a list of immediate sub-trees that have values to reduce, not the values that have been reduced.
subNodes :: Bool -> TrCur -> [SubNodeSeg]
subNodes withStub (TCFocus t@(IsTGenOp mut)) =
  let xs = [SubNodeSegNormal (MutArgTASeg i) | (i, _) <- zip [0 ..] (toList $ getMutArgs mut)]
      ys = subTNSegsOpt withStub t
   in xs ++ ys
subNodes withStub tc = subTNSegsOpt withStub (tcFocus tc)

subTNSegsOpt :: Bool -> Tree -> [SubNodeSeg]
subTNSegsOpt withStub t = map SubNodeSegNormal $ subTNSegs t ++ if withStub then subStubSegs t else []

subTNSegs :: Tree -> [TASeg]
subTNSegs t = case treeNode t of
  TNStruct s ->
    [BlockTASeg $ StringTASeg n | n <- Map.keys (stcFields s)]
      ++ [BlockTASeg $ refIdentToLetTASeg ident | ident <- Map.keys (stcBindings s)]
      ++ [BlockTASeg $ PatternTASeg i 0 | i <- IntMap.keys $ stcCnstrs s]
      ++ [BlockTASeg $ DynFieldTASeg i 0 | i <- IntMap.keys $ stcDynFields s]
  TNList l -> [IndexTASeg i | (i, _) <- zip [0 ..] (lstSubs l)]
  TNDisj d ->
    [DisjTASeg i | (i, _) <- zip [0 ..] (dsjDisjuncts d)]
  _ -> []

{- | Generate a list of sub-trees that are stubs.

TODO: comprehension struct
-}
subStubSegs :: Tree -> [TASeg]
subStubSegs (IsStruct s) =
  [BlockTASeg $ PatternTASeg i 1 | i <- IntMap.keys $ stcCnstrs s]
    ++ [BlockTASeg $ DynFieldTASeg i 1 | i <- IntMap.keys $ stcDynFields s]
    ++ [BlockTASeg $ StubFieldTASeg name | name <- Map.keys $ stcStaticFieldBases s]
subStubSegs _ = []

{- | Go to the absolute addr in the tree. No propagation is involved.

The tree must have all the latest changes.
-}
goTCAbsAddr :: (ErrorEnv m) => TreeAddr -> TrCur -> m (Maybe TrCur)
goTCAbsAddr dst tc = do
  when (headSeg dst /= Just RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  top <- topTC tc
  let dstNoRoot = fromJust $ tailTreeAddr dst
  return $ goDownTCAddr dstNoRoot top

goTCAbsAddrMust :: (ErrorEnv m) => TreeAddr -> TrCur -> m TrCur
goTCAbsAddrMust dst tc = do
  tarM <- goTCAbsAddr dst tc
  maybe (throwErrSt $ printf "failed to go to the addr %s" (show dst)) return tarM
