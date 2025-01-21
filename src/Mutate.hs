{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Mutate where

import Class
import Config
import Control.Monad (when)
import Control.Monad.Reader (ask)
import Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import Error
import Path
import TMonad
import Text.Printf (printf)
import Util
import Value.Tree as VT

{- | Check whether the mutator is reducible.

The first argument is a mutable node, and the second argument is the value of the mutable.
-}
isMutableTreeReducible :: Tree -> Tree -> Bool
isMutableTreeReducible fnT res =
  treeHasAtom res
    || isTreeBottom res
    || isTreeRefCycleTail res
    || isTreeStructuralCycle res
    -- If the mutible tree does not have any references, then we can safely replace the mutible with the result.
    || not (treeHasRef fnT)

{- | Mutate the Mutable. If the previous mutable mutates to another mutable, then this function will be recursively
 - called.

The mutation is run in the sub-tree indicated by MutableValTASeg. The mutMethod result will be put in the mutVal.

The focus of the tree should still be of type Mutable after the mutation.
No global states should be changed too.
-}
mutate :: (TreeMonad s m) => m ()
mutate = mustMutable $ \m -> withAddrAndFocus $ \addr _ -> do
  let name = getMutName m
  debugSpan (printf "mutate, addr: %s, mut: %s" (show addr) (show name)) $ case m of
    Ref ref -> mutateRef ref
    SFunc fn -> mutateFunc fn
    Index idx -> mutateIndexer idx
    MutStub -> throwErrSt "mutate a stub"

  -- If the mutval still exists, we should delete the notification receivers that have the /addr because once reduced,
  -- the mutval should not be notified.
  -- If the mutable has been reduced to non-mutables, then notifiers should be kept.
  withTree $ \t ->
    maybe
      (return ())
      (const $ delMutValRecvs addr)
      (getMutableFromTree t)

mutateRef :: (TreeMonad s m) => VT.Reference Tree -> m ()
mutateRef ref = do
  Config{cfDeref = deref} <- ask
  runInMutValEnv $ deref (refPath ref) (refOrigAddrs ref)
  withAddrAndFocus $ \addr focus ->
    logDebugStr $ printf "mutateRef: addr: %s, deref result: %s" (show addr) (show focus)

  -- Make sure the mutable is still the focus of the tree.
  assertMVNotRef

  Config{cfReduce = reduce} <- ask
  runWithMutVal reduce
  withAddrAndFocus $ \addr focus ->
    logDebugStr $ printf "mutateRef: addr: %s, reduce mv result: %s" (show addr) (show focus)
  maybe
    (return ())
    ( \mv ->
        if
          | isRefResReducible mv -> reduceToMutVal mv
          -- If the result is another mutable
          | Just imut <- getMutableFromTree mv -> do
              case getMutVal imut of
                Just imv -> mustSetMutValTree imv
                -- If the function has no result, then we need to reset the mutable value to Nothing.
                _ -> resetTMMutVal
          | otherwise -> return ()
    )
    =<< getTMMutVal
 where
  assertMVNotRef = do
    mvM <- getTMMutVal
    case mvM >>= getMutableFromTree of
      Just (Ref _) -> throwErrSt "mutateRef: mutable value should not be a ref"
      _ -> return ()

  isRefResReducible t = treeHasAtom t || isTreeBottom t || isTreeRefCycleTail t || isTreeStructuralCycle t

mutateFunc :: (TreeMonad s m) => StatefulFunc Tree -> m ()
mutateFunc fn = withTree $ \t -> do
  mustMutable $ \_ -> runInMutValEnv $ invokeMutMethod fn
  assertMVNotFunc
  maybe
    (return ())
    (\mv -> when (isMutableTreeReducible t mv) $ reduceToMutVal mv)
    =<< getTMMutVal
 where
  assertMVNotFunc = do
    mvM <- getTMMutVal
    case mvM >>= getMutableFromTree of
      Just (SFunc _) ->
        throwErrSt $
          printf "mutateFunc: mutable value of the StatefulFunc should not be a StatefulFunc, but got: %s" (show mvM)
      _ -> return ()

mutateIndexer :: (TreeMonad s m) => Indexer Tree -> m ()
mutateIndexer idxer = do
  Config{cfIndex = index, cfReduce = reduce} <- ask
  mustMutable $ \_ -> runInMutValEnv $ index (idxOrigAddrs idxer) (idxSels idxer)
  maybe
    (return ())
    ( \mv ->
        case getMutableFromTree mv of
          -- If the mutval is a ref, then we need to replace the mutable with the result and reduce it.
          Just (Ref _) -> do
            modifyTMTN (treeNode mv)
            reduce
          _ -> reduceToMutVal mv
    )
    =<< getTMMutVal

-- | Replace the mutable tree node with the mutval.
reduceToMutVal :: (TreeMonad s m) => Tree -> m ()
reduceToMutVal val = do
  modifyTMTN (treeNode val)
  handleRefCycle

{- | Convert the RefCycleTail to RefCycle if the addr is the same as the cycle start addr.

RefCycleTail is like Bottom.
-}
handleRefCycle :: (TreeMonad s m) => m ()
handleRefCycle = withTree $ \val -> case treeNode val of
  TNRefCycle (RefCycleVertMerger (cycleStartTreeAddr, _)) -> do
    addr <- getTMAbsAddr
    if referableAddr cycleStartTreeAddr == referableAddr addr
      then do
        logDebugStr $ printf "handleRefCycle: addr: %s, cycle head found" (show addr)
        -- The ref cycle tree must record the original tree.
        modifyTMTN (TNRefCycle RefCycleVert)
      else modifyTMTN (treeNode val)
  _ -> return ()

{- | Delete the notification receivers that have the specified prefix.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delNotifRecvPrefix :: (TMonad s m t) => TreeAddr -> m ()
delNotifRecvPrefix addrPrefix = do
  withContext $ \ctx -> do
    putTMContext $ ctx{ctxNotifGraph = delEmptyElem $ del (ctxNotifGraph ctx)}
  withAddrAndFocus $ \addr _ -> do
    notifiers <- ctxNotifGraph <$> getTMContext
    logDebugStr $
      printf
        "delNotifRecvs: addr: %s delete receiver prefix: %s, updated notifiers: %s"
        (show addr)
        (show addrPrefix)
        (showNotifiers notifiers)
 where
  delEmptyElem :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  delEmptyElem = Map.filter (not . null)

  del :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  del = Map.map (filter (\p -> not (isPrefix addrPrefix p)))

{- | Delete the notification receivers of the sub values of the mutval.

If the receiver addresss is the mutable address itself, then it should be skipped because the mutable could be a
reference.

If the receiver addresss is the mutable address plus the argument segment, then it should be skipped.
-}
delMutValRecvs :: (TMonad s m t) => TreeAddr -> m ()
delMutValRecvs mutAddr = do
  withContext $ \ctx ->
    putTMContext $ ctx{ctxNotifGraph = delEmptyElem $ delRecvs (ctxNotifGraph ctx)}
  withAddrAndFocus $ \addr _ -> do
    notifiers <- ctxNotifGraph <$> getTMContext
    logDebugStr $
      printf
        "delMutValRecvs: addr: %s delete mutval receiver: %s, updated notifiers to: %s"
        (show addr)
        (show mutAddr)
        (showNotifiers notifiers)
 where
  delEmptyElem :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  delEmptyElem = Map.filter (not . null)

  -- Delete the receivers that have the mutable address as the prefix.
  delRecvs :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  delRecvs =
    Map.map
      ( filter
          ( \recv ->
              let
                isAddrSub = isPrefix mutAddr recv && recv /= mutAddr
                rest = trimPrefixTreeAddr recv mutAddr
                isAddrMutArg = isAddrSub && isSegMutArg (fromJust (headSeg rest))
               in
                not isAddrSub || isAddrMutArg
          )
      )

  isSegMutArg :: TASeg -> Bool
  isSegMutArg (MutableTASeg (MutableArgTASeg _)) = True
  isSegMutArg _ = False

runInMutValEnv :: (TreeMonad s m) => m () -> m ()
runInMutValEnv f = do
  mustMutable $ \mut -> do
    let sub = fromMaybe mutValStubTree (getMutVal mut)
    inSubTM (MutableTASeg MutableValTASeg) sub f
  mustMutable $ \mut -> do
    -- If the function can not generate a value due to incomplete arguments, reset the mutable value.
    mv <-
      maybe
        (throwErrSt $ printf "mutable value is lost, mut: %s" (show $ mkMutableTree mut))
        return
        (getMutVal mut)
    when (mv == mutValStubTree) resetTMMutVal

runWithMutVal :: (TreeMonad s m) => m () -> m ()
runWithMutVal f = do
  mvM <- getTMMutVal
  maybe
    (return ())
    (\_ -> runInMutValEnv f)
    mvM

resetTMMutVal :: (TreeMonad s m) => m ()
resetTMMutVal = mustMutable $ \mut -> modifyTMTN (TNMutable $ setMutVal Nothing mut)

mustSetMutValTree :: (TreeMonad s m) => Tree -> m ()
mustSetMutValTree t = mustMutable $ \mut -> modifyTMTN (TNMutable $ setMutVal (Just t) mut)

{- | Get the mutable value of the mutable node.

If the function can not generate a value due to incomplete arguments, then Nothing is returned.
-}
getTMMutVal :: (TreeMonad s m) => m (Maybe Tree)
getTMMutVal = mustMutable $ \mut -> return (getMutVal mut)
