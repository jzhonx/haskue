{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Mutate where

import Class (TreeOp (isTreeBottom, treeHasRef))
import Config (
  Config (cfFunctions),
  Functions (Functions, fnDeref, fnIndex, fnReduce),
 )
import Control.Monad (unless, when)
import Control.Monad.Reader (asks)
import Cursor (
  Context (ctxCnstrValidatorAddr, ctxNotifGraph),
  showNotifiers,
 )
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import Exception (throwErrSt)
import Path (
  TASeg (MutableArgTASeg, SubValTASeg),
  TreeAddr,
  headSeg,
  isPrefix,
  referableAddr,
  trimPrefixTreeAddr,
 )
import TMonad (
  TreeMonad,
  descendTMSeg,
  getTMAbsAddr,
  getTMContext,
  modifyTMTN,
  mustMutable,
  propUpTM,
  putTMContext,
  withAddrAndFocus,
  withContext,
  withTree,
 )
import Text.Printf (printf)
import Util (debugSpan, logDebugStr)
import Value.Tree as VT (
  Indexer (idxOrigAddrs, idxSels),
  Mutable (Index, Ref, SFunc),
  RefCycle (RefCycleVert, RefCycleVertMerger),
  Reference (refOrigAddrs, refPath),
  StatefulFunc,
  Tree (treeNode),
  TreeNode (TNAtom, TNMutable, TNRefCycle),
  getMutName,
  getMutVal,
  getMutableFromTree,
  invokeMutMethod,
  isTreeRefCycleTail,
  isTreeStructuralCycle,
  setMutVal,
  stubTree,
 )

{- | Mutate the Mutable. If the previous mutable mutates to another mutable, then this function will be recursively
 - called.

The mutation is run in the sub-tree indicated by MutableValTASeg. The mutMethod result will be put in the mutVal.

The focus of the tree should still be of type Mutable after the mutation.
No global states should be changed too.
-}
mutate :: (TreeMonad s m) => m ()
mutate = mustMutable $ \m -> withAddrAndFocus $ \addr _ -> do
  _mustSetMutVal (Just stubTree)
  let name = getMutName m
  debugSpan (printf "mutate, addr: %s, mut: %s" (show addr) (show name)) $ case m of
    Ref ref -> mutateRef ref
    SFunc fn -> mutateFunc fn
    Index idx -> mutateIndexer idx

  -- If the mutval still exists, we should delete the notification receivers that have the /addr because once reduced,
  -- the mutval should not be notified.
  -- If the mutable has been reduced to non-mutables, then notifiers should be kept.
  withTree $ \t -> case treeNode t of
    TNMutable mut ->
      maybe
        (return ())
        ( \mv -> do
            when (mv == stubTree) _resetTMMutVal
            delMutValRecvs addr
        )
        (getMutVal mut)
    _ -> return ()

mutateRef :: (TreeMonad s m) => VT.Reference Tree -> m ()
mutateRef ref = do
  Functions{fnDeref = deref} <- asks cfFunctions
  -- Set the mutval to the stub since mutable should not depend on the previous mutable value.
  tarAddrM <- _runInMutValEnv $ deref (refPath ref) (refOrigAddrs ref)
  withAddrAndFocus $ \addr focus ->
    logDebugStr $ printf "mutateRef: addr: %s, tarAddr: %s, tar: %s" (show addr) (show tarAddrM) (show focus)

  -- Make sure the mutable is still the focus of the tree.
  assertMVNotRef

  cnstrValAddrM <- ctxCnstrValidatorAddr <$> getTMContext
  -- When we are in the validating constraint phase, if the constraint value is the same as the target atom value,
  -- then we should reduce the mutable to atom.
  if tarAddrM == cnstrValAddrM && isJust tarAddrM
    then do
      withAddrAndFocus $ \addr _ ->
        logDebugStr $
          printf
            "mutateRef: addr: %s, validating cnstr, tarAddrM: %s"
            (show addr)
            (show tarAddrM)
      mv <- _getTMMutVal
      case treeNode <$> mv of
        Just (TNAtom _) -> reduceToMutVal $ fromJust mv
        _ -> throwErrSt $ printf "constraint's atom not found, but got: %s" (show mv)
    else do
      mvM <- _getTMMutVal
      if mvM == Just stubTree
        then return ()
        else do
          Functions{fnReduce = reduce} <- asks cfFunctions
          _runInMutValEnv reduce
          withAddrAndFocus $ \addr focus ->
            logDebugStr $ printf "mutateRef: addr: %s, reduce mv result: %s" (show addr) (show focus)

          _runWithExtMutVal $ \mv ->
            if
              | isRefResReducible mv -> reduceToMutVal mv
              -- The result is another mutable, when we reference another mutable.
              | Just imut <- getMutableFromTree mv ->
                  case getMutVal imut of
                    Just imv -> _mustSetMutVal (Just imv)
                    -- If the function has no result, then we should set the mutval to the stub.
                    _ -> _mustSetMutVal (Just stubTree)
              | otherwise -> return ()
 where
  assertMVNotRef = _runWithExtMutVal $ \mv -> case getMutableFromTree mv of
    Just (Ref _) -> throwErrSt "mutateRef: mutable value should not be a ref"
    _ -> return ()

  isRefResReducible t = isTreeBottom t || isTreeRefCycleTail t || isTreeStructuralCycle t

mutateFunc :: (TreeMonad s m) => StatefulFunc Tree -> m ()
mutateFunc fn = withTree $ \t -> do
  mustMutable $ \_ -> _runInMutValEnv $ invokeMutMethod fn
  assertMVNotFunc
  _runWithExtMutVal $ \mv -> when (isMutableTreeReducible t mv) $ reduceToMutVal mv
 where
  assertMVNotFunc = _runWithExtMutVal $ \mv -> case getMutableFromTree mv of
    Just (SFunc _) ->
      throwErrSt $
        printf "mutateFunc: mutable value of the StatefulFunc should not be a StatefulFunc, but got: %s" (show mv)
    _ -> return ()

  -- Check whether the mutator is reducible.
  --
  --  The first argument is a mutable node, and the second argument is the mutval.
  isMutableTreeReducible :: Tree -> Tree -> Bool
  isMutableTreeReducible mut mv =
    isTreeBottom mv
      || isTreeRefCycleTail mv
      || isTreeStructuralCycle mv
      -- If the mutible tree does not have any references, then we can safely replace the mutible with the result.
      || not (treeHasRef mut)

mutateIndexer :: (TreeMonad s m) => Indexer Tree -> m ()
mutateIndexer idxer = do
  Functions{fnIndex = index, fnReduce = reduce} <- asks cfFunctions
  mustMutable $ \_ -> _runInMutValEnv $ index (idxOrigAddrs idxer) (idxSels idxer)
  _runWithExtMutVal $ \mv -> case getMutableFromTree mv of
    -- If the mutval is a ref, then we need to replace the mutable with the result and reduce it.
    Just (Ref _) -> do
      modifyTMTN (treeNode mv)
      reduce
    _ -> reduceToMutVal mv

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
delNotifRecvPrefix :: (TreeMonad s m) => TreeAddr -> m ()
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
delMutValRecvs :: (TreeMonad s m) => TreeAddr -> m ()
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
  isSegMutArg (MutableArgTASeg _) = True
  isSegMutArg _ = False

_runInMutValEnv :: (TreeMonad s m) => m a -> m a
_runInMutValEnv f = mustMutable $ \_ -> do
  ok <- descendTMSeg SubValTASeg
  unless ok $ throwErrSt "can not descend to the mutable value"
  r <- f
  propUpTM
  return r

_resetTMMutVal :: (TreeMonad s m) => m ()
_resetTMMutVal = _mustSetMutVal Nothing

_mustSetMutVal :: (TreeMonad s m) => Maybe Tree -> m ()
_mustSetMutVal m = mustMutable $ \mut -> modifyTMTN (TNMutable $ setMutVal m mut)

{- | Get the mutable value of the mutable node.

If the function can not generate a value due to incomplete arguments, then Nothing is returned.
-}
_getTMMutVal :: (TreeMonad s m) => m (Maybe Tree)
_getTMMutVal = mustMutable $ \mut -> return (getMutVal mut)

-- | Run the function with the existing mutable value if it exists.
_runWithExtMutVal :: (TreeMonad s m) => (Tree -> m ()) -> m ()
_runWithExtMutVal f = maybe (return ()) f =<< _getTMMutVal