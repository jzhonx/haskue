{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Mutate where

import Common (TreeOp (isTreeBottom, treeHasRef))
import Control.Monad (unless, when)
import Control.Monad.Reader (asks)
import Cursor (
  Context (ctxCnstrValidatorAddr, ctxRefSysGraph),
  showRefSysiers,
 )
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust)
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.RMonad as RM
import Text.Printf (printf)
import Util (debugSpan, logDebugStr)
import qualified Value.Tree as VT

{- | Mutate the Mutable.

The mutation is run in the mutval environment.

The focus of the tree should still be of type Mutable after the mutation.

No global states should be changed too.
-}
mutate :: (RM.ReduceMonad s r m) => m ()
mutate = RM.mustMutable $ \m -> RM.withAddrAndFocus $ \addr _ -> do
  -- Set the mutval to the stub since mutable should not depend on the previous mutable value.
  _mustSetMutVal (Just VT.stubTree)
  let name = VT.getMutName m VT.getStringFromTree
  rM <- debugSpan (printf "mutate, addr: %s, mut: %s" (show addr) (show name)) $ case m of
    VT.Ref ref -> mutateRef ref
    VT.SFunc fn -> mutateFunc fn >> return Nothing

  -- If the mutval still exists, we should delete the notification receivers that have the /addr because once reduced,
  -- the mutval should not be notified.
  -- If the mutable has been reduced to non-mutables, then notifiers should be kept.
  RM.withTree $ \t -> case VT.treeNode t of
    VT.TNMutable mut ->
      maybe
        (return ())
        ( \mv -> do
            when (mv == VT.stubTree) _resetRMMutVal
            delMutValRecvs addr
        )
        (VT.getMutVal mut)
    _ -> return ()

  maybe
    (return ())
    ( \newT -> do
        RM.modifyRMNodeWithTree newT
        MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
        -- TODO: use a thinner reduce, which does not notify.
        reduce
    )
    rM

mutateRef :: (RM.ReduceMonad s r m) => VT.Reference VT.Tree -> m (Maybe VT.Tree)
mutateRef ref = do
  MutEnv.Functions{MutEnv.fnIndex = index} <- asks MutEnv.getFuncs

  resE <- _runInMutValEnv $ index (VT.refOrigAddrs ref) (VT.refArg ref)
  case resE of
    Left newT -> do
      RM.withAddrAndFocus $ \addr _ ->
        logDebugStr $
          printf
            "mutateRef: addr: %s, newT %s replaces the original ref"
            (show addr)
            (show newT)
      return $ Just newT
    Right tarAddrM -> do
      RM.withAddrAndFocus $ \addr focus ->
        logDebugStr $ printf "mutateRef: addr: %s, tarAddrM: %s, tar: %s" (show addr) (show tarAddrM) (show focus)
      -- Make sure the mutable is still the focus of the tree.
      assertMVNotRef

      cnstrValAddrM <- ctxCnstrValidatorAddr <$> RM.getRMContext
      -- When we are in the validating constraint phase, if the constraint value is the same as the target atom value,
      -- then we should reduce the mutable to atom.
      if tarAddrM == cnstrValAddrM && isJust tarAddrM
        then do
          RM.withAddrAndFocus $ \addr _ ->
            logDebugStr $
              printf
                "mutateRef: addr: %s, validating cnstr, tarAddrM: %s"
                (show addr)
                (show tarAddrM)
          mv <- _getRMMutVal
          case VT.treeNode <$> mv of
            Just (VT.TNAtom _) -> reduceToMutVal $ fromJust mv
            _ -> throwErrSt $ printf "constraint's atom not found, but got: %s" (show mv)
          return Nothing
        else do
          mvM <- _getRMMutVal
          if mvM == Just VT.stubTree
            then return Nothing
            else do
              MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
              _runInMutValEnv reduce
              RM.withAddrAndFocus $ \addr focus ->
                logDebugStr $ printf "mutateRef: addr: %s, reduce mv result: %s" (show addr) (show focus)

              _runWithExtMutVal $ \mv ->
                if
                  | isRefResReducible mv -> reduceToMutVal mv
                  -- The result is another mutable, when we reference another mutable.
                  | Just imut <- VT.getMutableFromTree mv ->
                      case VT.getMutVal imut of
                        Just imv -> _mustSetMutVal (Just imv)
                        -- If the function has no result, then we should set the mutval to the stub.
                        _ -> _mustSetMutVal (Just VT.stubTree)
                  | otherwise -> return ()

              return Nothing
 where
  assertMVNotRef = _runWithExtMutVal $ \mv -> case VT.getMutableFromTree mv of
    Just (VT.Ref rf)
      | VT.isRefRef rf -> throwErrSt "mutateRef: mutable value should not be a ref"
    _ -> return ()

  isRefResReducible t = isTreeBottom t || VT.isTreeRefCycleTail t || VT.isTreeStructuralCycle t

mutateFunc :: (RM.ReduceMonad s r m) => VT.StatefulFunc VT.Tree -> m ()
mutateFunc fn = RM.withTree $ \t -> do
  RM.mustMutable $ \_ -> _runInMutValEnv $ VT.invokeMutMethod fn
  assertMVNotFunc
  _runWithExtMutVal $ \mv -> when (isMutableTreeReducible t mv) $ reduceToMutVal mv
 where
  assertMVNotFunc = _runWithExtMutVal $ \mv -> case VT.getMutableFromTree mv of
    Just (VT.SFunc _) ->
      throwErrSt $
        printf "mutateFunc: mutable value of the VT.StatefulFunc should not be a VT.StatefulFunc, but got: %s" (show mv)
    _ -> return ()

  -- Check whether the mutator is reducible.
  -- The first argument is a mutable node, and the second argument is the mutval.
  isMutableTreeReducible :: VT.Tree -> VT.Tree -> Bool
  isMutableTreeReducible mut mv =
    isTreeBottom mv
      || VT.isTreeRefCycleTail mv
      || VT.isTreeStructuralCycle mv
      -- If the mutible tree does not have any references, then we can safely replace the mutible with the result.
      || not (treeHasRef mut)

-- | Replace the mutable tree node with the mutval.
reduceToMutVal :: (RM.ReduceMonad s r m) => VT.Tree -> m ()
reduceToMutVal val = do
  RM.modifyRMTN (VT.treeNode val)
  handleRefCycle

{- | Convert the RefCycleTail to VT.RefCycle if the addr is the same as the cycle start addr.

RefCycleTail is like Bottom.
-}
handleRefCycle :: (RM.ReduceMonad s r m) => m ()
handleRefCycle = RM.withTree $ \val -> case VT.treeNode val of
  VT.TNRefCycle (VT.RefCycleVertMerger (cycleStartTreeAddr, _)) -> do
    addr <- RM.getRMAbsAddr
    if Path.referableAddr cycleStartTreeAddr == Path.referableAddr addr
      then do
        logDebugStr $ printf "handleRefCycle: addr: %s, cycle head found" (show addr)
        -- The ref cycle tree must record the original tree.
        RM.modifyRMTN (VT.TNRefCycle VT.RefCycleVert)
      else RM.modifyRMTN (VT.treeNode val)
  _ -> return ()

{- | Delete the notification receivers that have the specified prefix.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delRefSysRecvPrefix :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m ()
delRefSysRecvPrefix addrPrefix = do
  RM.withContext $ \ctx -> do
    RM.putRMContext $ ctx{ctxRefSysGraph = delEmptyElem $ del (ctxRefSysGraph ctx)}
  RM.withAddrAndFocus $ \addr _ -> do
    notifiers <- ctxRefSysGraph <$> RM.getRMContext
    logDebugStr $
      printf
        "delRefSysRecvs: addr: %s delete receiver prefix: %s, updated notifiers: %s"
        (show addr)
        (show addrPrefix)
        (showRefSysiers notifiers)
 where
  delEmptyElem :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  delEmptyElem = Map.filter (not . null)

  del :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  del = Map.map (filter (\p -> not (Path.isPrefix addrPrefix p)))

{- | Delete the notification receivers of the sub values of the mutval.

If the receiver addresss is the mutable address itself, then it should be skipped because the mutable could be a
reference.

If the receiver addresss is the mutable address plus the argument segment, then it should be skipped.
-}
delMutValRecvs :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m ()
delMutValRecvs mutAddr = do
  RM.withContext $ \ctx ->
    RM.putRMContext $ ctx{ctxRefSysGraph = delEmptyElem $ delRecvs (ctxRefSysGraph ctx)}
  RM.withAddrAndFocus $ \addr _ -> do
    notifiers <- ctxRefSysGraph <$> RM.getRMContext
    logDebugStr $
      printf
        "delMutValRecvs: addr: %s delete mutval receiver: %s, updated notifiers to: %s"
        (show addr)
        (show mutAddr)
        (showRefSysiers notifiers)
 where
  delEmptyElem :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  delEmptyElem = Map.filter (not . null)

  -- Delete the receivers that have the mutable address as the prefix.
  delRecvs :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  delRecvs =
    Map.map
      ( filter
          ( \recv ->
              let
                isAddrSub = Path.isPrefix mutAddr recv && recv /= mutAddr
                rest = Path.trimPrefixTreeAddr recv mutAddr
                isAddrMutArg = isAddrSub && isSegMutArg (fromJust (Path.headSeg rest))
               in
                not isAddrSub || isAddrMutArg
          )
      )

  isSegMutArg :: Path.TASeg -> Bool
  isSegMutArg (Path.MutableArgTASeg _) = True
  isSegMutArg _ = False

{- | Reduce the argument of the mutable.

If nothing concrete can be returned, then the original argument is returned.
-}
reduceMutableArg :: (RM.ReduceMonad s r m) => Path.TASeg -> VT.Tree -> m VT.Tree
reduceMutableArg seg sub = RM.withAddrAndFocus $ \addr _ ->
  debugSpan (printf "reduceMutableArg, addr: %s, seg: %s" (show addr) (show seg)) $ do
    m <-
      mutValToArgsRM
        seg
        sub
        ( do
            MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
            reduce
            RM.withTree $ \x -> return $ case VT.treeNode x of
              VT.TNMutable mut -> Just $ fromMaybe sub (VT.getMutVal mut)
              _ -> Just x
        )
    return $ fromJust m

-- * VT.Mutable Environment

{- | Go to the parent mutable and run the action in an argument environment, then come back to the mutval environment.

The mutable must see changes propagated from the argument environment.
-}
mutValToArgsRM :: (RM.ReduceMonad s r m) => Path.TASeg -> VT.Tree -> m a -> m a
mutValToArgsRM subSeg sub f = doInMutRM $ RM.mustMutable $ \_ -> RM.inSubRM subSeg sub f
 where
  -- Run the action in the parent tree. All changes will be propagated to the parent tree and back to the current
  -- tree.
  -- After evaluating the argument environment, the focus of the tree should still be the mutable.
  doInMutRM :: (RM.ReduceMonad s r m) => m a -> m a
  doInMutRM action = do
    seg <- RM.getRMTASeg
    RM.propUpRM
    r <- action
    ok <- RM.descendRMSeg seg
    unless ok $ throwErrSt $ printf "failed to go down with seg %s" (show seg)
    return r

_runInMutValEnv :: (RM.ReduceMonad s r m) => m a -> m a
_runInMutValEnv f = RM.mustMutable $ \_ -> do
  ok <- RM.descendRMSeg Path.SubValTASeg
  unless ok $ throwErrSt "can not descend to the mutable value"
  r <- f
  RM.propUpRM
  return r

_resetRMMutVal :: (RM.ReduceMonad s r m) => m ()
_resetRMMutVal = _mustSetMutVal Nothing

_mustSetMutVal :: (RM.ReduceMonad s r m) => Maybe VT.Tree -> m ()
_mustSetMutVal m = RM.mustMutable $ \mut -> RM.modifyRMTN (VT.TNMutable $ VT.setMutVal m mut)

{- | Get the mutable value of the mutable node.

If the function can not generate a value due to incomplete arguments, then Nothing is returned.
-}
_getRMMutVal :: (RM.ReduceMonad s r m) => m (Maybe VT.Tree)
_getRMMutVal = RM.mustMutable $ \mut -> return (VT.getMutVal mut)

-- | Run the function with the existing mutable value if it exists.
_runWithExtMutVal :: (RM.ReduceMonad s r m) => (VT.Tree -> m ()) -> m ()
_runWithExtMutVal f = maybe (return ()) f =<< _getRMMutVal
