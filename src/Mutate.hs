{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Mutate where

import Class
import Config
import Control.Monad (void)
import Control.Monad.Reader (ask)
import Cursor
import qualified Data.Map.Strict as Map
import Error
import Path
import TMonad
import Text.Printf (printf)
import Util
import Value.Tree

{- | Check whether the mutator is reducible.

The first argument is a mutable node, and the second argument is the value of the mutable.
-}
isMutableTreeReducible :: Tree -> Tree -> Bool
isMutableTreeReducible fnt res =
  treeHasAtom res
    || isTreeBottom res
    || isTreeRefCycleTail res
    -- If the mutible tree does not have any references, then we can safely replace the mutible with the result.
    || not (treeHasRef fnt)

{- | Mutate the Mutable. If the previous mutable mutates to another mutable, then this function will be recursively
 - called.

@param reduceTar: whether to reduce the deref'd value.

The mutation is run in the sub-tree indicated by MutableValTASeg. The mutMethod result will be put in the mutVal.

The focus of the tree should still be of type Mutable after the mutation.
No global states should be changed too.
-}
mutate :: (TreeMonad s m) => Bool -> m ()
mutate skipReduce = mustMutable $ \m -> withAddrAndFocus $ \addr _ -> do
  let name = getMutName m
  debugSpan (printf "mutate, addr: %s, mut: %s" (show addr) (show name)) $ do
    -- modified is not equivalent to reducible. For example, if the unification generates a new struct, it is not
    -- enough to replace the mutable with the new struct.
    Config{cfDeref = deref} <- ask
    inSubTM
      (MutableTASeg MutableValTASeg)
      mutValStubTree
      ( case m of
          Ref ref -> deref (refPath ref) skipReduce
          SFunc mut -> invokeMutMethod mut
      )

    -- Make sure the mutable is still the focus of the tree.
    withTree $ \_ -> mustMutable $ \mut ->
      case getMutVal mut of
        Nothing -> throwErrSt "mutable value is lost"
        Just res -> do
          logDebugStr $ printf "mutate: addr: %s, mut %s, result:\n%s" (show addr) (show name) (show res)
          case getMutableFromTree res of
            Just nm ->
              if nm == mutValStub
                then do
                  -- The mutable is not mutated, so we need to reset the mutable value to Nothing.
                  putTMTree $ mkMutableTree $ resetMutVal mut
                else do
                  -- recursively mutate in mutval env until the result is not a mutable.
                  putTMTree res >> mutate skipReduce
            Nothing -> void $ tryReduceMut (Just res)

{- | Try to reduce the mutable by using the mutate result to replace the mutable node.

This should be called after the mutable is evaluated.
-}
tryReduceMut :: (TreeMonad s m) => Maybe Tree -> m Bool
tryReduceMut valM = withTree $ \t -> mustMutable $ \mut ->
  maybe
    (return False)
    ( \val ->
        if isTreeMutable val
          -- If the mutable returns another mutable, then it is not reducible.
          then putTMTree val >> return False
          else do
            let reducible = isMutableTreeReducible t val

            withAddrAndFocus $ \addr _ -> do
              logDebugStr $
                printf
                  "tryReduceMut: func %s, addr: %s, %s is reducible: %s"
                  (show $ getMutName mut)
                  (show addr)
                  (show val)
                  (show reducible)

            if reducible
              then do
                putTMTree val
                handleRefCycle
                --
                addr <- getTMAbsAddr
                delNotifRecvPrefix addr
              else
                -- Not reducible, we need to update the mutable value.
                putTMTree (mkMutableTree $ setMutVal mut val)
            return reducible
    )
    valM

{- | Convert the RefCycleTail to RefCycle if the addr is the same as the cycle start addr.

RefCycleTail is like Bottom.
-}
handleRefCycle :: (TreeMonad s m) => m ()
handleRefCycle = withTree $ \val -> case treeNode val of
  TNRefCycle (RefCycleVertMerger (cycleStartTreeAddr, _)) -> do
    addr <- getTMAbsAddr
    if cycleStartTreeAddr == addr
      then do
        logDebugStr $ printf "handleRefCycle: addr: %s, cycle head found" (show addr)
        -- The ref cycle tree must record the original tree.
        withTree $ \t -> putTMTree $ convRefCycleTree t
      else putTMTree val
  _ -> return ()

{- | Delete the notification receivers that have the specified prefix.

This should be called when the reference becomes invalid.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delNotifRecvPrefix :: (TMonad s m t) => TreeAddr -> m ()
delNotifRecvPrefix addrPrefix = do
  withContext $ \ctx -> do
    putTMContext $ ctx{ctxNotifiers = del (ctxNotifiers ctx)}
  withAddrAndFocus $ \addr _ -> do
    notifiers <- ctxNotifiers <$> getTMContext
    logDebugStr $
      printf
        "delNotifRecvs: addr: %s delete receiver prefix: %s, ref_addr: %s, updated notifiers: %s"
        (show addr)
        (show addrPrefix)
        (show refTreeAddrPrefix)
        (show $ Map.toList notifiers)
 where
  refTreeAddrPrefix = getReferableAddr addrPrefix

  del :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  del = Map.map (filter (\p -> not (isPrefix refTreeAddrPrefix p)))
