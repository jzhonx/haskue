{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Mutate where

import Class
import Control.Monad (void)
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

The mutation is run in the sub-tree indicated by MutableValSelector. The mutMethod result will be put in the mutVal.

The focus of the tree should still be of type Mutable after the mutation.
No global states should be changed too.
-}
mutate :: (TreeMonad s m) => m ()
mutate = mustMutable $ \m -> withDebugInfo $ \path _ -> do
  let name = mutName m
  debugSpan (printf "mutate, path: %s, mut: %s" (show path) (show name)) $ do
    -- modified is not equivalent to reducible. For example, if the unification generates a new struct, it is not
    -- enough to replace the mutable with the new struct.
    inSubTM (MutableSelector MutableValSelector) (mkMutableTree mutValStub) (invokeMutMethod m)

    -- Make sure the mutable is still the focus of the tree.
    withTree $ \_ -> mustMutable $ \mut ->
      case mutValue mut of
        Nothing -> throwErrSt "mutable value is lost"
        Just res -> do
          logDebugStr $ printf "mutate: path: %s, mut %s, result:\n%s" (show path) (show name) (show res)
          case getMutableFromTree res of
            Just nm ->
              if nm == mutValStub
                then do
                  -- The mutable is not mutated, so we need to reset the mutable value to Nothing.
                  putTMTree $ mkMutableTree $ resetMutableVal mut
                else do
                  -- recursively mutate in mutval env until the result is not a mutable.
                  putTMTree res >> mutate
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

            withDebugInfo $ \path _ -> do
              logDebugStr $
                printf
                  "tryReduceMut: func %s, path: %s, is reducible: %s, args: %s"
                  (show $ mutName mut)
                  (show path)
                  (show reducible)
                  (show $ mutArgs mut)

            if reducible
              then do
                handleRefCycle val
                --
                path <- getTMAbsPath
                delNotifRecvPrefix path
              else
                -- Not reducible, we need to update the mutable value.
                putTMTree (mkMutableTree $ setMutableState mut val)
            return reducible
    )
    valM

{- | Convert the RefCycleTail to RefCycle if the path is the same as the cycle start path.

RefCycleTail is like Bottom.
-}
handleRefCycle :: (TreeMonad s m) => Tree -> m ()
handleRefCycle val = case treeNode val of
  TNRefCycle (RefCycleTail (cycleStartPath, _)) -> do
    path <- getTMAbsPath
    if cycleStartPath == path
      then do
        logDebugStr $ printf "handleRefCycle: path: %s, cycle head found" (show path)
        -- The ref cycle tree must record the original tree.
        withTree $ \t -> putTMTree $ convRefCycleTree t False
      else putTMTree val
  _ -> putTMTree val

{- | Delete the notification receivers that have the specified prefix.

This should be called when the reference becomes invalid.

we need to delete receiver starting with the path, not only the path. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delNotifRecvPrefix :: (TMonad s m t) => Path -> m ()
delNotifRecvPrefix pathPrefix = do
  withContext $ \ctx -> do
    putTMContext $ ctx{ctxNotifiers = del (ctxNotifiers ctx)}
  withDebugInfo $ \path _ -> do
    notifiers <- ctxNotifiers <$> getTMContext
    logDebugStr $
      printf
        "delNotifRecvs: path: %s delete receiver prefix: %s, ref_path: %s, updated notifiers: %s"
        (show path)
        (show pathPrefix)
        (show refPathPrefix)
        (show notifiers)
 where
  refPathPrefix = treeRefPath pathPrefix

  del :: Map.Map Path [Path] -> Map.Map Path [Path]
  del = Map.map (filter (\p -> not (isPrefix refPathPrefix p)))
