{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Ref where

import Control.Monad (unless, void)
import Control.Monad.Except (throwError)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Set as Set
import Path
import Text.Printf (printf)
import Util
import Value.Tree

tryPopulateRef :: (TreeMonad s m) => Tree -> ((TreeMonad s m) => Func Tree -> m ()) -> m ()
tryPopulateRef nt evalFunc = do
  withDebugInfo $ \path _ ->
    logDebugStr $
      printf "tryPopulateRef: path: %s, new value: %s" (show path) (show nt)
  withCtxTree $ \ct -> do
    let
      resPath = cvPath ct
      notifers = ctxNotifiers . cvCtx $ ct
      deps = fromMaybe [] (Map.lookup resPath notifers)
    withDebugInfo $ \path _ ->
      unless (null deps) $
        logDebugStr $
          printf "tryPopulateRef: path: %s, using value to update %s" (show path) (show deps)
    mapM_ (\dep -> inAbsRemoteTM dep (populateRef nt evalFunc)) deps

{- | Substitute the cached result of the Func node pointed by the path with the new non-function value. Then trigger the
 - re-evluation of the lowest ancestor Func.
-}
populateRef :: (TreeMonad s m) => Tree -> ((TreeMonad s m) => Func Tree -> m ()) -> m ()
populateRef nt evalFunc = do
  withDebugInfo $ \path t ->
    logDebugStr $ printf "populateRef: path: %s, focus: %s, new value: %s" (show path) (show t) (show nt)
  withTree $ \tar -> case (treeNode tar, treeNode nt) of
    -- If the new value is a function, just skip the reduction.
    (TNFunc _, TNFunc _) -> return ()
    (TNFunc fn, _) -> do
      unless (isFuncRef fn) $
        throwError $
          printf "populateRef: the target node %s is not a reference." (show tar)

      void $ reduceFunc (Just nt)
    _ -> throwError $ printf "populateRef: the target node %s is not a function." (show tar)

  res <- getTMTree
  withDebugInfo $ \path _ ->
    logDebugStr $ printf "populateRef: path: %s, function reduced to: %s" (show path) (show res)

  -- Locate the lowest ancestor function to trigger the re-evaluation of the ancestor function.
  locateLAFunc
  withTree $ \t -> case treeNode t of
    TNFunc fn
      | isFuncRef fn -> do
          -- If it is a reference, the re-evaluation can be skipped because
          -- 1. The highest function is actually itself.
          -- 2. Re-evaluating the reference would get the same value.
          withDebugInfo $ \path _ ->
            logDebugStr $
              printf
                "populateRef: lowest ancestor function is a reference, skip re-evaluation. path: %s, node: %s"
                (show path)
                (show t)
      -- re-evaluate the highest function when it is not a reference.
      | otherwise -> do
          withDebugInfo $ \path _ ->
            logDebugStr $ printf "populateRef: re-evaluating the lowest ancestor function, path: %s, node: %s" (show path) (show t)
          r <- evalFunc fn >> getTMTree
          tryPopulateRef r evalFunc
    _ ->
      if isTreeFunc res
        then throwError $ printf "populateRef: the lowest ancestor node %s is not a function" (show t)
        else logDebugStr "populateRef: the lowest ancestor node is not found"

-- Locate the lowest ancestor node of type regular function.
locateLAFunc :: (TreeMonad s m) => m ()
locateLAFunc = do
  path <- getTMAbsPath
  if hasEmptyPath path || not (hasFuncSel path)
    then return ()
    else propUpTM >> locateLAFunc
 where
  hasEmptyPath (Path.Path sels) = null sels
  hasFuncSel (Path.Path sels) =
    any
      ( \case
          (FuncSelector (FuncArgSelector _)) -> True
          _ -> False
      )
      sels

-- Dereference the reference. It keeps dereferencing until the target node is not a reference node.
-- If the target is not found, the current node is kept.
-- No more evaluation is done after the dereference.
deref :: (TreeMonad s m) => Path -> m Bool
deref tp = do
  path <- getTMAbsPath
  withDebugInfo $ \_ t ->
    logDebugStr $
      printf
        "deref: path: %s, start:, ref_path: %s, tip: %s"
        (show path)
        (show tp)
        (show t)
  follow tp Set.empty >>= \case
    (Just (_, tar)) -> do
      withDebugInfo $ \_ t ->
        logDebugStr $
          printf
            "deref: path: %s, done: ref_path: %s, tip: %s, tar: %s"
            (show path)
            (show tp)
            (show t)
            (show tar)

      putTMTree tar
      return True
    Nothing -> return False
 where
  -- Keep dereferencing until the target node is not a reference node.
  -- The refsSeen keeps track of the followed references to detect cycles.
  -- returns the target node.
  follow :: (TreeMonad s m) => Path -> Set.Set Path -> m (Maybe (Path, Tree))
  follow ref refsSeen = do
    resM <- getDstVal ref refsSeen
    case resM of
      Nothing -> return Nothing
      Just (origPath, orig) -> do
        withDebugInfo $ \path _ -> do
          logDebugStr $ printf "deref: path: %s, substitutes with orig_path: %s, orig: %s" (show path) (show origPath) (show orig)
        -- substitute the reference with the target node.
        putTMTree orig
        withTN $ \case
          -- follow the reference.
          TNFunc fn | isFuncRef fn -> do
            nextDst <-
              maybe
                (throwError "deref: can not generate path from the arguments")
                return
                (treesToPath (fncArgs fn))
            follow nextDst (Set.insert ref refsSeen)
          _ -> return resM

  -- Get the value pointed by the reference.
  -- If the reference path is self or visited, then return the tuple of the absolute path of the start of the cycle and
  -- the cycle tail relative path.
  getDstVal :: (TreeMonad s m) => Path -> Set.Set Path -> m (Maybe (Path, Tree))
  getDstVal ref refsSeen = do
    srcPath <- getTMAbsPath
    inRemoteTMMaybe ref $ do
      dstPath <- getTMAbsPath
      logDebugStr $
        printf "deref: getDstVal ref: %s, dstPath: %s, seen: %s" (show ref) (show dstPath) (show $ Set.toList refsSeen)
      let
        canSrcPath = canonicalizePath srcPath
        canDstPath = canonicalizePath dstPath
      val <-
        if
          -- This handles the case when following the chain of references leads to a cycle.
          -- For example, { a: b, b: a, d: a } and we are at d.
          -- The the values of d would be: 1. a -> b, 2. b -> a, 3. a (seen) -> RC.
          -- The returned RC would be a self-reference cycle, which has empty path because the cycle is formed by all
          -- references.
          | Set.member ref refsSeen -> do
              logDebugStr $ printf "deref: reference cycle detected: %s, seen: %s" (show ref) (show $ Set.toList refsSeen)
              return $ Just . mkNewTree $ TNRefCycle (RefCycle True)
          -- This handles the case when the reference refers to itself that is the ancestor.
          -- For example, { a: a + 1 } or { a: !a }.
          -- The tree representation of the latter is,
          -- { }
          --  | - a
          -- (!)
          --  | - unary_op
          -- ref_a
          | canDstPath == canSrcPath && srcPath /= dstPath -> do
              logDebugStr $ printf "deref: reference tail cycle detected: %s == %s." (show dstPath) (show srcPath)
              return $ Just . mkNewTree $ TNRefCycle (RefCycleTail (dstPath, relPath dstPath srcPath))
          -- return $ Left (dstPath, relPath dstPath srcPath)
          | isPrefix canDstPath canSrcPath && srcPath /= dstPath ->
              throwError $ printf "structural cycle detected. %s is a prefix of %s" (show dstPath) (show srcPath)
          -- The value of a reference is a copy of the expression associated with the field that it is bound to, with
          -- any references within that expression bound to the respective copies of the fields they were originally
          -- bound to.
          | otherwise -> withTree $ \tar -> case treeNode tar of
              -- The atom value is final, so we can return it directly.
              TNAtom _ -> return $ Just tar
              TNConstraint c -> return $ Just (mkAtomVTree $ cnsAtom c)
              _ -> do
                let x = fromMaybe tar (treeOrig tar)
                    -- back up the original tree.
                    orig = x{treeOrig = Just x}
                logDebugStr $
                  printf
                    "deref: path: %s, deref'd orig is: %s, set: %s, tar: %s"
                    (show dstPath)
                    (show orig)
                    (show $ Set.toList refsSeen)
                    (show tar)
                return $ Just orig
      return $ (dstPath,) <$> val

  inRemoteTMMaybe :: (TreeMonad s m) => Path -> m (Maybe a) -> m (Maybe a)
  inRemoteTMMaybe p f = do
    origAbsPath <- getTMAbsPath
    tarM <- goLowestAncPathTM p (Just <$> getTMTree)
    res <- maybe (return Nothing) (\x -> putTMTree x >> f) tarM
    backM <- goTMAbsPath origAbsPath
    unless backM $ throwError "inRemoteTMMaybe: failed to go back to the original path"
    return res
