{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Ref where

import Control.Monad (unless)
import Control.Monad.Except (throwError)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Path
import Text.Printf (printf)
import Util
import Value.Tree

tryPopulateRef :: (TreeMonad s m) => Tree -> ((TreeMonad s m) => Func Tree -> m ()) -> m ()
tryPopulateRef nt evalFunc = do
  withCtxTree $ \ct -> do
    let
      resPath = cvPath ct
      notifers = ctxNotifiers . cvCtx $ ct
      deps = fromMaybe [] (Map.lookup resPath notifers)
    withDebugInfo $ \path _ ->
      unless (null deps) $
        logDebugStr $
          printf "evalTM: path: %s, using value to update %s" (show path) (show deps)
    mapM_ (\dep -> inAbsRemoteTM dep (populateRef nt evalFunc)) deps

{- | Substitute the cached result of the Func node pointed by the path with the new non-function value. Then trigger the
 - re-evluation of the lowest ancestor Func.
-}
populateRef :: (TreeMonad s m) => Tree -> ((TreeMonad s m) => Func Tree -> m ()) -> m ()
populateRef nt evalFunc = do
  withDebugInfo $ \path _ ->
    logDebugStr $ printf "populateRef: path: %s, new value: %s" (show path) (show nt)
  withTree $ \tar -> case (treeNode tar, treeNode nt) of
    -- If the new value is a function, just skip the re-evaluation.
    (TNFunc _, TNFunc _) -> return ()
    (TNFunc fn, _) -> do
      unless (isFuncRef fn) $
        throwError $
          printf "populateRef: the target node %s is not a reference." (show tar)

      _ <- reduceFunc getFuncFromTree nt mkFuncTree
      withDebugInfo $ \path v ->
        logDebugStr $ printf "populateRef: path: %s, updated value: %s" (show path) (show v)
    _ -> throwError $ printf "populateRef: the target node %s is not a function." (show tar)

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
          tryPopulateRef nt evalFunc
      -- re-evaluate the highest function when it is not a reference.
      | otherwise -> do
          withDebugInfo $ \path _ ->
            logDebugStr $ printf "populateRef: re-evaluating the lowest ancestor function, path: %s, node: %s" (show path) (show t)
          r <- evalFunc fn >> getTMTree
          tryPopulateRef r evalFunc
    _ -> throwError "populateRef: the target node is not a function"

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
        "deref: start, path: %s, ref_path: %s, tip: %s"
        (show path)
        (show tp)
        (show t)
  follow tp >>= \case
    (Just tar) -> do
      withDebugInfo $ \_ t ->
        logDebugStr $
          printf
            "deref: done, path: %s, ref_path: %s, tip: %s, tar: %s"
            (show path)
            (show tp)
            (show t)
            (show tar)
      putTMTree tar
      return True
    Nothing -> return False
 where
  -- Keep dereferencing until the target node is not a reference node.
  -- returns the target node.
  follow :: (TreeMonad s m) => Path -> m (Maybe Tree)
  follow dst = do
    srcPath <- getTMAbsPath
    logDebugStr $ printf "deref: path: %s, dereferencing: %s" (show srcPath) (show dst)
    resE <- getDstVal srcPath dst
    case resE of
      Left (cycleStartPath, cycleTailRelPath) -> do
        ctx <- getTMContext
        putTMContext $ ctx{ctxCycle = Just (cycleStartPath, cycleTailRelPath)}
        return $ Just (mkNewTree $ TNRefCycle RefCycleTail)
      Right origM
        | Nothing <- origM -> return Nothing
        | (Just orig) <- origM -> do
            withDebugInfo $ \path _ -> do
              logDebugStr $ printf "deref: path: %s, substitutes with orig: %s" (show path) (show orig)
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
                follow nextDst
              _ -> Just <$> getTMTree

  -- Get the value pointed by the reference.
  -- If the reference path is self or visited, then return the tuple of the absolute path of the start of the cycle and
  -- the cycle tail relative path.
  getDstVal :: (TreeMonad s m) => Path -> Path -> m (Either (Path, Path) (Maybe Tree))
  getDstVal srcPath dst = inRemoteTMMaybe dst $ do
    dstPath <- getTMAbsPath
    visitingSet <- ctxVisiting <$> getTMContext
    let
      canSrcPath = canonicalizePath srcPath
      canDstPath = canonicalizePath dstPath
    if
      | Set.member dstPath visitingSet -> do
          delNotifRecvs dstPath
          logDebugStr $ printf "deref: reference cycle detected: %s, set: %s" (show dstPath) (show $ Set.toList visitingSet)
          return $ Left (dstPath, relPath dstPath srcPath)
      | canDstPath == canSrcPath -> do
          logDebugStr $ printf "deref: reference self cycle detected: %s == %s." (show dstPath) (show srcPath)
          return $ Left (dstPath, relPath dstPath srcPath)
      | isPrefix canDstPath canSrcPath ->
          throwError $ printf "structural cycle detected. %s is a prefix of %s" (show dstPath) (show srcPath)
      -- The value of a reference is a copy of the expression associated with the field that it is bound to, with
      -- any references within that expression bound to the respective copies of the fields they were originally
      -- bound to.
      | otherwise -> withTree $ \tar -> case treeNode tar of
          -- The atom value is final, so we can return it directly.
          TNAtom _ -> return . Right $ Just tar
          TNConstraint c -> return . Right $ Just (mkAtomVTree $ cnsAtom c)
          _ -> do
            let x = fromMaybe tar (treeOrig tar)
                -- back up the original tree.
                orig = x{treeOrig = Just x}
            logDebugStr $
              printf
                "deref: path: %s, deref'd orig is: %s, set: %s, tar: %s"
                (show dstPath)
                (show orig)
                (show $ Set.toList visitingSet)
                (show tar)
            return . Right $ Just orig

  inRemoteTMMaybe :: (TreeMonad s m) => Path -> m (Either a (Maybe b)) -> m (Either a (Maybe b))
  inRemoteTMMaybe p f = do
    origAbsPath <- getTMAbsPath
    tarM <- goLowestAncPathTM p (Just <$> getTMTree)
    res <- maybe (return (Right Nothing)) (\x -> putTMTree x >> f) tarM
    backM <- goTMAbsPath origAbsPath
    unless backM $ throwError "inRemoteTMMaybe: failed to go back to the original path"
    return res
