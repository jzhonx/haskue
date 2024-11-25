{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Ref where

import Class
import Config
import Control.Monad (unless, void, when)
import Control.Monad.Reader (ask)
import Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isNothing)
import qualified Data.Set as Set
import Error
import Mutate
import Path
import TMonad
import Text.Printf (printf)
import Util
import Value.Tree

notify :: (TreeMonad s m) => Tree -> ((TreeMonad s m) => Mutable Tree -> m ()) -> m ()
notify nt reduceMutable = withDebugInfo $ \path _ ->
  debugSpan (printf "notify: path: %s, new value: %s" (show path) (show nt)) $ do
    withCtxTree $ \ct -> do
      let
        srcRefPath = treeRefPath $ cvPath ct
        notifers = ctxNotifiers . cvCtx $ ct
        notifs = fromMaybe [] (Map.lookup srcRefPath notifers)

      unless (null notifs) $
        logDebugStr $
          printf "notify: path: %s, srcRefPath: %s, notifs %s" (show path) (show srcRefPath) (show notifs)
      mapM_
        ( \dep ->
            inAbsRemoteTMMaybe dep (populateRef nt reduceMutable)
              -- Remove the notifier if the receiver is not found. The receiver might be relocated. For examaple,
              -- the receiver could first be reduced in a unifying function reducing arguments phase with path a/fa0.
              -- Then the receiver is relocated to a due to unifying fields.
              >>= maybe (delNotifRecvPrefix dep) return
        )
        notifs

{- | Substitute the cached result of the Mutable node pointed by the path with the new non-function value. Then trigger the
 - re-evluation of the lowest ancestor Mutable.
 - The tree focus is set to the ref func.
-}
populateRef :: (TreeMonad s m) => Tree -> ((TreeMonad s m) => Mutable Tree -> m ()) -> m ()
populateRef nt reduceMutable = withDebugInfo $ \path x ->
  debugSpan (printf "populateRef: path: %s, focus: %s, new value: %s" (show path) (show x) (show nt)) $ do
    withTree $ \tar -> case treeNode nt of
      TNMutable newMut ->
        maybe
          (return ()) -- If the new value is a pure function (mutable without any values), just skip the reduction.
          ( \res -> do
              logDebugStr $ printf "populateRef: path: %s, new res of function: %s" (show path) (show res)
              void $ tryReduceMut (Just res)
          )
          (mutValue newMut)
      _ -> case treeNode tar of
        TNMutable _ -> void $ tryReduceMut (Just nt)
        _ -> do
          logDebugStr $ printf "populateRef: the target node %s is not a reference now." (show tar)
          -- we need to delete receiver starting with the path, not only the path. For example, if the function
          -- is index and the first argument is a reference, then the first argument dependency should also be
          -- deleted.
          delNotifRecvPrefix path

    res <- getTMTree
    logDebugStr $ printf "populateRef: path: %s, mutable reduced to: %s" (show path) (show res)

    -- Locate the lowest ancestor mutable to trigger the re-evaluation of the ancestor mutable.
    locateLAMutable
    withTree $ \t -> case treeNode t of
      TNMutable fn
        | isMutableRef fn -> do
            -- If it is a reference, the re-evaluation can be skipped because
            -- 1. The la mutable is actually itself.
            -- 2. Re-evaluating the reference would get the same value.
            logDebugStr $
              printf
                "populateRef: lowest ancestor mutable is a reference, skip re-evaluation. path: %s, node: %s"
                (show path)
                (show t)
        -- re-evaluate the highest mutable when it is not a reference.
        | otherwise -> do
            logDebugStr $
              printf "populateRef: re-evaluating the lowest ancestor mutable, path: %s, node: %s" (show path) (show t)
            r <- reduceMutable fn >> getTMTree
            notify r reduceMutable
      _ ->
        if isTreeMutable res
          then throwErrSt $ printf "populateRef: the lowest ancestor node %s is not a function" (show t)
          else logDebugStr "populateRef: the lowest ancestor node is not found"

-- Locate the lowest ancestor mutable.
-- TODO: consider the mutable does not have arguments.
locateLAMutable :: (TreeMonad s m) => m ()
locateLAMutable = do
  path <- getTMAbsPath
  if hasEmptyPath path || not (hasMutableArgSel path)
    then return ()
    -- If the path has mutable argument selectors, that means we are in a mutable node.
    else propUpTM >> locateLAMutable
 where
  hasEmptyPath (Path.Path sels) = null sels
  -- Check if the path has mutable argument selectors.
  hasMutableArgSel (Path.Path sels) =
    any
      ( \case
          (MutableSelector (MutableArgSelector _)) -> True
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
      printf "deref: path: %s, start:, ref_path: %s, tip: %s" (show path) (show tp) (show t)
  r <-
    follow tp Set.empty >>= \case
      (Just (_, tar)) -> do
        withDebugInfo $ \_ t ->
          logDebugStr $
            printf "deref: path: %s, done: ref_path: %s, tip: %s, tar: %s" (show path) (show tp) (show t) (show tar)

        putTMTree tar
        return True
      Nothing -> return False

  -- add notifier. If the referenced value changes, then the reference should be updated.
  -- duplicate cases are handled by the addCtxNotifier.
  withCtxTree $ \ct -> do
    tarPath <- getRefTarAbsPath tp
    let
      tarRefPath = treeRefPath tarPath
      recvRefPath = treeRefPath $ cvPath ct

    logDebugStr $ printf "deref: add notifier: (%s, %s)" (show tarRefPath) (show recvRefPath)
    putTMContext $ addCtxNotifier (cvCtx ct) (tarRefPath, recvRefPath)
  return r
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
          logDebugStr $
            printf
              "deref: path: %s, substitutes with orig_path: %s, orig: %s"
              (show path)
              (show origPath)
              (show orig)
        -- substitute the reference with the target node.
        putTMTree orig
        case treeNode orig of
          -- follow the reference.
          TNMutable fn | isMutableRef fn -> do
            nextDst <-
              maybe
                (throwErrSt "can not generate path from the arguments")
                return
                (treesToPath (mutArgs fn))
            follow nextDst (Set.insert ref refsSeen)
          _ -> return resM

  -- Get the value pointed by the reference.
  -- If the reference path is self or visited, then return the tuple of the absolute path of the start of the cycle and
  -- the cycle tail relative path.
  getDstVal :: (TreeMonad s m) => Path -> Set.Set Path -> m (Maybe (Path, Tree))
  getDstVal ref refsSeen = do
    srcPath <- getTMAbsPath
    rM <- inRemoteTMMaybe ref $ do
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
          -- The values of d would be: 1. a -> b, 2. b -> a, 3. a (seen) -> RC.
          -- The returned RC would be a self-reference cycle, which has empty path because the cycle is formed by all
          -- references.
          | Set.member ref refsSeen -> do
              logDebugStr $
                printf "deref: self reference cycle detected: %s, seen: %s" (show ref) (show $ Set.toList refsSeen)
              return $ Just . mkNewTree $ TNRefCycle (RefCycle True)
          -- This handles the case when the reference refers to itself that is the ancestor.
          -- For example, { a: a + 1 } or { a: !a }.
          -- The tree representation of the latter is,
          -- { }
          --  | - a
          -- (!)
          --  | - unary_op
          -- ref_a
          | canDstPath == canSrcPath && treeRefPath srcPath /= treeRefPath dstPath -> withTree $ \tar -> case treeNode tar of
              -- In the validation phase, the subnode of the Constraint node might find the parent Constraint node.
              TNConstraint c -> return $ Just (mkAtomVTree $ cnsOrigAtom c)
              _ -> do
                logDebugStr $ printf "deref: reference cycle tail detected: %s == %s." (show dstPath) (show srcPath)
                return $ Just . mkNewTree $ TNRefCycle (RefCycleTail (dstPath, relPath dstPath srcPath))
          | isPrefix canDstPath canSrcPath && canSrcPath /= canDstPath ->
              return . Just $
                mkBottomTree $
                  printf "structural cycle detected. %s is a prefix of %s" (show dstPath) (show srcPath)
          -- The value of a reference is a copy of the expression associated with the field that it is bound to, with
          -- any references within that expression bound to the respective copies of the fields they were originally
          -- bound to.
          | otherwise -> withTree $ \tar -> case treeNode tar of
              -- The atom value is final, so we can just return it.
              TNAtom _ -> return $ Just tar
              TNConstraint c -> return $ Just (mkAtomVTree $ cnsAtom c)
              _ -> do
                orig <-
                  maybe
                    (return tar)
                    ( \e -> do
                        Config{cfEvalExpr = evalExpr} <- ask
                        evalExpr e
                    )
                    (treeOrig tar)
                Config{cfClose = close} <- ask
                let visitedRefs = Set.insert ref refsSeen
                val <-
                  if any pathHasDef visitedRefs
                    then do
                      logDebugStr $
                        printf
                          "deref: path: %s, visitedRefs: %s, has definition, recursively close the value."
                          (show dstPath)
                          (show $ Set.toList visitedRefs)
                      return $
                        mkMutableTree $
                          (mkStubMutable $ close True)
                            { mutName = "deref_close"
                            , mutArgs = [orig]
                            }
                    else return orig
                logDebugStr $
                  printf
                    "deref: path: %s, deref'd val is: %s, set: %s, tar: %s"
                    (show dstPath)
                    (show val)
                    (show $ Set.toList refsSeen)
                    (show tar)
                return $ Just val
      return $ (dstPath,) <$> val
    when (isNothing rM) $
      logDebugStr $
        printf "deref: getDstVal ref: %s, nothing found" (show ref)
    return rM

  pathHasDef :: Path -> Bool
  pathHasDef p =
    any
      ( \case
          StructSelector (StringSelector s) -> fromMaybe False $ do
            typ <- getFieldType s
            return $ typ == SFTDefinition
          _ -> False
      )
      $ pathToList p

  inRemoteTMMaybe :: (TreeMonad s m) => Path -> m (Maybe a) -> m (Maybe a)
  inRemoteTMMaybe p f = do
    origAbsPath <- getTMAbsPath
    tarM <- goLowestAncPathTM p (Just <$> getTMTree)
    res <- maybe (return Nothing) (\x -> putTMTree x >> f) tarM
    backM <- goTMAbsPath origAbsPath
    unless backM $ throwErrSt $ printf "failed to go back to the original path %s" (show origAbsPath)
    return res

{- | Get the reference target absolute path. The target might not exist at the time, but the path should be valid as the
first selector is a locatable var.
-}
getRefTarAbsPath :: (TreeMonad s m) => Path -> m Path
getRefTarAbsPath ref = do
  let fstSel = fromJust $ headSel ref
  tc <- getTMCursor
  varTC <-
    maybeM
      (throwErrSt $ printf "reference %s is not found" (show fstSel))
      return
      (searchTCVar fstSel tc)
  let fstSelAbsPath = tcPath varTC
  return $ maybe fstSelAbsPath (`appendPath` fstSelAbsPath) (tailPath ref)
