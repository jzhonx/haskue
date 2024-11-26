{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Ref (
  notify,
  deref,
)
where

import Class
import Config
import Control.Monad (unless, void)
import Control.Monad.Reader (ask)
import Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust)
import qualified Data.Set as Set
import Error
import Mutate
import Path
import TMonad
import Text.Printf (printf)
import Util
import Value.Tree

notify :: (TreeMonad s m) => Tree -> ((TreeMonad s m) => m ()) -> m ()
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
populateRef :: (TreeMonad s m) => Tree -> ((TreeMonad s m) => m ()) -> m ()
populateRef nt reduceMutable = withDebugInfo $ \path x ->
  debugSpan (printf "populateRef: path: %s, focus: %s, new value: %s" (show path) (show x) (show nt)) $ do
    mustMutable $ \_ -> case treeNode nt of
      TNMutable newMut ->
        maybe
          (return ()) -- If the new value is a pure function (mutable without any values), just skip the reduction.
          ( \res -> do
              logDebugStr $ printf "populateRef: path: %s, new res of function: %s" (show path) (show res)
              void $ tryReduceMut (Just res)
          )
          (mutValue newMut)
      _ -> void $ tryReduceMut (Just nt)

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
            r <- reduceMutable >> getTMTree
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

{- | Dereference the reference. It keeps dereferencing until the target node is not a reference node or a cycle is
 - detected.

If the target is not found, the current node is kept.
No more evaluation is done after the dereference.
-}
deref :: (TreeMonad s m) => Path -> m Bool
deref ref = do
  path <- getTMAbsPath
  t <- getTMTree
  rM <- debugSpan (printf "deref: path: %s, ref: %s, focus: %s" (show path) (show ref) (show t)) $ do
    -- refInAnc <- pathInAncestorRefs ref
    -- if refInAnc
    --   then do
    --     logDebugStr $ printf "deref: path: %s, ref: %s, ref is reducing in ancestor" (show path) (show ref)
    --     return . Just $ mkBottomTree "structural cycle caused by infinite evaluation detected"
    --   else do
    rM <- do
      follow ref Set.empty >>= \case
        (Just (_, tar)) -> do
          putTMTree tar
          return (Just tar)
        Nothing -> return Nothing

    -- add notifier. If the referenced value changes, then the reference should be updated.
    -- duplicate cases are handled by the addCtxNotifier.
    tarPath <- getRefTarAbsPath ref
    recvPath <- getTMAbsPath
    addNotifier tarPath recvPath
    return rM

  return $ isJust rM

addNotifier :: (TreeMonad s m) => Path -> Path -> m ()
addNotifier srcPath recvPath = do
  let
    srcRefPath = treeRefPath srcPath
    recvRefPath = treeRefPath recvPath

  logDebugStr $ printf "addNotifier: (%s -> %s)" (show srcRefPath) (show recvRefPath)
  ctx <- getTMContext
  putTMContext $ addCtxNotifier ctx (srcRefPath, recvRefPath)

{- | Keep dereferencing until the target node is not a reference node. Returns the target node.

The refsSeen keeps track of the followed references to detect cycles.
-}
follow :: (TreeMonad s m) => Path -> Set.Set Path -> m (Maybe (Path, Tree))
follow ref refsSeen = do
  resM <- getDstVal ref refsSeen
  case resM of
    Nothing -> return Nothing
    Just (tarPath, tar) -> do
      withDebugInfo $ \path _ -> do
        logDebugStr $
          printf
            "deref: path: %s, substitutes with tar_path: %s, tar: %s"
            (show path)
            (show tarPath)
            (show tar)
      case treeNode tar of
        -- follow the reference.
        TNMutable fn | isMutableRef fn -> do
          nextDst <-
            maybe
              (throwErrSt "can not generate path from the arguments")
              return
              (treesToPath (mutArgs fn))
          follow nextDst (Set.insert ref refsSeen)
        _ -> do
          -- substitute the reference with the target node.
          putTMTree tar
          return resM

{- | Get the value pointed by the reference.

If the reference path is self or visited, then return the tuple of the absolute path of the start of the cycle and
the cycle tail relative path.
-}
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
            return $ mkNewTree $ TNRefCycle (RefCycle True)
        -- This handles the case when the reference refers to itself that is the ancestor.
        -- For example, { a: a + 1 } or { a: !a }.
        -- The tree representation of the latter is,
        -- { }
        --  | - a
        -- (!)
        --  | - unary_op
        -- ref_a
        -- Notice that for self-cycle, the srcPath could be /path/fv, and the dstPath could be /path. They are the
        -- same in the treeRefPath form.
        | canDstPath == canSrcPath && treeRefPath srcPath /= treeRefPath dstPath -> withTree $ \tar ->
            case treeNode tar of
              -- In the validation phase, the subnode of the Constraint node might find the parent Constraint node.
              TNConstraint c -> return (mkAtomVTree $ cnsOrigAtom c)
              _ -> do
                logDebugStr $ printf "deref: reference cycle tail detected: %s == %s." (show dstPath) (show srcPath)
                return $ mkNewTree $ TNRefCycle (RefCycleTail (dstPath, relPath dstPath srcPath))
        | isPrefix canDstPath canSrcPath && canSrcPath /= canDstPath ->
            return $
              mkBottomTree $
                printf "structural cycle detected. %s is a prefix of %s" (show dstPath) (show srcPath)
        | otherwise -> getTMTree
    return $ Just (dstPath, val)

  maybe
    ( do
        logDebugStr $ printf "deref: getDstVal ref: %s, nothing found" (show ref)
        return Nothing
    )
    ( \(p, r) -> do
        c <- copyRefVal ref refsSeen r
        return $ Just (p, c)
    )
    rM

{- | Check if the ref is already being reduced in the ancestor nodes.

The function is supposed to be run in the mutval env.
-}
pathInAncestorRefs :: (TreeMonad s m) => Path -> m Bool
pathInAncestorRefs ref = do
  -- exclude the mut node.
  mutCrumbs <- tail <$> getTMCrumbs
  let match = foldl (\acc (_, t) -> acc || getRef t == Just ref) False mutCrumbs
  withDebugInfo $ \path _ ->
    logDebugStr $ printf "pathInAncestorRefs: path: %s, ref: %s, match: %s" (show path) (show ref) (show match)
  return match
 where
  getRef :: Tree -> Maybe Path
  getRef t = case treeNode t of
    TNMutable mut | isMutableRef mut -> treesToPath (mutArgs mut)
    _ -> Nothing

{- | Copy the value of the reference.

From the spec:
The value of a reference is a copy of the expression associated with the field that it is bound to, with
any references within that expression bound to the respective copies of the fields they were originally
bound to.
-}
copyRefVal :: (TreeMonad s m) => Path -> Set.Set Path -> Tree -> m Tree
copyRefVal ref refsSeen tar = do
  path <- getTMAbsPath
  case treeNode tar of
    -- The atom value is final, so we can just return it.
    TNAtom _ -> return tar
    TNConstraint c -> return (mkAtomVTree $ cnsAtom c)
    _ -> do
      -- evaluate the original expression.
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
                (show path)
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
          (show path)
          (show val)
          (show $ Set.toList refsSeen)
          (show tar)
      return val

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

inRemoteTMMaybe :: (TreeMonad s m) => Path -> m (Maybe a) -> m (Maybe a)
inRemoteTMMaybe p f = do
  origAbsPath <- getTMAbsPath
  tarM <- goLowestAncPathTM p (Just <$> getTMTree)
  res <- maybe (return Nothing) (\x -> putTMTree x >> f) tarM
  backM <- goTMAbsPath origAbsPath
  unless backM $ throwErrSt $ printf "failed to go back to the original path %s" (show origAbsPath)
  return res

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
