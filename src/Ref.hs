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

import Config
import Control.Monad (unless, void, when)
import Control.Monad.Reader (ask)
import Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Set as Set
import Error
import Mutate
import Path
import TMonad
import Text.Printf (printf)
import Util
import Value.Tree

-- | Notify dependents of the change of the value.
notify :: (TreeMonad s m) => ((TreeMonad s m) => m ()) -> m ()
notify reduceMutable = withDebugInfo $ \path t ->
  debugSpan (printf "notify: path: %s, new value: %s" (show path) (show t)) $ do
    tc <- getTMCursor
    notifyWithTC tc reduceMutable

notifyWithTC :: (TreeMonad s m) => TreeCursor Tree -> ((TreeMonad s m) => m ()) -> m ()
notifyWithTC (ValCursor _ []) _ = throwErrSt "already at the top"
notifyWithTC tc@(ValCursor nt cs) reduceMutable
  -- We should not use root value to notify.
  | length cs == 1 = return ()
  | otherwise = do
      notifiers <- ctxNotifiers <$> getTMContext
      let
        srcRefPath = treeRefPath $ tcPath tc
        notifs = fromMaybe [] (Map.lookup srcRefPath notifiers)
      logDebugStr $ printf "notifyWithTC: srcRefPath: %s, notifs %s" (show srcRefPath) (show notifs)
      unless (null notifs) $ notifyWithTree nt notifs reduceMutable
      let parentTCM = parentTC tc
      maybe
        (return ())
        ( \ptc -> do
            -- We must check if the parent is reducing. If the parent is reducing, we should not notify the parent.
            -- In addition, once parent is done with reducing, it will notify its dependents.
            inReducing <- parentIsReducing $ tcPath ptc
            unless inReducing $ do
              newTC <- propValUp tc
              notifyWithTC newTC reduceMutable
        )
        parentTCM
 where
  parentIsReducing parPath = do
    stack <- ctxReduceStack <$> getTMContext
    return $ length stack > 1 && stack !! 1 == parPath

notifyWithTree :: (TreeMonad s m) => Tree -> [Path] -> ((TreeMonad s m) => m ()) -> m ()
notifyWithTree nt notifs reduceMutable = do
  mapM_
    ( \dep ->
        inAbsRemoteTMMaybe dep (populateRef nt reduceMutable)
          -- Remove the notifier if the receiver is not found. The receiver might be relocated. For example,
          -- the receiver could first be reduced in a unifying function reducing arguments phase with path a/fa0.
          -- Then the receiver is relocated to a due to unifying fields.
          >>= maybe (delNotifRecvPrefix dep) return
    )
    notifs

{- | Populate the ref's mutval with the new value and trigger the re-evaluation of the lowest ancestor Mutable.

The tree focus is set to the ref mutable.
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
          (getMutVal newMut)
      _ -> void $ tryReduceMut (Just nt)

    reduceLAMut path reduceMutable

reduceLAMut :: (TreeMonad s m) => Path -> ((TreeMonad s m) => m ()) -> m ()
reduceLAMut from reduceMutable = do
  -- Locate the lowest ancestor mutable to trigger the re-evaluation of the ancestor mutable.
  -- Notice the tree focus now changes to the LA mutable.
  locateLAMutable
  path <- getTMAbsPath
  withTree $ \t -> case treeNode t of
    TNMutable fn
      | isMutableRef fn -> do
          when (from /= path) $
            throwErrSt $
              printf "the lowest ancestor mutable %s is not the same as the ref path: %s" (show path) (show from)
          -- If it is a reference, the re-evaluation can be skipped because
          -- 1. The la mutable is actually itself.
          -- 2. Re-evaluating the reference would get the same value.
          logDebugStr $
            printf
              -- "populateRef: lowest ancestor mutable is a reference, skip re-evaluation. path: %s, node: %s"
              "populateRef: lowest ancestor mutable is a reference, path: %s, node: %s, trigger notify"
              (show path)
              (show t)
          notify reduceMutable
      -- re-evaluate the highest mutable when it is not a reference.
      | otherwise -> do
          logDebugStr $
            printf "populateRef: re-evaluating the lowest ancestor mutable, path: %s, node: %s" (show path) (show t)
          reduceMutable
          notify reduceMutable
    _ -> logDebugStr "populateRef: the lowest ancestor node is not found"

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
 - detected. If the target is found, a copy of the target value is put to the tree.

@param ref: the reference path.
@param skipReduce: if true, the target value is not reduced.
-}
deref :: (TreeMonad s m) => Path -> Bool -> m ()
deref ref skipReduce = do
  path <- getTMAbsPath
  t <- getTMTree
  void $ debugSpan (printf "deref: path: %s, ref: %s, focus: %s" (show path) (show ref) (show t)) $ do
    isInfEval <- checkInfinite ref
    if isInfEval
      then do
        logDebugStr $ printf "deref: path: %s, ref: %s, ref is reducing in ancestor" (show path) (show ref)
        putTMTree $ mkBottomTree "structural cycle detected."
      else do
        rM <- follow ref (Set.fromList [treeRefPath path])
        maybe
          (addNotifier ref)
          ( \(_, tar) -> do
              putTMTree tar
              case treeNode tar of
                TNBottom _ -> return ()
                TNRefCycle (RefCycleHori (start, _))
                  | start == treeRefPath path ->
                      logDebugStr $
                        printf
                          "deref, path: %s, self-cycle: %s, skipping add notifier"
                          (show path)
                          (show tar)
                _ -> do
                  addNotifier ref

                  unless skipReduce $ do
                    logDebugStr (printf "deref, path: %s, reduce deref'd value. ref: %s, focus: %s" (show path) (show ref) (show tar))
                    Config{cfReduce = reduce} <- ask
                    reduce
          )
          rM

{- | Check if the ref is already being reduced in the ancestor nodes.

The function is supposed to be run in the mutval env.
-}
checkInfinite :: (TreeMonad s m) => Path -> m Bool
checkInfinite ref = do
  -- exclude the current mut node.
  mutCrumbs <- tail <$> getTMCrumbs
  let match = foldl (\acc (_, t) -> acc || getRef t == Just ref) False mutCrumbs
  withDebugInfo $ \path t ->
    logDebugStr $
      printf
        "checkInfinite: path: %s, ref: %s, match: %s, focus: %s"
        (show path)
        (show ref)
        (show match)
        (show t)
  return match
 where
  getRef :: Tree -> Maybe Path
  getRef t = case treeNode t of
    TNMutable (Ref rf) -> Just $ refPath rf
    _ -> Nothing

{- | Add a notifier to the context.


If the referenced value changes, then the reference should be updated. Duplicate cases are handled by the
addCtxNotifier.
This must not introduce a cycle.
-}
addNotifier :: (TreeMonad s m) => Path -> m ()
addNotifier ref = do
  srcPath <- getRefTarAbsPath ref
  recvPath <- getTMAbsPath
  let
    srcRefPath = treeRefPath srcPath
    recvRefPath = treeRefPath recvPath

  logDebugStr $ printf "addNotifier: (%s -> %s)" (show srcRefPath) (show recvRefPath)
  ctx <- getTMContext
  putTMContext $ addCtxNotifier ctx (srcRefPath, recvRefPath)

{- | Keep dereferencing until the target node is not a reference node. Returns the target node.

@param trail: keeps track of the followed treeRefPaths.
-}
follow :: (TreeMonad s m) => Path -> Set.Set Path -> m (Maybe (Path, Tree))
follow ref trail = do
  path <- getTMAbsPath
  resM <- getDstVal ref trail
  case resM of
    Nothing -> return Nothing
    Just (tarPath, tar) -> do
      logDebugStr $
        printf "deref: path: %s, substitutes with tar_path: %s, tar: %s" (show path) (show tarPath) (show tar)
      case treeNode tar of
        -- follow the reference.
        TNMutable (Ref rf) ->
          follow (refPath rf) (Set.insert (treeRefPath tarPath) trail)
        _ -> do
          -- substitute the reference with the target node.
          putTMTree tar
          return resM

{- | Get the value pointed by the reference.

If the reference path is self or visited, then return the tuple of the absolute path of the start of the cycle and
the cycle tail relative path.
-}
getDstVal :: (TreeMonad s m) => Path -> Set.Set Path -> m (Maybe (Path, Tree))
getDstVal ref trail = do
  srcPath <- getTMAbsPath

  rM <- inRemoteTMMaybe ref $ do
    dstPath <- getTMAbsPath
    logDebugStr $
      printf "deref: getDstVal ref: %s, dstPath: %s, trail: %s" (show ref) (show dstPath) (show $ Set.toList trail)
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
        | Set.member (treeRefPath dstPath) trail -> do
            logDebugStr $
              printf
                "deref: horizontal reference cycle detected: %s, dst: %s, trail: %s"
                (show ref)
                (show dstPath)
                (show $ Set.toList trail)
            return . mkNewTree $ TNRefCycle (RefCycleHori (dstPath, srcPath))
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
                logDebugStr $ printf "deref: vertical reference cycle tail detected: %s == %s." (show dstPath) (show srcPath)
                return $ mkNewTree $ TNRefCycle (RefCycleVertMerger (dstPath, srcPath))
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
        c <- copyRefVal ref trail r
        return $ Just (p, c)
    )
    rM

{- | Copy the value of the reference.

From the spec:
The value of a reference is a copy of the expression associated with the field that it is bound to, with
any references within that expression bound to the respective copies of the fields they were originally
bound to.
-}
copyRefVal :: (TreeMonad s m) => Path -> Set.Set Path -> Tree -> m Tree
copyRefVal ref trail tar = do
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
      let visitedRefs = Set.insert ref trail
      val <-
        if any pathHasDef visitedRefs
          then do
            logDebugStr $
              printf
                "deref: path: %s, visitedRefs: %s, has definition, recursively close the value."
                (show path)
                (show $ Set.toList visitedRefs)
            return . mkMutableTree . SFunc $
              emptySFunc
                { sfnArgs = [orig]
                , sfnName = "deref_close"
                , sfnMethod = close True
                }
          else return orig
      logDebugStr $
        printf
          "deref: path: %s, deref'd val is: %s, trail: %s, tar: %s"
          (show path)
          (show val)
          (show $ Set.toList trail)
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
