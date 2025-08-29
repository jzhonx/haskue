{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.PostReduce where

import Common (ctxNotifGraph)
import Control.Monad (when)
import Cursor
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (isJust)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import NotifGraph
import Path
import Reduce.Nodes (checkLabelsPerm, normalizeDisj)
import Reduce.RMonad (
  ReduceMonad,
  ResolveMonad,
  debugInstantRM,
  debugInstantTM,
  debugSpanArgsTM,
  debugSpanTM,
  debugSpanTreeRM,
  getRMContext,
  getRMUnreferredLets,
  getTMCursor,
  getTMTree,
  inSubTM,
  modifyTMNodeWithTree,
  modifyTMTN,
  putRMContext,
  putTMCursor,
  putTMTree,
  setForceReduceArgs,
  withTN,
  withTree,
 )
import Reduce.RefSys (LocateRefResult (..), locateRef)
import Reduce.Root (reduce)
import Text.Printf (printf)
import Value

postValidation :: (ReduceMonad s r m) => m ()
postValidation = debugSpanTM "postValidation" $ do
  ctx <- getRMContext
  -- remove all notifiers.
  putRMContext $ ctx{ctxNotifGraph = emptyNotifGraph}

  -- rewrite all functions to their results if the results exist.
  snapshotRM
  simplifyRM

  t <- getTMTree
  debugSpanArgsTM "validate" (show t) $ do
    -- then validate all constraints.
    traverseTM $ withTN $ \case
      TNAtomCnstr c -> validateCnstr c
      _ -> return ()

  unreferred <- getRMUnreferredLets
  withTree $ \res -> do
    when (not (null unreferred) && (case res of IsBottom _ -> False; _ -> True)) $ do
      let u = head unreferred
      label <- case lastSeg u of
        Just (BlockTASeg (LetTASeg label)) -> return label
        _ -> throwErrSt "invalid let seg"

      putTMTree $ mkBottomTree $ printf "unreferenced let clause let %s" (T.unpack $ TE.decodeUtf8 label)

{- | Traverse the tree and does the following things with the node:

1. Replace the Mutable node with the result of the mutator if it exists, otherwise the original mutator node is kept.
2. Extract the embedded value from the block.
-}
snapshotRM :: (ReduceMonad s r m) => m ()
snapshotRM = debugSpanTM "snapshotRM" $ do
  traverseTM $ withTree $ \t -> case extract t of
    Just r -> modifyTMNodeWithTree r
    Nothing -> return ()
 where
  -- It is similar to rtrDeterministic, but it skips the AtomCnstr which will be validated later.
  extract t = case treeNode t of
    TNMutable mut -> getMutVal mut >>= extract
    TNBlock blk
      | IsBlockEmbed ev <- blk -> extract ev
    _ -> return t

{- | Traverse the tree and does the following things with the node:

1. Check struct permission and empty all stub value containers of the struct, which are constraints and
embeddings. All the pending values should have been already applied to the static fields.
-}
simplifyRM :: (ReduceMonad s r m) => m ()
simplifyRM = debugSpanTM "simplifyRM" $ do
  traverseTM $ do
    withTN $ \case
      TNBlock _ -> validateStructPerm
      _ -> return ()

    withTN $ \case
      TNBlock block
        | IsBlockEmbed _ <- block -> throwErrSt "non struct value exists in block"
        | otherwise ->
            modifyTMTN $
              TNBlock $
                (modifyBlockStruct (\st -> st{stcPerms = []}) block)
                  { blkEmbeds = IntMap.empty
                  , blkCnstrs = IntMap.empty
                  }
      _ -> return ()

{- | Validate the constraint.

It creates a validate function, and then evaluates the function. Notice that the validator will be assigned to the
constraint in the propValUp.
-}
validateCnstr :: (ReduceMonad s r m) => AtomCnstr -> m ()
validateCnstr c = debugSpanTM "validateCnstr" $ do
  -- Run the validator in a forced reduce args mode.
  -- If any reference in the validator is a RC reference, it will either get the latest value of the RC node, or
  -- get an incomplete value if the RC node did not yield a concrete value.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  setForceReduceArgs True
  putTMTree (cnsValidator c)
  reduce
  setForceReduceArgs False

  res <- getTMTree
  case rtrNonMut res of
    Just (IsBottom _) -> putTMTree res
    -- The result is valid.
    Just (IsAtom _) -> putTMTree (mkAtomTree $ cnsAtom c)
    -- Incomplete case.
    Nothing -> return ()
    _ -> putTMTree $ mkBottomTree $ printf "constraint not satisfied, %s" (show res)

validateStructPerm :: (ReduceMonad s r m) => m ()
validateStructPerm = debugSpanTM "validateStructPerm" $ do
  t <- getTMTree
  case treeNode t of
    -- After snapsnot, the blkNonStructValue should be None.
    TNBlock blk@(IsBlockStruct s) -> mapM_ (validatePermItem blk) (stcPerms s)
    _ -> return ()

{- | Validate the permission item.

A struct must be provided so that dynamic fields and constraints can be found.

It constructs the allowing labels and constraints and checks if the joining labels are allowed.
-}
validatePermItem :: (ReduceMonad s r m) => Block -> PermItem -> m ()
validatePermItem blk p = debugSpanTM "validatePermItem" $ do
  let
    labelsM = mapM labelToText $ Set.toList $ piLabels p
    opLabelsM = mapM labelToText $ Set.toList $ piOpLabels p
    cnstrs = IntMap.fromList $ map (\i -> (i, blkCnstrs blk IntMap.! i)) (Set.toList $ piCnstrs p)
  case (labelsM, opLabelsM) of
    (Just labels, Just opLabels) ->
      getTMCursor
        >>= checkLabelsPerm (Set.fromList labels) cnstrs True False (Set.fromList opLabels)
        >>= putTMCursor
    -- If not all dynamic fields can be resolved to string labels, we can not check the permission.
    -- This is what CUE does.
    _ -> return ()
 where
  labelToText :: BlockLabel -> Maybe T.Text
  labelToText (BlockFieldLabel n) = Just n
  labelToText (BlockDynFieldOID i) = do
    df <- IntMap.lookup i (blkDynFields blk)
    rtrString (dsfLabel df)

{- | Traverse all the one-level sub nodes of the tree.

For the bottom handling:
1. It surfaces the bottom as field value.
-}
traverseSub :: forall s r m. (ReduceMonad r s m) => m () -> m ()
traverseSub f = withTree $ \_t -> do
  mapM_ (\(seg, _) -> inSubTM seg f) (subNodes _t)

  tc <- getTMCursor
  let t = tcFocus tc
  case treeNode t of
    -- If the any of the sub node is reduced to bottom, then the parent struct node should be reduced to bottom.
    TNBlock (IsBlockStruct struct) -> do
      let errM =
            foldl
              ( \acc field ->
                  if
                    | isJust acc -> acc
                    | IsBottom _ <- (ssfValue field) -> Just (ssfValue field)
                    | otherwise -> Nothing
              )
              Nothing
              (stcFields struct)
      maybe (return ()) putTMTree errM
    TNDisj dj -> do
      newDjT <- normalizeDisj dj tc
      modifyTMNodeWithTree newDjT
    _ -> return ()

{- | Traverse the leaves of the tree cursor in the following order

1. Traverse the current node.
2. Traverse the sub-tree with the segment.
-}
traverseTM :: (ReduceMonad r s m) => m () -> m ()
traverseTM f = f >> traverseSub (traverseTM f)