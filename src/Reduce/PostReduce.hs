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
  -- We can first assume that the tree value is an atom. Make sure the latest atom is created.
  let atomT = mkAtomTree $ cnsAtom c
  putTMTree atomT

  let raw = cnsValidator c
  tc <- getTMCursor
  validator <- replaceSelfRef (mkAtomTree $ cnsAtom c) (raw `setTCFocus` tc)
  debugInstantTM "validateCnstr" $
    printf "raw: %s, validator: %s" (show raw) (show validator)

  -- Run the validator in a sub context of an atom value.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  putTMTree validator
  reduce
  res <- getTMTree
  case rtrNonMut res of
    Just (IsBottom _) -> putTMTree res
    -- The result is valid.
    Just (IsAtom _) -> putTMTree atomT
    -- Incomplete case.
    Nothing -> return ()
    _ -> putTMTree $ mkBottomTree $ printf "constraint not satisfied, %s" (show res)

{- | Replace any reference in the validator of the atom constraint that references the constraint and forms a vertical
cycle with the constraint's atom.
-}
replaceSelfRef :: (ResolveMonad s r m) => Tree -> TrCur -> m Tree
replaceSelfRef atomT cnstrTC = debugSpanTreeRM "replaceSelfRef" cnstrTC $ do
  let cnstrAddr = tcCanAddr cnstrTC
  utc <- traverseTCSimple subNodes (replace cnstrAddr) cnstrTC
  return (tcFocus utc)
 where
  replace cnstrAddr tc = do
    let focus = tcFocus tc
    rfM <- case focus of
      IsRef _ rf -> return $ fieldPathFromRef rtrAtom rf
      _ -> return Nothing

    maybe
      (return focus)
      -- If the focus is a reference, we need to check if the ref references the cnstrAddr.
      ( \rf -> do
          lr <- locateRef rf tc
          debugInstantRM "replaceSelfRef" (printf "lr: %s" (show lr)) cnstrTC
          case lr of
            LRIdentNotFound err -> return err
            LRPartialFound _ _ -> return focus
            LRRefFound rtc ->
              return $
                if tcCanAddr rtc == cnstrAddr
                  then atomT
                  else focus
      )
      rfM

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