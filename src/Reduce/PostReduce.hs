{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.PostReduce where

import Control.Monad (unless)
import Cursor
import Data.Maybe (catMaybes, fromJust, isJust, listToMaybe)
import Feature
import NotifGraph
import Reduce.Nodes (normalizeDisj)
import Reduce.RMonad (
  RM,
  ctxNotifGraph,
  debugInstantRM,
  descendTMSeg,
  getRMContext,
  getTMCursor,
  getTMTree,
  inSubTM,
  modifyTMNodeWithTree,
  postVisitTreeSimple,
  propUpTM,
  putRMContext,
  putTMCursor,
  putTMTree,
  throwFatal,
  traceSpanArgsTM,
  traceSpanTM,
  withTN,
 )
import Reduce.Root (reduce)
import Text.Printf (printf)
import Value

postValidation :: RM ()
postValidation = traceSpanTM "postValidation" $ do
  ctx <- getRMContext
  -- remove all notifiers.
  putRMContext $ ctx{ctxNotifGraph = emptyNotifGraph}

  -- rewrite all functions to their results if the results exist.
  simplifyRM

  t <- getTMTree
  traceSpanArgsTM "validate" (show t) $ do
    -- then validate all constraints.
    traverseTM $ withTN $ \case
      TNAtomCnstr c -> validateCnstr c
      _ -> return ()

{- | Traverse the tree and does the following things with the node:

1. Replace the Mutable node with the result of the mutator if it exists, otherwise the original mutator node is kept.
2. Extract the embedded value from the block.
-}
simplifyRM :: RM ()
simplifyRM = traceSpanTM "simplifyRM" $ do
  tc <- getTMCursor
  putTMCursor
    =<< postVisitTreeSimple
      (subNodes False)
      ( \x -> case addrIsRfbAddr (tcAddr x) of
          -- We only need to care about the referable node.
          Nothing -> return x
          Just _ -> do
            let t = tcFocus x
            case t of
              -- Keep the genop if the value is no val.
              IsNoVal | IsTGenOp _ <- t -> return x
              -- Overwrite the mutable node with an immutable top.
              IsRefCycle -> return $ mkNewTree TNTop `setTCFocus` x
              IsDisj d -> do
                r <-
                  normalizeDisj
                    ( \y -> case y of
                        IsSCycle -> True
                        IsNoVal -> True
                        _ -> isJust (rtrBottom y)
                    )
                    d
                    x
                return $ setTCFocusTN (treeNode r) x
              IsStruct struct -> do
                let subErrM =
                      foldl
                        ( \acc field ->
                            if
                              | isJust acc -> acc
                              | IsBottom _ <- (ssfValue field) -> Just (ssfValue field)
                              | otherwise -> Nothing
                        )
                        Nothing
                        (stcFields struct)
                    embErrM = mkNewTree . TNBottom <$> rtrBottom t
                debugInstantRM
                  "simplifyRM"
                  (printf "struct subErrM: %s, embErrM: %s" (show subErrM) (show embErrM))
                  x
                maybe
                  (return $ makeTreeImmutable t `setTCFocus` x)
                  (\err -> return $ err `setTCFocus` x)
                  (listToMaybe $ catMaybes [subErrM, embErrM])
              -- Make the tree immutable.
              _ -> return $ makeTreeImmutable t `setTCFocus` x
      )
      tc

{- | Validate the constraint.

It creates a validate function, and then evaluates the function. Notice that the validator will be assigned to the
constraint in the propValUp.
-}
validateCnstr :: AtomCnstr -> RM ()
validateCnstr c = traceSpanTM "validateCnstr" $ do
  -- Run the validator in a forced reduce args mode.
  -- If any reference in the validator is a RC reference, it will either get the latest value of the RC node, or
  -- get an incomplete value if the RC node did not yield a concrete value.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  -- setForceReduceArgs True
  putTMTree (cnsValidator c)
  reduce

  res <- getTMTree
  case rtrNonMut res of
    Just (IsBottom _) -> putTMTree res
    -- The result is valid.
    Just (IsAtom _) -> putTMTree (mkAtomTree c.value)
    -- Incomplete case.
    Nothing -> return ()
    _ -> putTMTree $ mkBottomTree $ printf "constraint not satisfied, %s" (show res)

{- | Traverse the leaves of the tree cursor in the following order

1. Traverse the current node.
2. Traverse the sub-tree with the segment.
-}
traverseTM :: RM () -> RM ()
traverseTM f = f >> traverseSub (traverseTM f)

{- | Traverse all the one-level sub nodes of the tree.

For the bottom handling:
1. It surfaces the bottom as field value.
2. Normalize the disjunction if any of the sub node becomes bottom.
-}
traverseSub :: RM () -> RM ()
traverseSub f = do
  do
    tc <- getTMCursor
    mapM_
      ( \case
          SubNodeSegNormal seg -> inSubTM seg f
          SubNodeSegEmbed seg -> do
            x <- getTMCursor
            let origSeg = fromJust $ tcFocusSeg x
            propUpTM
            inSubTM seg f
            ok <- descendTMSeg origSeg
            unless ok $ throwFatal "original segment not found after embedding traversal"
      )
      (subNodes False tc)

  tc <- getTMCursor
  let t = tcFocus tc
  case treeNode t of
    -- If the any of the sub node is reduced to bottom, then the parent struct node should be reduced to bottom.
    TNStruct struct -> do
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
      newDjT <-
        normalizeDisj
          ( \x -> case x of
              IsSCycle -> True
              IsNoVal -> True
              _ -> isJust (rtrBottom x)
          )
          dj
          tc
      modifyTMNodeWithTree newDjT
    _ -> return ()
