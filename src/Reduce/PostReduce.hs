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
import DepGraph
import Feature
import Reduce.Core (reduce)
import Reduce.Disjunction (normalizeDisj)
import Reduce.Monad (
  RM,
  depGraph,
  descendTMSeg,
  getRMContext,
  getTMCursor,
  getTMVal,
  inSubTM,
  modifyTMNodeWithVal,
  postVisitValSimple,
  propUpTM,
  putRMContext,
  putTMCursor,
  putTMVal,
  throwFatal,
  withVN,
 )
import Reduce.TraceSpan (
  debugInstantRM,
  traceSpanArgsTM,
  traceSpanTM,
 )
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)
import Value

postValidation :: RM ()
postValidation = traceSpanTM "postValidation" $ do
  ctx <- getRMContext
  -- remove all notifiers.
  putRMContext $ ctx{depGraph = emptyPropGraph}

  -- rewrite all functions to their results if the results exist.
  simplifyRM

  t <- getTMVal
  traceSpanArgsTM "validate" (show t) $ do
    -- then validate all constraints.
    traverseTM $ withVN $ \case
      VNAtomCnstr c -> validateCnstr c
      _ -> return ()

{- | Traverse the tree and does the following things with the node:

1. Replace the SOp node with the result of the mutator if it exists, otherwise the original mutator node is kept.
2. Extract the embedded value from the block.
-}
simplifyRM :: RM ()
simplifyRM = traceSpanTM "simplifyRM" $ do
  vc <- getTMCursor
  putTMCursor
    =<< postVisitValSimple
      (subNodes False)
      ( \x -> case addrIsRfbAddr (vcAddr x) of
          -- We only need to care about the referable node.
          Nothing -> return x
          Just _ -> do
            let t = focus x
            case t of
              -- Keep the genop if the value is no val.
              IsNoVal | IsValMutable _ <- t -> return x
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
                return $ setVCFocusVN (valNode r) x
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
                    embErrM = mkNewVal . VNBottom <$> rtrBottom t
                debugInstantRM
                  "simplifyRM"
                  (printf "struct subErrM: %s, embErrM: %s" (show subErrM) (show embErrM))
                  x
                maybe
                  (return $ setValImmutable t `setVCFocus` x)
                  (\err -> return $ err `setVCFocus` x)
                  (listToMaybe $ catMaybes [subErrM, embErrM])
              -- Make the tree immutable.
              _ -> return $ setValImmutable t `setVCFocus` x
      )
      vc

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
  putTMVal (cnsValidator c)
  reduce

  res <- getTMVal
  if
    | IsNoVal <- res -> return ()
    | Just _ <- rtrBottom res -> putTMVal res
    | Just a <- rtrAtom res -> putTMVal $ mkAtomVal a
    | IsEmbedVal ev <- res, Just a <- rtrAtom ev -> putTMVal $ mkAtomVal a
    | otherwise -> do
        resStr <- tshow res
        putTMVal $ mkBottomVal $ printf "constraint not satisfied, %s" resStr

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
    vc <- getTMCursor
    mapM_
      ( \case
          SubNodeSegNormal seg -> inSubTM seg f
          SubNodeSegEmbed seg -> do
            x <- getTMCursor
            let origSeg = fromJust $ vcFocusSeg x
            propUpTM
            inSubTM seg f
            ok <- descendTMSeg origSeg
            unless ok $ throwFatal "original segment not found after embedding traversal"
      )
      (subNodes False vc)

  vc <- getTMCursor
  let t = focus vc
  case valNode t of
    -- If the any of the sub node is reduced to bottom, then the parent struct node should be reduced to bottom.
    VNStruct struct -> do
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
      maybe (return ()) putTMVal errM
    VNDisj dj -> do
      newDjT <-
        normalizeDisj
          ( \x -> case x of
              IsSCycle -> True
              IsNoVal -> True
              _ -> isJust (rtrBottom x)
          )
          dj
          vc
      modifyTMNodeWithVal newDjT
    _ -> return ()
