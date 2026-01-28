{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Finalize where

import Cursor
import Data.Maybe (catMaybes, isJust, listToMaybe)
import Feature
import Reduce.Core (reduce)
import Reduce.Disjunction (normalizeDisj)
import Reduce.Monad (
  RM,
  getTMCursor,
  getTMVal,
  inSubTM,
  postVisitValSimple,
  putTMCursor,
  putTMVal,
  withVN,
 )
import Reduce.TraceSpan (
  debugInstantRM,
  traceSpanTM,
 )
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)
import Value

{- | Finalize the reduced value.

After the value is reduced to the fixpoint, we need to do some finalization work:

1. Validate all constraints.
2. Pop up bottoms.
-}
finalize :: RM ()
finalize = traceSpanTM "finalize" $ do
  traceSpanTM "validate" $ do
    -- then validate all constraints.
    traverseTM $ withVN $ \case
      VNAtomCnstr c -> validateCnstr c
      _ -> return ()

  -- rewrite all functions to their results if the results exist.
  simplifyRM

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
      ( \x -> case fetchLabelType <$> lastSeg (vcAddr x) of
          -- We do not need to simplify mutable argument labels.
          Just MutArgLabelType -> return x
          _ -> do
            let t = focus x
            case t of
              -- Keep the genop if the value is no val.
              IsNoVal | IsValMutable _ <- t -> return x
              IsDisj d -> do
                r <-
                  normalizeDisj
                    ( \y -> case y of
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
                  (const $ return $ printf "struct subErrM: %s, embErrM: %s" (show subErrM) (show embErrM))
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
traverseTM f = do
  f
  vc <- getTMCursor
  mapM_ (\seg -> inSubTM seg (traverseTM f)) (subNodes False vc)
