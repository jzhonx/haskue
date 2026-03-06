{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Finalize where

import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isJust, listToMaybe)
import Feature
import Reduce.Core (reduce)
import Reduce.Disjunction (normalizeDisj)
import Reduce.Monad (RM)
import Reduce.TraceSpan (traceSpanValTM)
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)
import Value
import Value.Instances (vtmapVectorM)

{- | Finalize the reduced value.

After the value is reduced to the fixpoint, we need to do some finalization work:

1. Validate all constraints.
2. Pop up bottoms.
-}
finalize :: ValAddr -> Val -> RM Val
finalize addr root = traceSpanValTM "finalize" addr root $ finalizeInner addr root

-- | Finalize the value by traversing the val tree in a post-order way.
finalizeInner :: ValAddr -> Val -> RM Val
finalizeInner addr topV = traceSpanValTM "finalizeInner" addr topV $ do
  v' <- case topV of
    -- If the value is mutable, we do not simplify the ops.
    IsValMutable _ -> do
      vn <- vtmapM finalizeInner addr (valNode topV)
      return (setVN vn topV)
    IsStruct s -> do
      stcFields' <-
        Map.traverseWithKey (\k v -> vtmapM finalizeInner (appendSeg addr $ mkStringFeature k) v) (stcFields s)
      let s' = s{stcFields = stcFields'}
      return $ setVN (VNStruct s') topV
    IsList l -> do
      final' <- vtmapVectorM f mkListIdxFeature addr (final l)
      let l' = l{final = final'}
      return $ setVN (VNList l') topV
    _ -> vtmapM finalizeInner addr topV
  f addr v'
 where
  f p x = traceSpanValTM "finalize_node" p x $ do
    case x of
      IsAtomCnstr c -> validateCnstr c p x
      -- Keep the mutable if the value is no val.
      IsNoVal | IsValMutable _ <- x -> return x
      IsDisj d -> do
        r <- normalizeDisj d p
        return $ setVN (valNode r) x
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
            embErrM = mkNewVal . VNBottom <$> rtrBottom x
        maybe
          (return $ setValImmutable x)
          return
          (listToMaybe $ catMaybes [subErrM, embErrM])
      -- Make the tree immutable.
      _ -> return $ setValImmutable x

{- | Validate the constraint.

It creates a validate function, and then evaluates the function. Notice that the validator will be assigned to the
constraint in the propValUp.
-}
validateCnstr :: AtomCnstr -> ValAddr -> Val -> RM Val
validateCnstr c addr v = traceSpanValTM "validateCnstr" addr v $ do
  -- Run the validator in a forced reduce args mode.
  -- If any reference in the validator is a RC reference, it will either get the latest value of the RC node, or
  -- get an incomplete value if the RC node did not yield a concrete value.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  res <- reduce addr (cnsValidator c)
  if
    | IsNoVal <- res -> return v
    | Just _ <- rtrBottom res -> return res
    | Just a <- rtrAtom res -> return $ mkAtomVal a
    | IsEmbedVal ev <- res, Just a <- rtrAtom ev -> return $ mkAtomVal a
    | otherwise -> do
        resStr <- tshow res
        return $ mkBottomVal $ printf "constraint not satisfied, %s" resStr
