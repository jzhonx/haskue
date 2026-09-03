{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Finalize where

import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isJust, listToMaybe)
import EvalAddr
import Reduce.Core (reduce)
import Reduce.Disjunction (normalizeDisj)
import Reduce.Monad (RM)
import Reduce.TraceSpan (traceSpanTermTreeTM)
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)
import Value
import Value.Instances (mapMVectorWAddr)

{- | Finalize the reduced value.

After the value is reduced to the fixpoint, we need to do some finalization work:

1. Validate all constraints.
2. Pop up bottoms.
-}
finalize :: EvalAddr -> VNode -> RM VNode
finalize addr root = traceSpanTermTreeTM "finalize" addr root $ finalizeInner addr root

-- | Finalize the value by traversing the val tree in a post-order way.
finalizeInner :: EvalAddr -> VNode -> RM VNode
finalizeInner addr topV = traceSpanTermTreeTM "finalizeInner" addr topV $ do
  -- First traverse the sub values.
  -- We do not traverse the constraints.
  v' <- case topV of
    IsStruct s -> do
      -- we only need to finalize the fields of the struct.
      stcFields' <-
        Map.traverseWithKey
          (\k v -> vtmapM (applyAddrFOnVN finalizeInner) (appendFeature addr $ mkStringFeature k) v)
          (stcFields s)
      let s' = s{stcFields = stcFields'}
      return $ setVNodeValue (VStruct s') topV
    IsList l -> do
      -- We only need to finalize the final part of the list.
      final' <-
        mapMVectorWAddr
          (\p v -> value <$> finalizeInner p (mkValVN v))
          (featureToAddrSegment . mkListIdxFeature)
          addr
          (final l)
      let l' = l{final = final'}
      return $ setVNodeValue (VList l') topV
    IsDisj d -> do
      d' <- vtmapM (applyAddrFOnVN finalizeInner) addr d
      return $ setVNodeValue (VDisj d') topV
    _ -> return topV
  simplify addr v'
 where
  simplify p x = traceSpanTermTreeTM "simplify" p x $ do
    case x of
      IsAtom _ | not x.constraints.allResolved -> validateCnstr p x
      -- Keep the constraints if the value is no val.
      IsUnknown -> return x
      IsDisj d -> do
        r <- normalizeDisj p d
        return $ setVNodeValue r x
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
            embErrM = mkValVN . VBottom <$> rtrBottom (value x)
        maybe
          (return x)
          return
          (listToMaybe $ catMaybes [subErrM, embErrM])
      _ -> return x

{- | Validate the constraint.

It creates a validate function, and then evaluates the function. Notice that the validator will be assigned to the
constraint in the propValUp.
-}
validateCnstr :: EvalAddr -> VNode -> RM VNode
validateCnstr addr v = traceSpanTermTreeTM "validateCnstr" addr v $ do
  -- Run the validator in a forced reduce args mode.
  -- If any reference in the validator is a RC reference, it will either get the latest value of the RC node, or
  -- get an incomplete value if the RC node did not yield a concrete value.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  res <- reduce addr v
  let rv = if res.constraints.allResolved then res else res{value = VUnknown}
  if
    | IsUnknown <- rv -> return rv
    | Just _ <- rtrBottom (value rv) -> return rv
    | Just a <- rtrAtom (value rv) -> return $ mkAtomVN a
    | IsEmbedVal ev <- (value rv), Just a <- rtrAtom ev -> return $ mkAtomVN a
    | otherwise -> do
        rvnStr <- tshow rv
        return $ mkBottomVN $ printf "constraint is not satisfied: %s" rvnStr
