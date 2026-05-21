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
import Reduce.TraceSpan (traceSpanTermsRepTM)
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)
import Value
import Value.Instances (mapMVectorWAddr)

{- | Finalize the reduced value.

After the value is reduced to the fixpoint, we need to do some finalization work:

1. Validate all constraints.
2. Pop up bottoms.
-}
finalize :: ValAddr -> VNode -> RM VNode
finalize addr root = traceSpanTermsRepTM "finalize" addr root $ finalizeInner addr root

-- | Finalize the value by traversing the val tree in a post-order way.
finalizeInner :: ValAddr -> VNode -> RM VNode
finalizeInner addr topV = traceSpanTermsRepTM "finalizeInner" addr topV $ do
  -- First traverse the sub values.
  -- We do not traverse the constraints.
  v' <- case topV of
    IsStruct s -> do
      -- we only need to finalize the fields of the struct.
      stcFields' <-
        Map.traverseWithKey
          (\k v -> vtmapM (applyAddrFOnVN finalizeInner) (appendSeg addr $ mkStringFeature k) v)
          (stcFields s)
      let s' = s{stcFields = stcFields'}
      return $ setVNodeValue (VStruct s') topV
    IsList l -> do
      -- We only need to finalize the final part of the list.
      final' <- mapMVectorWAddr finalizeInner mkListIdxFeature addr (final l)
      let l' = l{final = final'}
      return $ setVNodeValue (VList l') topV
    IsDisj _ -> do
      vtmapM
        ( \p vt -> case vt of
            VTVNode v -> VTVNode <$> finalizeInner p v
            -- If the vtnode is not a value, we traverse its children and apply the function on the children.
            _ -> vtmapM (applyAddrFOnVN finalizeInner) p vt
        )
        addr
        topV
    _ -> return topV
  simplify addr v'
 where
  simplify p x = traceSpanTermsRepTM "simplify" p x $ do
    case x of
      IsAtom _ | not x.constraints.allResolved -> validateCnstr p x
      -- Keep the constraints if the value is no val.
      IsNoVal -> return x
      IsDisj d -> do
        r <- normalizeDisj d p
        return $ setVNodeValue r (removeConstraints x)
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
          (return $ removeConstraints x)
          return
          (listToMaybe $ catMaybes [subErrM, embErrM])
      _ -> return $ removeConstraints x

{- | Validate the constraint.

It creates a validate function, and then evaluates the function. Notice that the validator will be assigned to the
constraint in the propValUp.
-}
validateCnstr :: ValAddr -> VNode -> RM VNode
validateCnstr addr v = traceSpanTermsRepTM "validateCnstr" addr v $ do
  -- Run the validator in a forced reduce args mode.
  -- If any reference in the validator is a RC reference, it will either get the latest value of the RC node, or
  -- get an incomplete value if the RC node did not yield a concrete value.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  res <- reduce addr v
  let rv = if res.constraints.allResolved then res else res{value = VNoVal}
  if
    | IsNoVal <- rv -> return rv
    | Just _ <- rtrBottom (value rv) -> return rv
    | Just a <- rtrAtom (value rv) -> return $ mkAtomVN a
    | IsEmbedVal ev <- (value rv), Just a <- rtrAtom ev -> return $ mkAtomVN a
    | otherwise -> do
        rvnStr <- tshow rv
        return $ mkBottomVal $ printf "constraint not satisfied, %s" rvnStr
