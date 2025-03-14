{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.PostReduce where

import Common (TreeOp (isTreeAtom, isTreeBottom, isTreeMutable))
import Cursor (Context (ctxCnstrValidatorAddr, ctxRefSysGraph))
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import Reduce.RMonad (
  ReduceMonad,
  getRMAbsAddr,
  getRMContext,
  getRMTree,
  inTempSubRM,
  modifyRMContext,
  putRMContext,
  putRMTree,
  traverseRM,
  withTN,
  withTree,
 )
import qualified Reduce.RefSys as RefSys
import Reduce.Root (fullReduce)
import Text.Printf (printf)
import Util (logDebugStr)
import Value.Tree (
  AtomCnstr (cnsAtom, cnsValidator),
  CnstredVal (cnsedVal),
  LetBinding (LetBinding, lbReferred),
  Struct (stcFields),
  StructVal (SLet),
  Tree,
  TreeNode (TNAtomCnstr, TNCnstredVal, TNMutable, TNStruct),
  getMutVal,
  getMutableFromTree,
  mkAtomVTree,
  mkBottomTree,
  stcLets,
 )

postValidation :: (ReduceMonad s r m) => m ()
postValidation = do
  logDebugStr "postValidation: start"

  ctx <- getRMContext
  -- remove all notifiers.
  putRMContext $ ctx{ctxRefSysGraph = Map.empty}

  -- rewrite all functions to their results if the results exist.
  snapshotRM

  withTree $ \t -> logDebugStr $ printf "postValidation: tree: %s" (show t)

  -- then validate all constraints.
  traverseRM $ withTN $ \case
    TNAtomCnstr c -> validateCnstr c
    TNStruct s -> validateStruct s
    _ -> return ()

{- | Traverse the tree and does the following things with the node:

1. replace the Mutable node with the result of the mutator if it exists, otherwise the
original mutator node is kept.
2. replace the CnstredVal node with its value.
-}
snapshotRM :: (ReduceMonad s r m) => m ()
snapshotRM =
  traverseRM $ withTN $ \case
    TNMutable m -> maybe (return ()) putRMTree (getMutVal m)
    TNCnstredVal c -> putRMTree $ cnsedVal c
    _ -> return ()

-- Validate the constraint. It creates a validate function, and then evaluates the function. Notice that the validator
-- will be assigned to the constraint in the propValUp.
validateCnstr :: (ReduceMonad s r m) => AtomCnstr Tree -> m ()
validateCnstr c = do
  addr <- getRMAbsAddr
  logDebugStr $
    printf
      "validateCnstr: addr: %s, validator: %s"
      (show addr)
      (show (cnsValidator c))
  modifyRMContext $ \ctx -> ctx{ctxCnstrValidatorAddr = Just addr}

  -- make sure return the latest atom
  let atomT = mkAtomVTree $ cnsAtom c
  -- run the validator in a sub context.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  res <- inTempSubRM (mkBottomTree "no value yet") $ do
    raw <- RefSys.evalExprRM (cnsValidator c)
    putRMTree raw
    -- TODO: replace all refs that refer to the cnstr with the atom
    fullReduce >> getRMTree

  modifyRMContext $ \ctx -> ctx{ctxCnstrValidatorAddr = Nothing}

  putRMTree $
    if
      | isTreeBottom res -> res
      | isTreeAtom res -> atomT
      -- The result might be a mutable due to an atom unifying with a mutable.
      | Just a <- getMutableFromTree res >>= getMutVal, isTreeAtom a -> atomT
      -- incomplete case
      | isTreeMutable res -> res
      | otherwise -> mkBottomTree $ printf "constraint not satisfied, %s" (show res)

-- | Validate if a struct has any unreferenced let clauses.
validateStruct :: (ReduceMonad s r m) => Struct Tree -> m ()
validateStruct s =
  let errM =
        Map.foldrWithKey
          ( \label lb acc ->
              if isNothing acc && not (lbReferred lb)
                then Just $ mkBottomTree $ printf "unreferenced let clause let %s" label
                else acc
          )
          Nothing
          (stcLets s)
   in maybe (return ()) putRMTree errM
