{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.PostReduce where

import Common (TreeOp (isTreeAtom, isTreeBottom, isTreeMutable))
import Cursor (Context (ctxCnstrValidatorAddr, ctxRefSysGraph))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import Reduce.Root (fullReduce)
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

postValidation :: (RM.ReduceMonad s r m) => m ()
postValidation = RM.debugSpanRM "postValidation" $ do
  ctx <- RM.getRMContext
  -- remove all notifiers.
  RM.putRMContext $ ctx{ctxRefSysGraph = Map.empty}

  -- rewrite all functions to their results if the results exist.
  snapshotRM

  t <- RM.getRMTree
  RM.debugSpanArgsRM "validate" (VT.treeFullStr 0 t) $ do
    -- then validate all constraints.
    RM.traverseRM $ RM.withTN $ \case
      VT.TNAtomCnstr c -> validateCnstr c
      VT.TNStruct s -> validateStruct s
      _ -> return ()

{- | Traverse the tree and does the following things with the node:

1. Replace the Mutable node with the result of the mutator if it exists, otherwise the
original mutator node is kept.
2. Replace the CnstredVal node with its value.
3. Empty all stub value containers of the struct, which are lets, constraints, dynamic fields and embeddings. All the
pending values should have been already applied to the static fields.
-}
snapshotRM :: (RM.ReduceMonad s r m) => m ()
snapshotRM = RM.debugSpanRM "snapshotRM" $ do
  RM.traverseRM $ RM.withTN $ \case
    VT.TNMutable m -> maybe (return ()) RM.putRMTree (VT.getMutVal m)
    VT.TNCnstredVal c -> RM.putRMTree $ VT.cnsedVal c
    VT.TNStruct s ->
      RM.modifyRMTN $
        VT.TNStruct $
          s
            { VT.stcLets = Map.empty
            , VT.stcCnstrs = IntMap.empty
            , VT.stcEmbeds = IntMap.empty
            , VT.stcDynFields = IntMap.empty
            , VT.stcPerms = []
            }
    _ -> return ()

-- Validate the constraint. It creates a validate function, and then evaluates the function. Notice that the validator
-- will be assigned to the constraint in the propValUp.
validateCnstr :: (RM.ReduceMonad s r m) => VT.AtomCnstr VT.Tree -> m ()
validateCnstr c = do
  addr <- RM.getRMAbsAddr
  logDebugStr $
    printf
      "validateCnstr: addr: %s, validator: %s"
      (show addr)
      (show (VT.cnsValidator c))
  RM.modifyRMContext $ \ctx -> ctx{ctxCnstrValidatorAddr = Just addr}

  -- make sure return the latest atom
  let atomT = VT.mkAtomVTree $ VT.cnsAtom c
  -- run the validator in a sub context.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  res <- RM.inTempSubRM (VT.mkBottomTree "no value yet") $ do
    raw <- RefSys.evalExprRM (VT.cnsValidator c)
    RM.putRMTree raw
    -- TODO: replace all refs that refer to the cnstr with the atom
    fullReduce >> RM.getRMTree

  RM.modifyRMContext $ \ctx -> ctx{ctxCnstrValidatorAddr = Nothing}

  RM.putRMTree $
    if
      | isTreeBottom res -> res
      | isTreeAtom res -> atomT
      -- The result might be a mutable due to an atom unifying with a mutable.
      | Just a <- VT.getMutableFromTree res >>= VT.getMutVal, isTreeAtom a -> atomT
      -- incomplete case
      | isTreeMutable res -> res
      | otherwise -> VT.mkBottomTree $ printf "constraint not satisfied, %s" (show res)

-- | Validate if a struct has any unreferenced let clauses.
validateStruct :: (RM.ReduceMonad s r m) => VT.Struct VT.Tree -> m ()
validateStruct s =
  let errM =
        Map.foldrWithKey
          ( \label lb acc ->
              if isNothing acc && not (VT.lbReferred lb)
                then Just $ VT.mkBottomTree $ printf "unreferenced let clause let %s" label
                else acc
          )
          Nothing
          (VT.stcLets s)
   in maybe (return ()) RM.putRMTree errM
