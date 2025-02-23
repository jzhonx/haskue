{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module PostReduce where

import Class
import Config
import Control.Monad.Reader (asks)
import Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import Reduction
import Ref
import TMonad
import Text.Printf (printf)
import Util
import Value.Tree

postValidation :: (TreeMonad s m) => m ()
postValidation = do
  logDebugStr "postValidation: start"

  ctx <- getTMContext
  -- remove all notifiers.
  putTMContext $ ctx{ctxNotifGraph = Map.empty}

  -- rewrite all functions to their results if the results exist.
  snapshotTM

  withTree $ \t -> logDebugStr $ printf "postValidation: tree: %s" (show t)

  -- then validate all constraints.
  traverseTM $ withTN $ \case
    TNConstraint c -> validateCnstr c
    TNStruct s -> validateStruct s
    _ -> return ()

{- | Traverse the tree and replace the Mutable node with the result of the mutator if it exists, otherwise the
original mutator node is kept.
-}
snapshotTM :: (TreeMonad s m) => m ()
snapshotTM =
  traverseTM $ withTN $ \case
    TNMutable m -> maybe (return ()) putTMTree (getMutVal m)
    _ -> return ()

-- Validate the constraint. It creates a validate function, and then evaluates the function. Notice that the validator
-- will be assigned to the constraint in the propValUp.
validateCnstr :: (TreeMonad s m) => Constraint Tree -> m ()
validateCnstr c = do
  addr <- getTMAbsAddr
  logDebugStr $
    printf
      "validateCnstr: addr: %s, validator: %s"
      (show addr)
      (show (cnsValidator c))
  modifyTMContext $ \ctx -> ctx{ctxCnstrValidatorAddr = Just addr}

  -- make sure return the latest atom
  let atomT = mkAtomVTree $ cnsAtom c
  -- run the validator in a sub context.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  res <- inTempSubTM (mkBottomTree "no value yet") $ do
    raw <- evalExprTM (cnsValidator c)
    putTMTree raw
    -- TODO: replace all refs that refer to the cnstr with the atom
    fullReduce >> getTMTree

  modifyTMContext $ \ctx -> ctx{ctxCnstrValidatorAddr = Nothing}

  putTMTree $
    if
      | isTreeBottom res -> res
      | isTreeAtom res -> atomT
      -- The result might be a mutable due to an atom unifying with a mutable.
      | Just a <- getMutableFromTree res >>= getMutVal, isTreeAtom a -> atomT
      -- incomplete case
      | isTreeMutable res -> res
      | otherwise -> mkBottomTree $ printf "constraint not satisfied, %s" (show res)

-- | Validate if a struct has any unreferenced let clauses.
validateStruct :: (TreeMonad s m) => Struct Tree -> m ()
validateStruct s =
  let errM =
        Map.foldrWithKey
          ( \seg sv acc ->
              if isNothing acc && checkSV sv
                then Just $ mkBottomTree $ printf "unreferenced let clause %s" (show seg)
                else acc
          )
          Nothing
          (stcSubs s)
   in maybe (return ()) putTMTree errM
 where
  checkSV :: StructVal Tree -> Bool
  checkSV (SLet (LetBinding{lbReferred = False})) = True
  checkSV _ = False
