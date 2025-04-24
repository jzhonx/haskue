{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.PostReduce where

import Common (Env, TreeOp (isTreeAtom, isTreeBottom, isTreeMutable), ctxRefSysGraph)
import Control.Monad.Reader (asks)
import qualified Cursor
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import qualified MutEnv
import qualified Path
import Reduce.Nodes (validateStructPerm, whenStruct)
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import Reduce.Root (fullReduce)
import qualified TCursorOps
import Text.Printf (printf)
import qualified Value.Tree as VT

postValidation :: (RM.ReduceTCMonad s r m) => m ()
postValidation = RM.debugSpanRM "postValidation" $ do
  ctx <- RM.getRMContext
  -- remove all notifiers.
  RM.putRMContext $ ctx{ctxRefSysGraph = Map.empty}

  -- rewrite all functions to their results if the results exist.
  snapshotRM
  simplifyRM

  t <- RM.getRMTree
  RM.debugSpanArgsRM "validate" (VT.treeFullStr 0 t) $ do
    -- then validate all constraints.
    RM.traverseRM $ RM.withTN $ \case
      VT.TNAtomCnstr c -> validateCnstr c
      VT.TNStruct s -> validateStruct s
      _ -> return ()

{- | Traverse the tree and does the following things with the node:

1. Replace the Mutable node with the result of the mutator if it exists, otherwise the original mutator node is kept.
2. Replace the CnstredVal node with its value.
3. Check struct permission and empty all stub value containers of the struct, which are constraints, dynamic fields and
embeddings. All the pending values should have been already applied to the static fields.
-}
snapshotRM :: (RM.ReduceTCMonad s r m) => m ()
snapshotRM = RM.debugSpanRM "snapshotRM" $ do
  RM.traverseRM $ RM.withTN $ \case
    VT.TNMutable m -> maybe (return ()) RM.putRMTree (VT.getMutVal m)
    VT.TNCnstredVal c -> RM.putRMTree $ VT.cnsedVal c
    _ -> return ()

{- | Traverse the tree and does the following things with the node:

1. Check struct permission and empty all stub value containers of the struct, which are constraints, dynamic fields and
embeddings. All the pending values should have been already applied to the static fields.
-}
simplifyRM :: (RM.ReduceTCMonad s r m) => m ()
simplifyRM = RM.debugSpanRM "simplifyRM" $ do
  RM.traverseRM $ RM.withTN $ \case
    VT.TNStruct s -> do
      validateStructPerm s
      whenStruct () $ \_ ->
        RM.modifyRMTN $
          VT.TNStruct $
            s
              { VT.stcCnstrs = IntMap.empty
              , VT.stcEmbeds = IntMap.empty
              , VT.stcDynFields = IntMap.empty
              , VT.stcPerms = []
              }
    _ -> return ()

{- | Validate the constraint.

It creates a validate function, and then evaluates the function. Notice that the validatorß will be assigned to the
constraint in the propValUp.
-}
validateCnstr :: (RM.ReduceTCMonad s r m) => VT.AtomCnstr VT.Tree -> m ()
validateCnstr c = RM.debugSpanRM "validateCnstr" $ do
  -- We can first assume that the tree value is an atom. Make sure the latest atom is created.
  let atomT = VT.mkAtomVTree $ VT.cnsAtom c
  RM.putRMTree atomT

  MutEnv.Functions{MutEnv.fnEvalExpr = evalExpr} <- asks MutEnv.getFuncs
  raw <- evalExpr (VT.cnsValidator c)
  tc <- RM.getRMCursor
  validator <- replaceVertCycleRef (VT.mkAtomVTree $ VT.cnsAtom c) (raw `Cursor.setTCFocus` tc)
  RM.debugInstantRM "validateCnstr" $
    printf "raw: %s, validator: %s" (VT.treeFullStr 0 raw) (VT.treeFullStr 0 validator)

  -- Run the validator in a sub context of an atom value.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  res <- RM.inTempSubRM validator $ do
    -- TODO: replace all refs that refer to the cnstr with the atom
    fullReduce >> RM.getRMTree

  RM.putRMTree $
    if
      | isTreeBottom res -> res
      -- The result is valid.
      | isTreeAtom res -> atomT
      -- The result might be a mutable due to an atom unifying with a mutable.
      | Just a <- VT.getMutableFromTree res >>= VT.getMutVal, isTreeAtom a -> atomT
      -- incomplete case
      | isTreeMutable res -> res
      | otherwise -> VT.mkBottomTree $ printf "constraint not satisfied, %s" (show res)

{- | Replace any reference in the validator of the atom constraint that references the constraint and forms a vertical
cycle with the constraint's atom.
-}
replaceVertCycleRef :: (Env r s m) => VT.Tree -> Cursor.TreeCursor VT.Tree -> m VT.Tree
replaceVertCycleRef atomT cnstrTC = do
  let cnstrAddr = Cursor.tcTreeAddr cnstrTC
  utc <- TCursorOps.traverseTCSimple VT.subNodes (replace cnstrAddr) cnstrTC
  return (Cursor.tcFocus utc)
 where
  replace cnstrAddr tc = do
    let focus = Cursor.tcFocus tc
    rfM <- case VT.getMutableFromTree focus of
      Just (VT.Ref rf) -> return $ VT.refFromRefArg (\x -> Path.StringSel <$> VT.getStringFromTree x) (VT.refArg rf)
      _ -> return Nothing

    maybe
      (return focus)
      -- If the focus is a reference, we need to check if the ref references the cnstrAddr.
      ( \rf -> do
          rE <- RefSys.goTCLAAddr rf tc
          case rE of
            Left err -> return err
            Right m ->
              maybe
                (return focus)
                ( \rtc ->
                    return $
                      if Cursor.tcTreeAddr rtc == cnstrAddr
                        then atomT
                        else focus
                )
                m
      )
      rfM

{- | Validate the struct for the following cases:

1. If it has any unreferenced let clauses.
2. If its permission is right.
-}
validateStruct :: (RM.ReduceTCMonad s r m) => VT.Struct VT.Tree -> m ()
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
