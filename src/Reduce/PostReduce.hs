{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.PostReduce where

import Common (Env, TreeOp (isTreeAtom, isTreeBottom, isTreeMutable), buildASTExpr, ctxNotifGraph)
import Control.Monad (when)
import qualified Cursor
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isNothing)
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified Path
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import Reduce.Root (fullReduce)
import qualified Reduce.UnifyOp as UnifyOp
import qualified TCOps
import Text.Printf (printf)
import qualified Value.Tree as VT

postValidation :: (RM.ReduceTCMonad s r m) => m ()
postValidation = RM.debugSpanTM "postValidation" $ do
  ctx <- RM.getRMContext
  -- remove all notifiers.
  RM.putRMContext $ ctx{ctxNotifGraph = Map.empty}

  -- rewrite all functions to their results if the results exist.
  snapshotRM
  simplifyRM

  t <- RM.getTMTree
  RM.debugSpanArgsTM "validate" (VT.treeFullStr 0 t) $ do
    -- then validate all constraints.
    RM.traverseTM $ RM.withTN $ \case
      VT.TNAtomCnstr c -> validateCnstr c
      _ -> return ()

  unreferred <- RM.getRMUnreferredLets
  RM.withTree $ \res -> do
    when (not (null unreferred) && not (isTreeBottom res)) $ do
      let u = head unreferred
      label <- case Path.lastSeg u of
        Just (Path.StructTASeg (Path.LetTASeg label)) -> return label
        _ -> throwErrSt "invalid let seg"

      RM.putTMTree $
        VT.mkBottomTree $
          printf "unreferenced let clause let %s" label

{- | Traverse the tree and does the following things with the node:

1. Replace the Mutable node with the result of the mutator if it exists, otherwise the original mutator node is kept.
2. Replace the CnstredVal node with its value.
3. Check struct permission and empty all stub value containers of the struct, which are constraints, dynamic fields and
embeddings. All the pending values should have been already applied to the static fields.
-}
snapshotRM :: (RM.ReduceTCMonad s r m) => m ()
snapshotRM = RM.debugSpanTM "snapshotRM" $ do
  RM.traverseTM $ RM.withTN $ \case
    VT.TNBlock block
      | Just ev <- VT.blkNonStructValue block -> RM.modifyTMNodeWithTree ev
    VT.TNMutable m -> maybe (return ()) RM.modifyTMNodeWithTree (VT.getMutVal m)
    VT.TNCnstredVal c -> RM.modifyTMNodeWithTree $ VT.cnsedVal c
    _ -> return ()

{- | Traverse the tree and does the following things with the node:

1. Check struct permission and empty all stub value containers of the struct, which are constraints, dynamic fields and
embeddings. All the pending values should have been already applied to the static fields.
-}
simplifyRM :: (RM.ReduceTCMonad s r m) => m ()
simplifyRM = RM.debugSpanTM "simplifyRM" $ do
  RM.traverseTM $ do
    RM.withTN $ \case
      VT.TNBlock _ -> validateStructPerm
      _ -> return ()

    RM.withTN $ \case
      VT.TNBlock block
        | Just _ <- VT.blkNonStructValue block -> throwErrSt "non struct value exists in block"
        | otherwise ->
            RM.modifyTMTN $
              VT.TNBlock $
                ( VT.modifyBlockStruct
                    ( \st ->
                        st
                          { VT.stcCnstrs = IntMap.empty
                          , VT.stcDynFields = IntMap.empty
                          , VT.stcPerms = []
                          }
                    )
                    block
                )
                  { VT.blkEmbeds = IntMap.empty
                  }
      _ -> return ()

{- | Validate the constraint.

It creates a validate function, and then evaluates the function. Notice that the validator will be assigned to the
constraint in the propValUp.
-}
validateCnstr :: (RM.ReduceTCMonad s r m) => VT.AtomCnstr VT.Tree -> m ()
validateCnstr c = RM.debugSpanTM "validateCnstr" $ do
  -- We can first assume that the tree value is an atom. Make sure the latest atom is created.
  let atomT = VT.mkAtomVTree $ VT.cnsAtom c
  RM.putTMTree atomT

  raw <- RM.evalExprRM (VT.cnsValidator c)
  tc <- RM.getTMCursor
  validator <- replaceSelfRef (VT.mkAtomVTree $ VT.cnsAtom c) (raw `Cursor.setTCFocus` tc)
  RM.debugInstantTM "validateCnstr" $
    printf "raw: %s, validator: %s" (VT.treeFullStr 0 raw) (VT.treeFullStr 0 validator)

  -- Run the validator in a sub context of an atom value.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  res <- RM.inTempSubTM validator $ do
    -- TODO: replace all refs that refer to the cnstr with the atom
    fullReduce >> RM.getTMTree

  RM.putTMTree $
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
replaceSelfRef :: (RM.ReduceMonad s r m) => VT.Tree -> TCOps.TrCur -> m VT.Tree
replaceSelfRef atomT cnstrTC = RM.debugSpanRM "replaceSelfRef" Just cnstrTC $ do
  let cnstrAddr = Cursor.tcCanAddr cnstrTC
  utc <- TCOps.traverseTCSimple VT.subNodes (replace cnstrAddr) cnstrTC
  return (Cursor.tcFocus utc)
 where
  replace cnstrAddr tc = do
    let focus = Cursor.tcFocus tc
    rfM <- case VT.getMutableFromTree focus of
      Just (VT.Ref rf) -> return $ VT.valPathFromRef VT.getAtomFromTree rf
      _ -> return Nothing

    maybe
      (return focus)
      -- If the focus is a reference, we need to check if the ref references the cnstrAddr.
      ( \rf -> do
          rE <- RefSys.goTCLAAddr rf tc
          RM.debugInstantRM "replaceSelfRef" (printf "rE: %s" (show rE)) cnstrTC
          case rE of
            Left err -> return err
            Right m ->
              maybe
                (return focus)
                ( \rtc ->
                    return $
                      if Cursor.tcCanAddr rtc == cnstrAddr
                        then atomT
                        else focus
                )
                m
      )
      rfM

validateStructPerm :: (RM.ReduceTCMonad s r m) => m ()
validateStructPerm = RM.debugSpanTM "validateStructPerm" $ do
  t <- RM.getTMTree
  case VT.treeNode t of
    -- After snapsnot, the VT.blkNonStructValue should be None.
    VT.TNBlock (VT.Block{VT.blkStruct = s}) -> mapM_ (validatePermItem s) (VT.stcPerms s)
    _ -> return ()

{- | Validate the permission item.

A struct must be provided so that dynamic fields and constraints can be found.

It constructs the allowing labels and constraints and checks if the joining labels are allowed.
-}
validatePermItem :: (RM.ReduceTCMonad s r m) => VT.Struct VT.Tree -> VT.PermItem -> m ()
validatePermItem struct p = RM.debugSpanTM "validatePermItem" $ do
  let
    dynsM = dynIdxesToLabels (VT.piDyns p)
    labels = VT.piLabels p
    cnstrs = IntMap.fromList $ map (\i -> (i, VT.stcCnstrs struct IntMap.! i)) (Set.toList $ VT.piCnstrs p)
    opDynsM = dynIdxesToLabels (VT.piOpDyns p)
    opLabels = VT.piOpLabels p
  case (dynsM, opDynsM) of
    (Just dyns, Just opDyns) ->
      RM.getTMCursor
        >>= UnifyOp.checkLabelsPerm
          (labels `Set.union` dyns)
          cnstrs
          True
          False
          (opLabels `Set.union` opDyns)
        >>= RM.putTMCursor
    -- If not all dynamic fields can be resolved to string labels, we can not check the permission.
    -- This is what CUE does.
    _ -> return ()
 where
  dynIdxesToLabels :: Set.Set Int -> Maybe (Set.Set String)
  dynIdxesToLabels idxes =
    Set.fromList
      <$> mapM
        ( \i ->
            VT.getStringFromTree (VT.dsfLabel $ VT.stcDynFields struct IntMap.! i)
        )
        (Set.toList idxes)