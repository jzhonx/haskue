{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.PostReduce where

import Common (ctxNotifGraph)
import Control.Monad (when)
import Cursor
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import Path
import Reduce.RMonad (
  ReduceMonad,
  ReduceTCMonad,
  debugInstantRM,
  debugInstantTM,
  debugSpanArgsTM,
  debugSpanRM,
  debugSpanTM,
  evalExprRM,
  getRMContext,
  getRMUnreferredLets,
  getTMCursor,
  getTMTree,
  modifyTMNodeWithTree,
  modifyTMTN,
  putRMContext,
  putTMCursor,
  putTMTree,
  traverseTM,
  withTN,
  withTree,
 )
import Reduce.RefSys (goTCLAAddr)
import Reduce.Root (reduce)
import Reduce.UnifyOp (checkLabelsPerm)
import Text.Printf (printf)
import Value

postValidation :: (ReduceTCMonad s r m) => m ()
postValidation = debugSpanTM "postValidation" $ do
  ctx <- getRMContext
  -- remove all notifiers.
  putRMContext $ ctx{ctxNotifGraph = Map.empty}

  -- rewrite all functions to their results if the results exist.
  snapshotRM
  simplifyRM

  t <- getTMTree
  debugSpanArgsTM "validate" (treeFullStr 0 t) $ do
    -- then validate all constraints.
    traverseTM $ withTN $ \case
      TNAtomCnstr c -> validateCnstr c
      _ -> return ()

  unreferred <- getRMUnreferredLets
  withTree $ \res -> do
    when (not (null unreferred) && (case res of IsBottom _ -> False; _ -> True)) $ do
      let u = head unreferred
      label <- case lastSeg u of
        Just (StructTASeg (LetTASeg label)) -> return label
        _ -> throwErrSt "invalid let seg"

      putTMTree $ mkBottomTree $ printf "unreferenced let clause let %s" (T.unpack $ TE.decodeUtf8 label)

{- | Traverse the tree and does the following things with the node:

1. Replace the Mutable node with the result of the mutator if it exists, otherwise the original mutator node is kept.
2. Replace the CnstredVal node with its value.
3. Check struct permission and empty all stub value containers of the struct, which are constraints, dynamic fields and
embeddings. All the pending values should have been already applied to the static fields.
-}
snapshotRM :: (ReduceTCMonad s r m) => m ()
snapshotRM = debugSpanTM "snapshotRM" $ do
  traverseTM $ withTN $ \case
    TNBlock block
      | Just ev <- blkNonStructValue block -> modifyTMNodeWithTree ev
    TNMutable m -> maybe (return ()) modifyTMNodeWithTree (getMutVal m)
    TNCnstredVal c -> modifyTMNodeWithTree $ cnsedVal c
    _ -> return ()

{- | Traverse the tree and does the following things with the node:

1. Check struct permission and empty all stub value containers of the struct, which are constraints, dynamic fields and
embeddings. All the pending values should have been already applied to the static fields.
-}
simplifyRM :: (ReduceTCMonad s r m) => m ()
simplifyRM = debugSpanTM "simplifyRM" $ do
  traverseTM $ do
    withTN $ \case
      TNBlock _ -> validateStructPerm
      _ -> return ()

    withTN $ \case
      TNBlock block
        | Just _ <- blkNonStructValue block -> throwErrSt "non struct value exists in block"
        | otherwise ->
            modifyTMTN $
              TNBlock $
                ( modifyBlockStruct
                    ( \st ->
                        st
                          { stcCnstrs = IntMap.empty
                          , stcDynFields = IntMap.empty
                          , stcPerms = []
                          }
                    )
                    block
                )
                  { blkEmbeds = IntMap.empty
                  }
      _ -> return ()

{- | Validate the constraint.

It creates a validate function, and then evaluates the function. Notice that the validator will be assigned to the
constraint in the propValUp.
-}
validateCnstr :: (ReduceTCMonad s r m) => AtomCnstr -> m ()
validateCnstr c = debugSpanTM "validateCnstr" $ do
  -- We can first assume that the tree value is an atom. Make sure the latest atom is created.
  let atomT = mkAtomTree $ cnsAtom c
  putTMTree atomT

  raw <- evalExprRM (cnsValidator c)
  tc <- getTMCursor
  validator <- replaceSelfRef (mkAtomTree $ cnsAtom c) (raw `setTCFocus` tc)
  debugInstantTM "validateCnstr" $
    printf "raw: %s, validator: %s" (treeFullStr 0 raw) (treeFullStr 0 validator)

  -- Run the validator in a sub context of an atom value.
  -- We should never trigger others because the field is supposed to be atom and no value changes.
  res <- reduce (validator `setTCFocus` tc)
  putTMTree $ case res of
    IsBottom _ -> res
    -- The result is valid.
    IsAtom _ -> atomT
    IsMutable mut
      -- The result might be a mutable due to an atom unifying with a mutable.
      | Just a <- getMutVal mut, IsAtom _ <- a -> atomT
      -- incomplete case
      | otherwise -> res
    _ -> mkBottomTree $ printf "constraint not satisfied, %s" (show res)

{- | Replace any reference in the validator of the atom constraint that references the constraint and forms a vertical
cycle with the constraint's atom.
-}
replaceSelfRef :: (ReduceMonad s r m) => Tree -> TrCur -> m Tree
replaceSelfRef atomT cnstrTC = debugSpanRM "replaceSelfRef" Just cnstrTC $ do
  let cnstrAddr = tcCanAddr cnstrTC
  utc <- traverseTCSimple subNodes (replace cnstrAddr) cnstrTC
  return (tcFocus utc)
 where
  replace cnstrAddr tc = do
    let focus = tcFocus tc
    rfM <- case focus of
      IsRef rf -> return $ valPathFromRef rtrAtom rf
      _ -> return Nothing

    maybe
      (return focus)
      -- If the focus is a reference, we need to check if the ref references the cnstrAddr.
      ( \rf -> do
          rE <- goTCLAAddr rf tc
          debugInstantRM "replaceSelfRef" (printf "rE: %s" (show rE)) cnstrTC
          case rE of
            Left err -> return err
            Right m ->
              maybe
                (return focus)
                ( \rtc ->
                    return $
                      if tcCanAddr rtc == cnstrAddr
                        then atomT
                        else focus
                )
                m
      )
      rfM

validateStructPerm :: (ReduceTCMonad s r m) => m ()
validateStructPerm = debugSpanTM "validateStructPerm" $ do
  t <- getTMTree
  case treeNode t of
    -- After snapsnot, the blkNonStructValue should be None.
    TNBlock (Block{blkStruct = s}) -> mapM_ (validatePermItem s) (stcPerms s)
    _ -> return ()

{- | Validate the permission item.

A struct must be provided so that dynamic fields and constraints can be found.

It constructs the allowing labels and constraints and checks if the joining labels are allowed.
-}
validatePermItem :: (ReduceTCMonad s r m) => Struct -> PermItem -> m ()
validatePermItem struct p = debugSpanTM "validatePermItem" $ do
  let
    dynsM = dynIdxesToLabels (piDyns p)
    labels = piLabels p
    cnstrs = IntMap.fromList $ map (\i -> (i, stcCnstrs struct IntMap.! i)) (Set.toList $ piCnstrs p)
    opDynsM = dynIdxesToLabels (piOpDyns p)
    opLabels = piOpLabels p
  case (dynsM, opDynsM) of
    (Just dyns, Just opDyns) ->
      getTMCursor
        >>= checkLabelsPerm
          (labels `Set.union` dyns)
          cnstrs
          True
          False
          (opLabels `Set.union` opDyns)
        >>= putTMCursor
    -- If not all dynamic fields can be resolved to string labels, we can not check the permission.
    -- This is what CUE does.
    _ -> return ()
 where
  dynIdxesToLabels :: Set.Set Int -> Maybe (Set.Set T.Text)
  dynIdxesToLabels idxes =
    Set.fromList
      <$> mapM
        ( \i ->
            rtrString (dsfLabel $ stcDynFields struct IntMap.! i)
        )
        (Set.toList idxes)