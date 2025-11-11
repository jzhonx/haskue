{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Root where

import Control.Monad (foldM, when)
import Cursor
import Data.Aeson (ToJSON (..))
import Data.Foldable (toList)
import Data.Maybe (catMaybes, fromJust, isJust)
import qualified Data.Set as Set
import Feature
import NotifGraph (lookupGrpAddr)
import Reduce.Nodes (
  ResolvedPConjuncts (..),
  discoverPConjsFromUnifyOp,
  handleSObjChange,
  reduceCompreh,
  reduceDisj,
  reduceList,
  reduceStruct,
  resolveCloseFunc,
  resolveDisjOp,
  resolveInterpolation,
  resolvePendingConjuncts,
 )
import Reduce.RMonad (
  Context (..),
  ReduceMonad,
  debugInstantTM,
  emptySpanValue,
  getIsReducingRC,
  getRMContext,
  getTMAbsAddr,
  getTMCursor,
  getTMTree,
  inRemoteTM,
  inSubTM,
  modifyRMContext,
  modifyTMTN,
  modifyTMTree,
  preVisitTree,
  pushRecalcRootQ,
  throwFatal,
  traceSpanAdaptTM,
  traceSpanTM,
  treeDepthCheck,
 )
import Reduce.Recalc (recalc)
import Reduce.RefSys (
  CycleDetection (..),
  DerefResult (DerefResult),
  index,
 )
import qualified Reduce.RegOps as RegOps
import Reduce.UnifyOp (unifyNormalizedTCs)
import Text.Printf (printf)
import Value

-- | Reduce the tree to the lowest form.
reduce :: (ReduceMonad r s m) => m ()
reduce = do
  origAddr <- getTMAbsAddr
  traceSpanTM "reduce" reducePureFocus

  -- Add affected labels as new source of change.
  ng <- ctxNotifGraph <$> getRMContext
  xs <- handleSObjChange
  -- For each affected field, if it is not part of the notification graph (meaning no nodes depend on it or its
  -- sub-nodes), we need to reduce it first.
  mapM_
    ( \afAddr ->
        let siAddr = fromJust $ addrIsSufIrred afAddr
         in case lookupGrpAddr siAddr ng of
              Just gAddr -> pushRecalcRootQ gAddr
              Nothing -> inRemoteTM afAddr do
                reduce
                tc <- getTMCursor
                (_, gAddrs) <-
                  preVisitTree
                    (subNodes False)
                    ( \(x, a) -> case do
                        raddr <- addrIsSufRef (tcAddr x)
                        lookupGrpAddr (sufRefToSufIrred raddr) ng of
                        Just gAddr -> return (x, gAddr : a)
                        Nothing -> return (x, a)
                    )
                    (tc, [])
                debugInstantTM
                  "recalcNode"
                  (printf "preVisitTree done for affected addr %s, gAddrs: %s" (show afAddr) (show gAddrs))
                mapM_ pushRecalcRootQ gAddrs
    )
    xs

  when (isJust $ addrIsSufRef origAddr) recalc

withTreeDepthLimit :: (ReduceMonad r s m) => m a -> m a
withTreeDepthLimit f = do
  tc <- getTMCursor
  let addr = tcAddr tc
  treeDepthCheck tc
  push addr
  r <- f
  pop

  return r
 where
  push addr = modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}

  pop = modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}

reducePureFocus :: (ReduceMonad r s m) => m ()
reducePureFocus = withTreeDepthLimit $ do
  orig <- getTMTree

  case orig of
    -- When the node has TGen, we reduce it anyway, ignoring the tree node.
    IsTGenOp mut -> reduceMutable mut
    _ -> reducePureTN

  modifyTMTree $ \t ->
    (setTN orig (treeNode t))
      { isSCyclic = isSCyclic orig || isSCyclic t
      }

reduceMutable :: (ReduceMonad r s m) => Mutable -> m ()
reduceMutable (Mutable mop _) = case mop of
  Ref _ -> do
    (_, isReady) <- reduceArgs reduce rtrNonMut
    isReducingRCs <- getIsReducingRC
    if
      | not isReady -> return ()
      | isReducingRCs -> do
          -- Since the value of the reference was populated without reducing it, we need to reduce it if there is a
          -- mutval populated.
          -- TODO: set NoValRef
          tc <- getTMCursor
          (DerefResult rM _ _ isIterBinding) <- index tc
          handleRefRes isIterBinding rM
      | otherwise -> do
          tc <- getTMCursor
          (DerefResult rM _ cd isIterBinding) <- index tc
          case cd of
            NoCycleDetected -> handleRefRes isIterBinding rM
            RCDetected rcs -> do
              debugInstantTM "reduceMutable" (printf "detected ref cycle: %s" (show rcs))
              -- If we are not in the reducing reference cycles, this contains two cases:
              -- 1. No oldDesp
              -- 2. OldDesp has been added but in the unfinished expression evaluation, we find a new reference cycle.
              --    But this new reference cycle should not contain new info about the SCC as they are the same SCC.
              -- we should treat the reference cycle as an incomplete result.
              handleRefRes isIterBinding Nothing
  RegOp rop -> do
    r <-
      case ropOpType rop of
        InvalidOpType -> throwFatal "invalid op type"
        UnaryOpType op -> do
          (as, _) <- reduceArgs reduce rtrNonMut
          RegOps.resolveUnaryOp op (head as)
        -- Operands of the binary operation can be incomplete.
        BinOpType op -> do
          (as, _) <- reduceArgs reduce rtrNonMut
          getTMCursor >>= RegOps.resolveRegBinOp op (head as) (as !! 1)
        CloseFunc -> do
          (as, _) <- reduceArgs reduceToNonMut rtrNonMut
          getTMCursor >>= resolveCloseFunc (catMaybes as)
    handleMutRes r False
  Itp itp -> do
    (xs, isReady) <- reduceArgs reduce rtrNonMut
    r <-
      if isReady
        then resolveInterpolation itp (fromJust $ sequence xs)
        else return Nothing
    handleMutRes r False
  Compreh compreh -> reduceCompreh compreh
  DisjOp _ -> do
    -- Disjunction operation can have incomplete arguments.
    (_, _) <- reduceArgs reduce rtrNonMut
    r <- getTMCursor >>= resolveDisjOp
    handleMutRes r True
  UOp _ -> do
    pconjs <- discoverPConjsFromUnifyOp
    tc <- getTMCursor
    resolvePendingConjuncts pconjs tc >>= handleResolvedPConjsForUnifyMut

handleRefRes :: (ReduceMonad r s m) => Bool -> Maybe Tree -> m ()
handleRefRes _ Nothing = return ()
handleRefRes _ (Just result) = do
  tc <- getTMCursor
  case tc of
    TCFocus (IsRef _ _) -> do
      modifyTMTN (treeNode result)
      when result.isSCyclic $ modifyTMTree $ \t -> t{isSCyclic = True}
    _ -> throwFatal $ printf "handleRefRes: not a reference tree cursor, got %s" (show tc)

{-# INLINE handleMutRes #-}
handleMutRes :: (ReduceMonad r s m) => Maybe Tree -> Bool -> m ()
handleMutRes Nothing _ = return ()
handleMutRes (Just result) furtherReduce = do
  tc <- getTMCursor
  case tc of
    -- (TCFocus (IsRef _ _)) -> throwFatal "handleMutRes: tree cursor can not be a reference"
    (TCFocus (IsRef _ _)) -> return ()
    (TCFocus (IsTGenOp _)) -> do
      modifyTMTN (treeNode result)
      when furtherReduce reducePureTN
    -- _ -> throwFatal "handleMutRes: not a mutable tree"
    _ -> return ()

reducePureTN :: (ReduceMonad r s m) => m ()
reducePureTN = do
  t <- getTMTree
  case t of
    IsStruct _ -> reduceStruct
    IsList l -> reduceList l
    IsDisj d -> reduceDisj d
    _ -> return ()

{- | Reduce the arguments of a mutable tree.

It writes the reduced arguments back to the mutable tree and returns the reduced tree cursor.
It also returns the reduced arguments and whether the arguments are all reduced.
-}
reduceArgs :: (ReduceMonad r s m) => m () -> (Tree -> Maybe Tree) -> m ([Maybe Tree], Bool)
reduceArgs reduceFunc rtr = traceSpanAdaptTM "reduceArgs" emptySpanValue $ do
  tc <- getTMCursor
  case tcFocus tc of
    IsTGenOp mut@(Mutable _ mf) -> do
      (reducedArgs, updatedReducedSet) <-
        foldM
          ( \(accArgs, argsReducedSet) (i, _) -> do
              if not (i `Set.member` argsReducedSet)
                then do
                  r <- inSubTM (mkMutArgFeature i) $ reduceFunc >> rtr <$> getTMTree
                  return (r : accArgs, Set.insert i argsReducedSet)
                else do
                  r <- inSubTM (mkMutArgFeature i) $ rtr <$> getTMTree
                  return (r : accArgs, argsReducedSet)
          )
          ([], mfArgsReduced mf)
          (zip [0 ..] (toList $ getMutArgs mut))

      modifyTMTree $ \t -> case t of
        IsTGenOp newMut -> t{valGenEnv = TGenOp $ updateArgsReduced updatedReducedSet newMut}
        _ -> t

      return (reverse reducedArgs, isJust $ sequence reducedArgs)
    _ -> throwFatal "reduceArgs: not a mutable tree"
 where
  -- adapt (xs, b) = toJSON (map (fmap oneLinerStringOfTree) xs, b)
  adapt (xs, b) = toJSON ()

-- | Handle the resolved pending conjuncts for mutable trees.
handleResolvedPConjsForUnifyMut :: (ReduceMonad r s m) => ResolvedPConjuncts -> m ()
handleResolvedPConjsForUnifyMut IncompleteConjuncts = return ()
handleResolvedPConjsForUnifyMut (AtomCnstrConj ac) = modifyTMTN (TNAtomCnstr ac)
handleResolvedPConjsForUnifyMut (ResolvedConjuncts conjs) = do
  tc <- getTMCursor
  rM <- unifyNormalizedTCs conjs tc
  handleMutRes rM True

reduceToNonMut :: (ReduceMonad r s m) => m ()
reduceToNonMut = do
  t <- getTMTree
  case t of
    IsNoVal -> reduce
    _ -> return ()