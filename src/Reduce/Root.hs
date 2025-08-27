{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Root where

import Common (
  Config (..),
  Context (..),
  HasConfig (..),
  HasContext (..),
  RefCycleDesp (..),
  RuntimeParams (..),
  emptyRefCycleDesp,
 )
import Control.Monad (foldM, when)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (get, modify, put, runStateT)
import Cursor
import Data.Aeson (ToJSON (..), encode)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (catMaybes, fromJust, isJust)
import Exception (throwErrSt)
import NotifGraph (lookupSCCAddr)
import Path
import Reduce.Nodes (
  ResolvedPConjuncts (..),
  discoverPConjs,
  reduceBlock,
  reduceCompreh,
  reduceDisj,
  reduceList,
  resolveCloseFunc,
  resolveDisjOp,
  resolveInterpolation,
  resolvePendingConjuncts,
 )
import Reduce.Notif (startNotify)
import Reduce.RMonad (
  RTCState (..),
  ReduceMonad,
  ResolveMonad,
  debugInstantRM,
  debugInstantTM,
  debugSpanAdaptTM,
  debugSpanArgsTM,
  debugSpanTM,
  delMutValRecvs,
  deleteTMRCDesp,
  getRMContext,
  getRMGlobalVers,
  getTMAbsAddr,
  getTMCursor,
  getTMRCDesp,
  getTMTree,
  inRemoteTM,
  inSubTM,
  modifyRMContext,
  modifyTMTN,
  modifyTMTree,
  putRMContext,
  putTMCursor,
  putTMTree,
  setIsReducingRC,
  treeDepthCheck,
  withResolveMonad,
 )
import Reduce.RefSys (
  CycleDetection (..),
  DerefResult (DerefResult),
  index,
  populateRCRefs,
  populateRCRefsWithTop,
 )
import qualified Reduce.RegOps as RegOps
import Reduce.UnifyOp (unifyNormalizedTCs)
import Text.Printf (printf)
import Value

-- | Reduce the tree to the lowest form.
reduce :: (ReduceMonad s r m) => m ()
reduce = debugSpanTM "reduce" $ do
  origAddr <- getTMAbsAddr
  reduceTCFocus

  let origRfbAddr = trimToReferable origAddr
  when (origRfbAddr == origAddr) $ do
    ctx <- getRMContext
    case ctxRefCycleDetected ctx of
      -- If there is a reference cycle description, we should handle it immediately when we are in the node with
      -- referable address.
      Just rcDesp
        | not (rcdIsReducingRCs rcDesp) -> reduceRefCycles (rcdRCAddrs rcDesp)
      Nothing -> do
        let ng = Common.ctxNotifGraph ctx
        case lookupSCCAddr origRfbAddr ng of
          Just sccAddr
            | not (ctxIsNotifying ctx) -> startNotify sccAddr
          _ -> return ()
      _ -> return ()

  vers <- getRMGlobalVers
  modifyTMTree (\t -> t{treeVersion = vers})

withTreeDepthLimit :: (ReduceMonad s r m) => m a -> m a
withTreeDepthLimit f = do
  tc <- getTMCursor
  let addr = tcCanAddr tc
  treeDepthCheck tc
  push addr
  r <- f
  pop

  return r
 where
  push addr = modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}

  pop = modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}

reduceTCFocus :: (ReduceMonad s r m) => m ()
reduceTCFocus = withTreeDepthLimit $ do
  orig <- getTMTree

  case treeNode orig of
    TNMutable mut -> reduceMutable mut
    TNBlock _ -> reduceBlock
    TNList l -> reduceList l
    TNDisj d -> reduceDisj d
    _ -> return ()

  modifyTMTree $ \t ->
    (setTN orig (treeNode t))
      { treeIsCyclic = treeIsCyclic orig || treeIsCyclic t
      }

reduceMutable :: (ReduceMonad s r m) => Mutable -> m ()
reduceMutable (Mutable mop _) = case mop of
  Ref ref -> do
    (_, isReady) <- reduceArgs reduce rtrNonMut
    oldDespM <- getTMRCDesp
    if
      | not isReady -> return ()
      | Just oldDesp <- oldDespM
      , rcdIsReducingRCs oldDesp -> do
          -- Since the value of the reference was populated without reducing it, we need to reduce it now.
          inSubTM SubValTASeg reduce
      | otherwise -> do
          tc <- getTMCursor
          (DerefResult rM tarAddr cd isIterBinding) <- index ref tc
          case cd of
            NoCycleDetected -> handleRefRes isIterBinding rM
            SCDetected _ -> do
              -- If the target is cyclic, and it is not used to only reduce mutable, we should return structural
              -- cycle.
              -- This handles two cases:
              -- 1. The ref had not been marked as cyclic. For example, f: {out: null | f}, the inner f.
              -- 2. The ref had been marked as cyclic. For example, reducing f when reducing the y.
              -- { f: {out: null | f },  y: f }
              handleRefRes isIterBinding (Just $ mkBottomTree "structural cycle")
              modifyTMTree $ \t -> t{treeIsCyclic = True}
            RCDetected rcs -> do
              debugInstantTM "reduceMutable" (printf "detected ref cycle: %s, oldDesp: %s" (show rcs) (show oldDespM))
              -- If we are not in the reducing reference cycles, this contains two cases:
              -- 1. No oldDesp
              -- 2. OldDesp has been added but in the unfinished expression evaluation, we find a new reference cycle.
              --    But this new reference cycle should not contain new info about the SCC as they are the same SCC.
              -- we should treat the reference cycle as an incomplete result.
              ctx <- getRMContext
              putRMContext ctx{ctxRefCycleDetected = Just $ emptyRefCycleDesp{rcdRCAddrs = rcs}}
              handleRefRes isIterBinding Nothing
  RegOp rop -> do
    (as, isReady) <- reduceArgs reduce rtrNonMut
    r <-
      case ropOpType rop of
        InvalidOpType -> throwErrSt "invalid op type"
        UnaryOpType op -> RegOps.resolveUnaryOp op (head as)
        -- Operands of the binary operation can be incomplete.
        BinOpType op -> getTMCursor >>= RegOps.resolveRegBinOp op (head as) (as !! 1)
        CloseFunc
          | isReady -> getTMCursor >>= resolveCloseFunc (catMaybes as)
        _ -> return Nothing
    handleMutRes r False
  Itp itp -> do
    (_, isReady) <- reduceArgs reduce rtrNonMut
    r <-
      if isReady
        then resolveInterpolation itp
        else return Nothing
    handleMutRes r False
  Compreh compreh -> do
    r <- getTMCursor >>= reduceCompreh compreh
    -- the result of the comprehension could be an un-reduced tree or a unification op tree.
    handleMutRes r True
  DisjOp _ -> do
    -- Disjunction operation can have incomplete arguments.
    (_, _) <- reduceArgs reduce rtrNonMut
    r <- getTMCursor >>= resolveDisjOp False
    handleMutRes r True
  UOp _ -> do
    pconjs <- discoverPConjs
    tc <- getTMCursor
    resolvePendingConjuncts pconjs tc >>= handleResolvedPConjsForUnifyMut

handleRefRes :: (ReduceMonad s r m) => Bool -> Maybe Tree -> m ()
handleRefRes _ Nothing = return ()
handleRefRes isIterBinding (Just result) = do
  tc <- getTMCursor
  case tc of
    TCFocus t@(IsRef mut ref) -> do
      let addr = tcCanAddr tc

      case rtrNonMut result of
        -- No concrete value is found.
        Nothing -> return ()
        Just v
          -- If it is an iter binding, we can just return the reduced value.
          | isIterBinding -> do
              -- TODO: change dependents addresses from /sv to non-sv.
              delMutValRecvs addr
              putTMTree v
          | otherwise -> do
              delMutValRecvs addr
              let
                newMut = setMutOp (Ref ref{refVers = Just (treeVersion v)}) mut
                newT = setTN t (TNMutable $ setMutVal (Just v) newMut)
              putTMCursor $ newT `setTCFocus` tc

      rtc <- getTMCursor
      debugInstantRM
        "handleRefRes"
        (printf "result: %s, mut: %s, res: %s" (show result) (show $ mkMutableTree mut) (show $ tcFocus rtc))
        tc
    _ -> throwErrSt $ printf "handleRefRes: not a reference tree cursor, got %s" (show tc)

handleMutRes :: (ReduceMonad s r m) => Maybe Tree -> Bool -> m ()
handleMutRes Nothing _ = return ()
handleMutRes (Just result) furtherReduce = do
  tc <- getTMCursor
  case tc of
    (TCFocus (IsRef _ _)) -> throwErrSt "handleMutRes: tree cursor can not be a reference"
    (TCFocus (IsMutable mut)) -> do
      let addr = tcCanAddr tc

      next <-
        if furtherReduce
          then do
            putValInMutVal (Just result)
            inSubTM SubValTASeg (reduce >> getTMTree)
          else return result
      -- If the rM is another mutable tree, we need to check if the mutval exists by trying to get it.
      case rtrNonMut next of
        -- No concrete value is found.
        Nothing -> do
          -- We still remove receivers in case some refs have been reduced.
          delMutValRecvs addr
          putValInMutVal Nothing
        Just v
          -- If the value does not have immediate references or it is an iter binding, we can just return the reduced value.
          | isMutableReducible mut -> do
              -- TODO: change dependents addresses from /sv to non-sv.
              putTMTree v
          | otherwise -> do
              delMutValRecvs addr
              putValInMutVal (Just v)
      debugInstantRM
        "handleMutRes"
        (printf "result: %s, mut: %s, next: %s" (show result) (show $ mkMutableTree mut) (show next))
        tc
    _ -> throwErrSt "handleMutRes: not a mutable tree"

putValInMutVal :: (ReduceMonad s r m) => Maybe Tree -> m ()
putValInMutVal m = do
  tc <- getTMCursor
  case tcFocus tc of
    IsMutable mut -> do
      let newMut = setMutVal m mut
      putTMCursor (setTCFocusTN (TNMutable newMut) tc)
    _ -> throwErrSt "putValInMutVal: not a mutable tree"

{- | Check whether the mutator is reducible.

If the mutible tree is a reference or any of recursively true for its args, then it is not reducible.

For example, if the argument of the unify is a struct which has references as its fields, then it is reducible because
the holding block of the reference is not going to be changed.
-}
isMutableReducible :: Mutable -> Bool
isMutableReducible mut = not $ mutHasRefAsImChild mut

{- | Check whether the mutable tree has a reference as its immediate child, which means it is not a child of a container
node, such as a struct or a list.
-}
mutHasRefAsImChild :: Mutable -> Bool
mutHasRefAsImChild (MutOp (Ref _)) = True
mutHasRefAsImChild mut = any go (getMutArgs mut)
 where
  go argT = case treeNode argT of
    TNMutable mutArg -> mutHasRefAsImChild mutArg
    _ -> False

{- | Reduce the arguments of a mutable tree.

It writes the reduced arguments back to the mutable tree and returns the reduced tree cursor.
It also returns the reduced arguments and whether the arguments are all reduced.
-}
reduceArgs :: (ReduceMonad s r m) => m () -> (Tree -> Maybe Tree) -> m ([Maybe Tree], Bool)
reduceArgs f rtr = debugSpanAdaptTM "reduceArgs" adapt $ do
  tc <- getTMCursor
  case tcFocus tc of
    IsMutable mut -> do
      reducedArgs <-
        foldM
          ( \accArgs (i, _) -> do
              r <- inSubTM (MutArgTASeg i) (reduceArg f (rtr . tcFocus))
              return $ r : accArgs
          )
          []
          (zip [0 ..] (toList $ getMutArgs mut))

      return (reverse reducedArgs, isJust $ sequence reducedArgs)
    _ -> throwErrSt "reduceArgs: not a mutable tree"
 where
  adapt (xs, b) = toJSON (map (fmap oneLinerStringOfCurTreeState) xs, b)

reduceArg :: (ReduceMonad s r m) => m () -> (TrCur -> a) -> m a
reduceArg f convert = do
  tc <- getTMCursor
  oldDespM <- getTMRCDesp
  let arg = tcFocus tc
  -- If the argument is not reduced, or we are in the middle of reducing reference cycles, we need to reduce it.
  -- TODO: treeVersion is not needed, only treeIsEvaled is needed.
  if treeVersion arg == 0 || maybe False rcdIsReducingRCs oldDespM
    then f >> convert <$> getTMCursor
    -- If the argument is already reduced, we can just return it.
    else return (convert tc)

-- | Handle the resolved pending conjuncts for mutable trees.
handleResolvedPConjsForUnifyMut :: (ReduceMonad s r m) => ResolvedPConjuncts -> m ()
handleResolvedPConjsForUnifyMut IncompleteConjuncts = return ()
handleResolvedPConjsForUnifyMut (AtomCnstrConj ac) = do
  t <- getTMTree
  case t of
    IsMutable mut -> do
      let
        v = mkAtomCnstrTree ac
        newMut = setMutVal (Just v) mut
      modifyTMTN (TNMutable newMut)
    _ -> throwErrSt "handleResolvedPConjsForUnifyMut: not a mutable tree"
handleResolvedPConjsForUnifyMut (ResolvedConjuncts conjs) = do
  tc <- getTMCursor
  rM <- unifyNormalizedTCs conjs tc
  handleMutRes rM True

reduceRefCycles :: (ReduceMonad s r m) => [TreeAddr] -> m ()
reduceRefCycles [] = throwErrSt "reduceRefCycles: empty address list"
reduceRefCycles addrs = debugSpanTM "reduceRefCycles" $ do
  setIsReducingRC True
  mapM_
    ( \addr -> inRemoteTM addr $ do
        withResolveMonad $ \tc -> do
          rTC <- populateRCRefs addrs [tcCanAddr tc] tc
          debugInstantRM
            "reduceRefCycles"
            (printf "new populated-tc: %s" (show $ tcFocus rTC))
            rTC
          return (rTC, ())

        x <- getTMCursor
        debugInstantTM
          "reduceRefCycles"
          (printf "tree with RCs has been populated to: %s" (show $ tcFocus x))

        reduce
        withResolveMonad $ \tc -> do
          rTC <- populateRCRefsWithTop tc
          return (rTC, ())
    )
    addrs
  deleteTMRCDesp
  ctx <- getRMContext
  origRfbAddr <- getTMAbsAddr
  let ng = Common.ctxNotifGraph ctx
  case lookupSCCAddr origRfbAddr ng of
    Just sccAddr
      | not (ctxIsNotifying ctx) -> startNotify sccAddr
    _ -> return ()
