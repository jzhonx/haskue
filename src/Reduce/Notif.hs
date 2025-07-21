{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Reduce.Notif where

import Common (Context (..))
import qualified Common
import Control.Monad (foldM, when)
import Control.Monad.State.Strict (get, gets, modify, put, runStateT)
import Cursor
import Data.Maybe (fromMaybe, isJust, maybeToList)
import qualified Data.Sequence as Seq
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import NotifGraph
import Path
import qualified Reduce.Nodes as Nodes
import Reduce.RMonad (
  ReduceMonad,
  ResolveMonad,
  debugInstantTM,
  debugSpanArgsTM,
  debugSpanTM,
  getRMContext,
  getTMAbsAddr,
  getTMCursor,
  getTMTASeg,
  getTMTree,
  goTMAbsAddrMust,
  inRemoteTM,
  inSubTM,
  modifyRMContext,
  propUpTM,
 )
import {-# SOURCE #-} Reduce.Root (handleRefRes, reduce, reduceRefCycles)
import Text.Printf (printf)
import Util (
  HasTrace (..),
 )
import Value

{- | RefSysy starts notification propagation in the tree.

The propagation is done in a breadth-first manner. It first reduces the current visiting node if needed and then
propagates to the dependents of the visiting node and the dependents of its ancestors.

The propagation starts from the current focus.
-}
startNotify :: (ReduceMonad s r m) => SCCAddr -> m ()
startNotify sccAddr = debugSpanTM "startNotify" $ do
  ctx <- getRMContext
  when (ctxIsNotifying ctx) $ throwErrSt "startNotify: already notifying"
  -- Set the context to notifying.
  modifyRMContext $ \c -> c{ctxIsNotifying = True}

  origAddr <- getTMAbsAddr
  let q = Seq.fromList [(sccAddr, False)]
  s <- get
  (r, ns) <- runStateT fetchNotifyLoop (WithBFSState (BFSState q) s)
  put (wbOther ns)
  -- Restore the original address.
  goTMAbsAddrMust origAddr
  -- Reset the context to not notifying.
  modifyRMContext $ \c -> c{ctxIsNotifying = False}
  return r

class HasBFSState s where
  getBFSState :: s -> BFSState
  setBFSState :: s -> BFSState -> s

newtype BFSState = BFSState
  { bfsQueue :: Seq.Seq (SCCAddr, Bool)
  -- ^ Queue stores ready strongly-connected components that are either reduced or ready to be reduced to notify their
  -- dependents.
  }

data WithBFSState s = WithBFSState
  { wbState :: BFSState
  , wbOther :: s
  }

instance HasBFSState (WithBFSState s) where
  getBFSState = wbState
  setBFSState s bfs = s{wbState = bfs}

instance (HasTrace s) => HasTrace (WithBFSState s) where
  getTrace s = getTrace (wbOther s)
  setTrace s trace = s{wbOther = setTrace (wbOther s) trace}

instance (HasTreeCursor s) => HasTreeCursor (WithBFSState s) where
  getTreeCursor s = getTreeCursor (wbOther s)
  setTreeCursor s cursor = s{wbOther = setTreeCursor (wbOther s) cursor}

instance (Common.HasContext s) => Common.HasContext (WithBFSState s) where
  getContext s = Common.getContext (wbOther s)
  setContext s ctx = s{wbOther = Common.setContext (wbOther s) ctx}
  modifyContext s f = s{wbOther = Common.modifyContext (wbOther s) f}

fetchNotifyLoop :: (ReduceMonad r s m, HasBFSState s) => m ()
fetchNotifyLoop = do
  state@(BFSState{bfsQueue = q}) <- gets getBFSState
  case q of
    Seq.Empty -> return ()
    ((sccAddr, toReduce) Seq.:<| xs) -> do
      debugSpanArgsTM "fetchNotifyLoop" (printf "q:%s" (show q)) $ do
        -- pop the first element of the queue.
        modify $ \s -> setBFSState s state{bfsQueue = xs}

        when toReduce $ case sccAddr of
          ACyclicSCCAddr addr -> inRemoteTM addr reduce
          CyclicSCCAddr _ -> do
            ng <- Common.ctxNotifGraph <$> getRMContext
            let addrs = getSCCAddrs sccAddr ng
            reduceRefCycles addrs
          _ -> throwErrSt $ printf "fetchNotifyLoop: unexpected SCCAddr %s" (show sccAddr)

        addDepsToQ sccAddr

      fetchNotifyLoop

{- | Add the dependents of the current SCC and its ancestors to the queue.

Adding dependents or ancestors involves either populating value to the dependents or propagating the value up.

Notice that if the current SCC is cyclic, then it will have more than one ancestor.
-}
addDepsToQ :: (ReduceMonad r s m, HasBFSState s) => SCCAddr -> m ()
addDepsToQ sccAddr = do
  addDependentsToQ sccAddr
  addAncestorsToQ sccAddr

addDependentsToQ :: (ReduceMonad r s m, HasBFSState s) => SCCAddr -> m ()
addDependentsToQ sccAddr = do
  ng <- Common.ctxNotifGraph <$> getRMContext
  populateDependents sccAddr
  let depSCCAddrs = getDependentSCCs sccAddr ng
  readySCCAddrs <- findReadySCCAddrs depSCCAddrs
  addSCCAddrsToQ $ map (,True) readySCCAddrs

populateDependents :: (ReduceMonad r s m) => SCCAddr -> m ()
populateDependents sccAddr = do
  ng <- Common.ctxNotifGraph <$> getRMContext
  pairs <- case sccAddr of
    ACyclicSCCAddr addr -> inRemoteTM addr $ do
      v <- getTMTree
      return [(addr, v)]
    CyclicSCCAddr _ -> do
      let addrs = getSCCAddrs sccAddr ng
      mapM
        ( \addr -> inRemoteTM addr $ do
            v <- getTMTree
            return (addr, v)
        )
        addrs
    _ -> throwErrSt $ printf "fetchNotifyLoop: unexpected SCCAddr %s" (show sccAddr)
  mapM_
    ( \(addr, v) -> do
        -- Fill the dependents of the given address with the source value.
        let dependents = getDependents addr ng
        debugInstantTM
          "populateDependents"
          (printf "populating dependents %s, g: %s" (show dependents) (show ng))
        mapM_
          (\dep -> inRemoteTM dep $ handleRefRes False (Just v))
          dependents
    )
    pairs

findReadySCCAddrs :: (ReduceMonad r s m) => [SCCAddr] -> m [SCCAddr]
findReadySCCAddrs sccAddrs = do
  r <-
    foldM
      ( \acc sccAddr -> do
          isReady <- checkSCCReady sccAddr
          if isReady
            then return (sccAddr : acc)
            else return acc
      )
      []
      sccAddrs
  return $ reverse r

checkSCCReady :: (ReduceMonad r s m) => SCCAddr -> m Bool
checkSCCReady sccAddr = case sccAddr of
  ACyclicSCCAddr addr -> do
    checkRemoteTreeReady addr
  CyclicSCCAddr _ -> do
    ng <- Common.ctxNotifGraph <$> getRMContext
    let addrs = getSCCAddrs sccAddr ng
    foldM
      ( \acc addr -> do
          r <- checkRemoteTreeReady addr
          return $ acc && r
      )
      True
      addrs
  _ -> throwErrSt $ printf "checkSCCReady: unexpected SCCAddr %s" (show sccAddr)

checkRemoteTreeReady :: (ReduceMonad r s m) => TreeAddr -> m Bool
checkRemoteTreeReady addr = do
  goTMAbsAddrMust addr
  tc <- getTMCursor
  checkTreeReady tc

checkTreeReady :: (ResolveMonad r s m) => TrCur -> m Bool
checkTreeReady tc = do
  (_, isReady) <-
    traverseTC
      (\x -> subNodes x ++ rawNodes x)
      ( \(x, acc) ->
          if not acc
            then return (x, acc)
            else
              return
                ( x
                , case x of
                    TCFocus (IsRef mut _) -> isJust (getMutVal mut)
                    _ -> acc
                )
      )
      (tc, True)
  return isReady

addSCCAddrsToQ :: (ReduceMonad r s m, HasBFSState s) => [(SCCAddr, Bool)] -> m ()
addSCCAddrsToQ sccAddrs = debugSpanArgsTM "addSCCAddrsToQ" (printf "sccAddrs: %s" (show sccAddrs)) $ do
  modify $ \st ->
    let bfsState = getBFSState st
        newBFSState =
          foldr
            (\e (BFSState q) -> BFSState (q Seq.|> e))
            bfsState
            sccAddrs
     in setBFSState st newBFSState

addAncestorsToQ :: (ReduceMonad r s m, HasBFSState s) => SCCAddr -> m ()
addAncestorsToQ sccAddr = do
  parSccAddrs <- getAncestorSCCAddrs sccAddr
  addSCCAddrsToQ $ map (,False) parSccAddrs

getAncestorSCCAddrs :: (ReduceMonad r s m, HasBFSState s) => SCCAddr -> m [SCCAddr]
getAncestorSCCAddrs (ACyclicSCCAddr addr) = do
  rM <- getAncSCCFromAddr addr
  return $ maybeToList rM
getAncestorSCCAddrs sccAddr@(CyclicSCCAddr _) = do
  ng <- Common.ctxNotifGraph <$> getRMContext
  r <-
    foldM
      ( \acc addr -> do
          rM <- getAncSCCFromAddr addr
          return $ maybe acc (: acc) rM
      )
      []
      (getSCCAddrs sccAddr ng)
  return $ reverse r
getAncestorSCCAddrs sccAddr = throwErrSt $ printf "getAncestorSCCAddrs: unexpected SCCAddr %s" (show sccAddr)

{- | Get the ancestor SCC address from the given address.

Since it is a tree address, there is only one ancestor for each address, meaning that the ancestor must be acyclic.
And because it is either a struct or a list.
-}
getAncSCCFromAddr :: (ReduceMonad r s m, HasBFSState s) => TreeAddr -> m (Maybe SCCAddr)
getAncSCCFromAddr addr
  | rootTreeAddr == addr = return Nothing
  | otherwise = do
      goTMAbsAddrMust addr
      propUpWithPostHandling
      curAddr <- getTMAbsAddr
      return $ Just $ ACyclicSCCAddr curAddr

propUpWithPostHandling :: (ReduceMonad r s m, HasBFSState s) => m ()
propUpWithPostHandling = do
  seg <- getTMTASeg
  debugSpanTM "propUpWithPostHandling" $ do
    propUpTM
    t <- getTMTree
    case (seg, t) of
      (BlockTASeg sseg, IsBlock _) -> do
        affected <- Nodes.handleStructMutObjChange sseg
        mapM_
          ( \name -> inSubTM (BlockTASeg (StringTASeg (TE.encodeUtf8 name))) $ do
              tc <- getTMCursor
              isReady <- checkTreeReady tc
              ng <- Common.ctxNotifGraph <$> getRMContext
              when isReady $ do
                reduce
                maybe
                  -- The affected field is not part of the notification graph.
                  (return ())
                  (\affectedFieldSccAddr -> addSCCAddrsToQ [(affectedFieldSccAddr, False)])
                  (lookupSCCAddr (tcCanAddr tc) ng)
          )
          affected
      _ -> return ()
