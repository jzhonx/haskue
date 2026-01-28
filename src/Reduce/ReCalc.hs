{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Recalc where

import Control.Monad (foldM, unless, when)
import Control.Monad.Except
import Control.Monad.Reader (local)
import qualified Data.IntMap as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, maybeToList)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import DepGraph
import Feature
import {-# SOURCE #-} Reduce.Core (reduce)
import Reduce.Monad (
  Error (..),
  RM,
  RecalcRCFetch,
  RecalcRCResult (..),
  depGraph,
  fetch,
  getRMContext,
  getTMAbsAddr,
  getTMVal,
  goTMAbsAddr,
  goTMAbsAddrMust,
  inRemoteTM,
  isRecalcing,
  lastValueMap,
  mapParams,
  modifyRMContext,
  putRMContext,
  putTMVal,
  recalcRootQ,
  setIsReducingRC,
  setTMVN,
  throwFatal,
  withNoRecalcFlag,
 )
import Reduce.Struct (validateStructPerm)
import Reduce.TraceSpan (
  debugInstantTM,
  traceSpanArgsTM,
  traceSpanTM,
 )
import StringIndex (ShowWTIndexer (tshow))
import Text.Printf (printf)
import Util.Format (msprintf, packFmtA)
import Value
import Value.Export.Debug (treeToFullRepString)

-- | Start re-calculation.
recalc :: RM ()
recalc = do
  pushRecalcRootQ

  origAddr <- getTMAbsAddr
  ctx <- getRMContext
  -- If we are already in recalcing mode, then do not re-enter.
  -- Let drainQ handle it.
  unless (isRecalcing ctx) $ traceSpanTM "recalc" $ do
    modifyRMContext $ \c -> c{isRecalcing = True}
    drainQ
    -- Reset the context to not notifying.
    modifyRMContext $ \c -> c{isRecalcing = False}
    goTMAbsAddrMust origAddr

getRecalcGAddr :: SuffixIrredAddr -> RM (Maybe GrpAddr)
getRecalcGAddr siAddr = do
  ng <- depGraph <$> getRMContext
  case lookupGrpAddr siAddr ng of
    Just gAddr -> return $ Just gAddr
    _ -> return Nothing

-- | Push the top of the tree to the recalculation root queue.
pushRecalcRootQ :: RM ()
pushRecalcRootQ = do
  addr <- getTMAbsAddr
  case addrIsRfbAddr addr of
    Nothing -> return ()
    Just rfbAddr -> do
      lvM <- queryLastValue (rfbAddrToSufIrred rfbAddr)
      shouldPush <- case lvM of
        Nothing -> return True
        Just seen -> do
          t <- getTMVal
          repT <- treeToFullRepString t
          repSeen <- treeToFullRepString seen
          debugInstantTM
            "pushRecalcRootQ"
            (return $ T.pack $ printf "t: %s, seen: %s" repT repSeen)
          return (t /= seen)
      debugInstantTM
        "pushRecalcRootQ"
        (msprintf "addr: %s, shouldPush: %s" [packFmtA addr, packFmtA shouldPush])
      -- Only push if the value has changed.
      -- TOOD: use version.
      when shouldPush $ do
        gAddrM <- getRecalcGAddr (rfbAddrToSufIrred rfbAddr)
        case gAddrM of
          Nothing -> return ()
          Just gAddr -> modifyRMContext $ \ctx -> ctx{recalcRootQ = recalcRootQ ctx Seq.|> (addr, gAddr)}

popRecalcRootQ :: RM (Maybe (ValAddr, GrpAddr))
popRecalcRootQ = do
  ctx <- getRMContext
  case recalcRootQ ctx of
    Seq.Empty -> return Nothing
    (x Seq.:<| xs) -> do
      putRMContext ctx{recalcRootQ = xs}
      return (Just x)

drainQ :: RM ()
drainQ = do
  gAddrM <- popRecalcRootQ
  case gAddrM of
    Nothing -> return ()
    Just start@(_, gAddr) -> do
      g <- depGraph <$> getRMContext
      let qSetList = getNodeAddrsInGrp gAddr g
      debugInstantTM "drainQ" (msprintf "new popped root gAddr: %s, qSet: %s" [packFmtA gAddr, packFmtA qSetList])
      run
        ( RunState
            { startGAddr = gAddr
            , startAddr = fst start
            , q = Seq.singleton gAddr
            , qSet = Set.fromList qSetList
            , visited = Set.singleton gAddr
            }
        )
      drainQ

type ReCalcOrderState = (Set.Set SuffixIrredAddr, [GrpAddr])

{- | DNDiscRes stores ready strongly-connected components that are either reduced or ready to be reduced to notify
their dependents.
-}
data RunState = RunState
  { startGAddr :: GrpAddr
  , startAddr :: ValAddr
  , q :: Seq.Seq GrpAddr
  -- ^ The queue of GrpAddr for BFS traversal.
  , qSet :: Set.Set ValAddr
  -- ^ The set of ValAddr in the queue for quick lookup.
  , visited :: Set.Set GrpAddr
  -- ^ The set of visited GrpAddr, used to avoid re-visiting.
  }

-- | Run the recalculation list in breadth-first manner.
run :: RunState -> RM ()
run state = do
  case state.q of
    Seq.Empty -> return ()
    (cur Seq.:<| rest) -> do
      g <- depGraph <$> getRMContext
      noFieldInQ <- hasNoFieldInQ cur state.qSet
      if not noFieldInQ
        -- If there is a field of the current node in queue, we put it back to the end of the queue.
        -- The qSet remains the same since cur is still in the queue.
        then run state{q = rest Seq.|> cur}
        else do
          let curNodeIsAcyclicStart =
                cur == state.startGAddr
                  && case cur of
                    IsAcyclicGrpAddr _ -> True
                    _ -> False
          -- We do not need to recalc the starting acyclic node since it must have been reduced before recalc.
          unless curNodeIsAcyclicStart $ recalcGroup cur
          -- After recalculation, we check whether the value has changed.
          -- If not, we do not need to continue traversing its dependents. This makes sure early-cutoff.
          -- Do it here out of the
          hasSeen <- updateLastValues cur
          if hasSeen
            then run state{q = rest}
            else do
              nextState <- do
                ng <- depGraph <$> getRMContext
                parentGrpAddrs <- getAncestorGrpAddrs state.startAddr cur
                let
                  useGrpAddrs = getUseGroups cur ng
                  (newQ, newVisited) =
                    foldr
                      ( \x (qAcc, vAcc) ->
                          if Set.member x vAcc
                            then (qAcc, vAcc)
                            else (qAcc Seq.|> x, Set.insert x vAcc)
                      )
                      (rest, state.visited)
                      (useGrpAddrs ++ parentGrpAddrs)
                  restSet = foldr Set.delete state.qSet (getNodeAddrsInGrp cur g)
                  newQSet =
                    foldr
                      ( \gAddrAcc acc ->
                          let nodes = getNodeAddrsInGrp gAddrAcc ng
                           in foldr Set.insert acc nodes
                      )
                      restSet
                      useGrpAddrs
                return $
                  state
                    { q = newQ
                    , qSet = newQSet
                    , visited = newVisited
                    }

              run nextState

{- | Update the last seen values for all nodes in the group address. Return whether all nodes have the same value
as before.
-}
updateLastValues :: GrpAddr -> RM Bool
updateLastValues gaddr = do
  m <- lastValueMap <$> getRMContext
  case gaddr of
    IsAcyclicGrpAddr a -> go a m
    _ -> do
      addrs <- getCyclicGrpNodeAddrs gaddr
      foldM
        ( \acc a -> do
            r <- go a m
            return (acc && r)
        )
        True
        addrs
 where
  go siAddr m = do
    ok <- goTMAbsAddr (sufIrredToAddr siAddr)
    if ok
      then do
        t <- getTMVal
        r <- case Map.lookup siAddr m of
          Nothing -> return False
          Just lastT -> do
            return (t == lastT)
        modifyRMContext $ \ctx -> ctx{lastValueMap = Map.insert siAddr t ctx.lastValueMap}
        return r
      -- If the address does not exist, we consider it same as before.
      else return True

queryLastValue :: SuffixIrredAddr -> RM (Maybe Val)
queryLastValue siAddr = do
  m <- lastValueMap <$> getRMContext
  return $ Map.lookup siAddr m

-- | Check whether there is no fields of structs specified by the GrpAddr in the given set.
hasNoFieldInQ :: GrpAddr -> Set.Set ValAddr -> RM Bool
hasNoFieldInQ gaddr qSet = case gaddr of
  IsAcyclicGrpAddr addr -> check (sufIrredToAddr addr)
  _ -> do
    epAddrs <- getCyclicGrpNodeAddrs gaddr
    foldM
      ( \acc siAddr -> do
          r <- check (sufIrredToAddr siAddr)
          return (acc && r)
      )
      True
      epAddrs
 where
  check addr = do
    let
      baseSIAddr = trimAddrToSufIrred addr
      baseAddr = sufIrredToAddr baseSIAddr
    -- First we need to go to the base irreducible address.
    -- The base address could not exist if the node is a sub RC.
    ok <- goTMAbsAddr baseAddr
    if ok
      then do
        t <- getTMVal
        case t of
          -- If the current node is a struct, its tgen is a unify, and none of its mutable arguments is affected, then we
          -- only need to check whether the struct is ready to be used for validating its permissions.
          IsStruct struct
            | IsValMutable mut <- t
            , let
                -- If the node is an argument node, including a very deep argument in the comprehension.
                isArgChanged = addr /= baseAddr
            , Op (UOp _) <- mut
            , not isArgChanged -> do
                -- No argument affected, we can just check whether the struct is ready.
                checkSClean baseAddr qSet struct
            -- Same as above but for immutable tgen.
            | IsValImmutable <- t -> do
                checkSClean baseAddr qSet struct
          _ -> return True
      else return True

getCyclicGrpNodeAddrs :: GrpAddr -> RM [SuffixIrredAddr]
getCyclicGrpNodeAddrs gaddr = do
  ng <- depGraph <$> getRMContext
  let
    compAddrs = getElemAddrInGrp gaddr ng
    epAddrs = removeChildSIAddrs compAddrs
  return epAddrs

-- | Check whether the struct is clean if all its affected leaves are clean.
checkSClean :: ValAddr -> Set.Set ValAddr -> Struct -> RM Bool
checkSClean baseAddr qSet struct = do
  let
    affectedSufIrredAddrsSet = Set.map trimAddrToSufIrred qSet
    affectedFieldSegs =
      [ mkStringFeature name
      | name <- Map.keys (stcFields struct)
      , let a = trimAddrToSufIrred $ appendSeg baseAddr (mkStringFeature name)
      , Set.member a affectedSufIrredAddrsSet
      ]
    affectedDynSegs =
      [ mkDynFieldFeature i 0
      | i <- IntMap.keys (stcDynFields struct)
      , let
          seg = mkDynFieldFeature i 0
          a = trimAddrToSufIrred $ appendSeg baseAddr seg
         in
          Set.member a affectedSufIrredAddrsSet
      ]
    affectedCnstrSegs =
      [ mkPatternFeature i 0
      | i <- IntMap.keys (stcCnstrs struct)
      , let
          seg = mkPatternFeature i 0
          a = trimAddrToSufIrred $ appendSeg baseAddr seg
         in
          Set.member a affectedSufIrredAddrsSet
      ]
    allAffected = affectedFieldSegs ++ affectedDynSegs ++ affectedCnstrSegs
  return $ null allAffected

recalcGroup :: GrpAddr -> RM ()
recalcGroup (IsAcyclicGrpAddr node) = recalcNode node (const RsNormal)
recalcGroup sccAddr = do
  setIsReducingRC True
  -- In the intermediate steps of resolving RCs, we do not want to trigger recalculation of functions.
  -- TODO: what if the RC is a dynamic field or a constraint?
  withNoRecalcFlag True $ do
    ng <- depGraph <$> getRMContext
    -- If any node in the SCC is a child of another node in the SCC, then it should be removed as it is a sub-field
    -- reference cycle, which should be handled specially.
    let
      compAddrs = getElemAddrInGrp sccAddr ng
      epAddrs = removeChildSIAddrs compAddrs

    traceSpanArgsTM
      "recalcCyclic"
      ( const $ do
          compAddrStrs <- mapM tshow compAddrs
          epAddrStrs <- mapM tshow epAddrs
          return $ printf "compAddrs: %s, epAddrs: %s" (show compAddrStrs) (show epAddrStrs)
      )
      $ do
        store <-
          foldM
            ( \accStore siAddr -> do
                goTMAbsAddrMust (sufIrredToAddr siAddr)
                recalcRC (RCCalHelper epAddrs [siAddr] [])
                -- We have to save the recalculated value to the store since it will be overwritten when we go to the
                -- next RC node.
                v <- inRemoteTM (sufIrredToAddr siAddr) getTMVal
                debugInstantTM
                  "recalcCyclic"
                  (msprintf "recalcCyclic %s done, fetch done, v: %s" [packFmtA siAddr, packFmtA v])
                return (Map.insert siAddr v accStore)
            )
            Map.empty
            epAddrs

        -- We have to put back all the recalculated values because some of them could be overwritten during the process.
        mapM_
          (\(siAddr, t) -> inRemoteTM (sufIrredToAddr siAddr) (putTMVal t))
          (Map.toList store)

  setIsReducingRC False

data RCCalHelper = RCCalHelper
  { rcAddrs :: [SuffixIrredAddr]
  -- ^ List of addresses in the current reference cycle.
  , stack :: [SuffixIrredAddr]
  -- ^ The current stack of RC addresses being recalculated.
  , doneRCAddrs :: [SuffixIrredAddr]
  }

-- | Calculate the reference cycle node given by the top of the stack.
recalcRC :: RCCalHelper -> RM ()
recalcRC RCCalHelper{stack = []} = return ()
recalcRC h@RCCalHelper{stack = node : xs} = do
  goTMAbsAddrMust (sufIrredToAddr node)
  nodeStr <- tshow node
  traceSpanTM (printf "recalcRC %s" nodeStr) $ do
    recalcNode
      node
      ( \dep ->
          let
            -- If the dep is a sub-field of any node in the current stack, then it forms a cycle.
            depOnStack = any (\x -> isPrefix (sufIrredToAddr x) (sufIrredToAddr dep)) h.stack
            depIsDone = any (\x -> isPrefix (sufIrredToAddr x) (sufIrredToAddr dep)) h.doneRCAddrs
           in
            if
              -- OnStack must precede fetch since at the same time all cycle nodes are dirty, which would
              -- incorrectly raise error.
              | depOnStack -> RsCyclic
              -- DoneRCAddrs are still marked as dirty in the dirtSet, we have to return RsNormal to let
              -- locateRef fetch the latest value.
              | depIsDone -> RsNormal
              | otherwise -> RsDirty
      )
      `catchError` ( \case
                      DirtyDep dep -> recalcRC h{stack = dep : h.stack}
                      e -> throwError e
                   )

    debugInstantTM
      (printf "recalcRC %s" nodeStr)
      (msprintf "stack: %s, done: %s" [packFmtA (show h.stack), packFmtA (show h.doneRCAddrs)])
    recalcRC
      h{stack = xs, doneRCAddrs = node : h.doneRCAddrs}

{- | Re-calculate a single node given the dirty leaves and fetch function.

If a node is a struct and under certain conditions, we do not need to fully re-calculate it. We just need to check its
permissions.
-}
recalcNode :: SuffixIrredAddr -> RecalcRCFetch -> RM ()
recalcNode nodeSIAddr fetch = do
  -- First we need to go to the base irreducible address.
  ok <- goTMAbsAddr (sufIrredToAddr nodeSIAddr)
  when ok
    $ traceSpanArgsTM
      "recalcNode"
      ( const $ do
          addrStr <- tshow nodeSIAddr
          return $ printf "addr: %s" addrStr
      )
    $ do
      g <- depGraph <$> getRMContext
      let
        nodes = getNodeAddrsByFunc nodeSIAddr g
        anyArgChanged = any (\a -> a /= (sufIrredToAddr nodeSIAddr)) nodes
      debugInstantTM
        "recalcNode"
        (msprintf "nodes: %s, anyArgChanged: %s" [packFmtA (show nodes), packFmtA (show anyArgChanged)])
      t <- getTMVal
      case t of
        -- If the current node is a struct, its tgen is a unify, and none of its mutable arguments is affected, then we
        -- only need to check whether the struct is ready to be used for validating its permissions.
        IsStruct _
          | IsValMutable mut <- t
          , Op (UOp _) <- mut
          , -- No argument affected, we can just check whether the struct is ready.
            not anyArgChanged ->
              validateStructPerm
          -- Same as above but for immutable tgen.
          | IsValImmutable <- t -> validateStructPerm
        -- For mutable, list, disjunction, just re-calculate it.
        _ -> do
          local (mapParams (\p -> p{fetch})) do
            -- invalidateUpToRootMut baseAddr dirtyLeaves
            reduce

{- | Because reduce is a top-down process, we need to invalidate all mutable ancestors up to the root mutable.

TODO: seems like all segments should be mutables, because we are like lazy evaluating the tree.
-}
invalidateUpToRootMut :: ValAddr -> Set.Set ValAddr -> RM ()
invalidateUpToRootMut base addrSet = go (filter (isPrefix base) (Set.toList addrSet)) Set.empty
 where
  go [] _ = return ()
  go (addr : rest) done
    | addr `elem` done = go rest done
    -- Stop when we reach above the base address. The base address itself can be a reference.
    | isPrefix addr base && addr /= base = return ()
    | otherwise = do
        goTMAbsAddrMust addr
        t <- getTMVal
        case t of
          IsValMutable (Op _) -> setTMVN VNNoVal
          -- TODO: what if the intermediate value is not mutable? How to invalidate then?
          _ -> throwFatal $ printf "expected mutable node at address %s during invalidation" (show addr)
        let parentAddr = fromJust $ initValAddr addr
        go (parentAddr : rest) (Set.insert addr done)

{- | Get the ancestor GrpAddrs of the given GrpAddr.

It handles the case that the cyclic group may contain structural cycles.
-}
getAncestorGrpAddrs :: ValAddr -> GrpAddr -> RM [GrpAddr]
getAncestorGrpAddrs startAddr (IsAcyclicGrpAddr addr) = do
  let rM = getAncGrpFromAddr startAddr addr
  return $ maybeToList rM
getAncestorGrpAddrs startAddr sccAddr = do
  ng <- depGraph <$> getRMContext
  r <-
    foldM
      ( \acc addr -> do
          let rM = getAncGrpFromAddr startAddr addr
          return $ maybe acc (: acc) rM
      )
      []
      (removeChildSIAddrs $ getElemAddrInGrp sccAddr ng)
  return $ reverse r

{- | Get the ancestor SCC address from the given address.

Since it is a tree address, there is only one ancestor for each address, meaning that the ancestor must be acyclic.
And because it is either a struct or a list.
-}
getAncGrpFromAddr :: ValAddr -> SuffixIrredAddr -> Maybe GrpAddr
getAncGrpFromAddr startAddr raddr
  | rootValAddr == sufIrredToAddr raddr = Nothing
  | otherwise = do
      let parentAddr = fromJust $ initSufIrred raddr
      -- We should not add the ancestors that are above the starting address of the notification.
      -- The new parent should not be a starting address either.
      if isPrefix (sufIrredToAddr parentAddr) startAddr
        then Nothing
        else Just (GrpAddr (parentAddr, False))
