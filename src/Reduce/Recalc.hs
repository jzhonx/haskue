{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- | Re-calculation engine for the CUE evaluator.

When a value changes, its dependents are re-evaluated via a breadth-first
traversal of the dependency graph.  Only dependents whose inputs have
actually changed (determined by version comparisons in 'checkIfDirty')
are re-evaluated, making the process demand-driven.
-}
module Reduce.Recalc where

import Control.Monad (filterM, foldM, unless, void, when)
import Data.Aeson (ToJSON (..))
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, maybeToList)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import DepGraph
import Feature
import {-# SOURCE #-} Reduce.Core (reduce)
import Reduce.Disjunction (normalizeDisj)
import Reduce.Monad (
  RCResolver (..),
  RM,
  ReducedSignal (..),
  depGraph,
  emptyRCResolver,
  getRCResolver,
  getRMContext,
  mapRCResolver,
  modifyRMContext,
  putRMContext,
  rootRecalcQ,
 )
import Reduce.Store (fetchValFromStore, fetchValMust, propValUp, queryLastDerefedVersion, storeVal)
import Reduce.Struct (handleSObjChange, validateStructPerm, whenStruct)
import Reduce.TraceSpan (
  debugInstStr,
  emptySpanValue,
  traceSpanAdaptTM,
  traceSpanArgsTM,
  traceSpanTM,
  traceSpanTermsRepTM,
 )
import StringIndex (ShowWTIndexer (tshow))
import Text.Printf (printf)
import Util.Format (msprintfS, packFmtA)
import Value

-- | Start re-calculation by draining the root recalc queue via BFS.
recalc :: RM ()
recalc = do
  q <- rootRecalcQ <$> getRMContext
  debugInstStr
    "recalc"
    fileTopValAddr
    ( do
        qT <- tshow (toList q)
        return $ printf "starting queue: %s" qT
    )

  traceSpanTM "recalc" fileTopValAddr emptySpanValue drainQ

{- | Create a 'ReducedSignal' for the given address and enqueue it.

Does nothing if the address is not referable.
-}
sendToRootRecalcQ :: ValAddr -> RM ()
sendToRootRecalcQ addr = do
  itemM <- createReducedSignal addr
  debugInstStr
    "sendToRootRecalcQ"
    addr
    ( do
        itemMT <- tshow itemM
        return $ printf "created item: %s" itemMT
    )
  case itemM of
    Nothing -> return ()
    Just item -> modifyRMContext $ \ctx -> ctx{rootRecalcQ = rootRecalcQ ctx Seq.|> item}

{- | Create a 'ReducedSignal' for a value address, if it is referable.

Returns 'Nothing' for non-referable addresses.
-}
createReducedSignal :: ValAddr -> RM (Maybe ReducedSignal)
createReducedSignal addr = do
  case addrIsRfbAddr addr of
    Nothing -> return Nothing
    Just rfbAddr -> do
      gAddr <- vertexAddrToGrpAddr (rfbAddrToVertex rfbAddr)
      RCResolver{resolving} <- getRCResolver
      return $ Just ReducedSignal{addr, rfbAddr, grpAddr = gAddr, createdWithRCResolver = resolving}

{- | Look up the group address for a vertex in the dependency graph.

Returns an acyclic (standalone) group if not found in any existing group.
-}
vertexAddrToGrpAddr :: VertexAddr -> RM GrpAddr
vertexAddrToGrpAddr siAddr = do
  ng <- depGraph <$> getRMContext
  let r = lookupGrpAddr siAddr ng
  case r of
    Just gAddr -> return gAddr
    -- Not found in any group: the node has no deps or its dependents
    -- haven't been evaluated yet.  It cannot be part of a cycle.
    Nothing -> return $ GrpAddr (siAddr, False)

-- | Pop the next 'ReducedSignal' from the root recalc queue, or 'Nothing' if empty.
popRootRecalcQ :: RM (Maybe ReducedSignal)
popRootRecalcQ = do
  ctx <- getRMContext
  case rootRecalcQ ctx of
    Seq.Empty -> return Nothing
    (x Seq.:<| xs) -> do
      putRMContext ctx{rootRecalcQ = xs}
      return (Just x)

{- | Drain the root recalc queue, processing each 'ReducedSignal' in order.

For each popped item: if acyclic, discover dependents via 'findNeighbors';
if cyclic (SCC), build the BFS state via 'mkCyclicBFSState'.  Then run the
BFS traversal.  Loops until the queue is empty.
-}
drainQ :: RM ()
drainQ = do
  itemM <- popRootRecalcQ
  stop <- traceSpanArgsTM
    "drainQ"
    fileTopValAddr
    emptySpanValue
    ( do
        restQ <- rootRecalcQ <$> getRMContext
        itemMT <- tshow itemM
        restQT <- tshow (toList restQ)
        return $ printf "popped item: %s, restQ: %s" itemMT (show restQT)
    )
    $ case itemM of
      Nothing -> return True
      Just item -> do
        let gAddr = item.grpAddr
        next <-
          -- Acyclic: discover dependents.  Cyclic (SCC): use the item directly.
          if not (snd $ getGrpAddr gAddr)
            then findNeighbors gAddr Seq.empty
            else mkCyclicBFSState item
        unless (Seq.null next.bfsQ) $ do
          rsQT <- tshow (toList next.bfsQ)
          debugInstStr
            "drainQ"
            fileTopValAddr
            (msprintfS "new popped item: %s, bfsQ: %s" [packFmtA item, packFmtA rsQT])
          runBFS next
        return False

  unless stop drainQ

{- | Build a 'BFSState' for a cyclic (SCC) group.

If created while the RC resolver was active, discover dependents;
otherwise seed the queue with the item's group address alone.
-}
mkCyclicBFSState :: ReducedSignal -> RM BFSState
mkCyclicBFSState item = traceSpanAdaptTM
  "mkCyclicBFSState"
  item.addr
  emptySpanValue
  (const emptySpanValue)
  $ do
    g <- depGraph <$> getRMContext
    if item.createdWithRCResolver
      then findNeighbors item.grpAddr Seq.empty
      else return $ appendAddrsToBFSQ [item.grpAddr] Seq.empty g

{- | State for the breadth-first traversal of re-calculation.

@bfsQ@ holds groups still to process; @bfsQNodesSet@ is a companion set for
O(log n) duplicate detection.
-}
data BFSState = BFSState
  { bfsQ :: Seq.Seq GrpAddr
  -- ^ FIFO queue of groups to process.
  , bfsQNodesSet :: Set.Set ValAddr
  -- ^ Nodes currently in the queue, for fast dedup.
  }

{- | Run BFS re-calculation over the groups in the queue.

For each group: resolve its top reducer, recalculate, then re-lookup —
if the group address changed (e.g., a new cycle was discovered),
recalculate the updated group.  Finally discover dependents and continue.
-}
runBFS :: BFSState -> RM ()
runBFS state = case state.bfsQ of
  Seq.Empty -> return ()
  (h Seq.:<| rest) -> do
    cur <- getTopReducerGAddr h
    recalcGroup cur
    updated' <- vertexAddrToGrpAddr (fst $ getGrpAddr cur)
    -- If the group was restructured during recalculation (e.g., a new cycle
    -- discovered), recalculate the updated group.
    when (updated' /= cur) $ do
      debugInstStr
        "runBFS"
        fileTopValAddr
        ( do
            curT <- tshow cur
            updated'T <- tshow updated'
            return $ printf "current gAddr %s is updated to %s during recalculation, need to recalculate it again" curT updated'T
        )
      recalcGroup updated'
    findNeighbors updated' rest >>= runBFS

{- | Resolve the top-reducer group address for a 'GrpAddr'.

Cyclic groups reduce themselves; acyclic groups are trimmed to their top
reducer and looked up in the dependency graph.
-}
getTopReducerGAddr :: GrpAddr -> RM GrpAddr
getTopReducerGAddr gaddr
  | snd (getGrpAddr gaddr) = return gaddr -- cyclic: self-reducing
  | otherwise = do
      let nodeVertexAddr = VertexAddr $ getTopReducerAddr $ trimVertexToTopReducerAddr (fst $ getGrpAddr gaddr)
      ng <- depGraph <$> getRMContext
      case lookupGrpAddr nodeVertexAddr ng of
        Just gAddr -> return gAddr
        Nothing -> return (GrpAddr (nodeVertexAddr, False))

{- | Discover the dependent groups (\"neighbors\") of a group address and build
the next 'BFSState'.

Only groups whose values have actually changed (determined by 'filterAffectedUses') are included.
-}
findNeighbors :: GrpAddr -> Seq.Seq GrpAddr -> RM BFSState
findNeighbors cur restBFSQ = traceSpanAdaptTM
  "findNeighbors"
  fileTopValAddr
  emptySpanValue
  ( \a -> do
      nextQ <- mapM tshow (toList a.bfsQ)
      let
        msg :: String
        msg = printf "next bfsQ: %s" (show nextQ)
      return $ toJSON msg
  )
  $ do
    ng <- depGraph <$> getRMContext
    parentGrpAddrs <- getAncestorGrpAddrs cur
    let deps = cur : parentGrpAddrs
    nextGAddrs <-
      concat
        <$> mapM
          ( \dep -> do
              let depAddr = trimCanonicalToRfb (getVertexAddr $ fst $ getGrpAddr dep)
                  uses = getUseGroups dep ng
              filterAffectedUses depAddr uses
          )
          deps

    debugInstStr
      "findNeighbors"
      fileTopValAddr
      ( do
          curT <- tshow cur
          depsT <- mapM tshow deps
          nextGAddrsT <- mapM tshow nextGAddrs
          return $ printf "current gAddr: %s, deps: %s, next gAddrs: %s" curT (show depsT) (show nextGAddrsT)
      )

    let next = appendAddrsToBFSQ nextGAddrs restBFSQ ng
    return next

{- | Filter use-groups to those affected by a change to the dependency.

A group is affected if any of its member nodes are \"dirty\" — the
dependency's version differs from the last version the group observed.
-}
filterAffectedUses :: ReferableAddr -> [GrpAddr] -> RM [GrpAddr]
filterAffectedUses depAddr =
  filterM
    ( \use -> do
        useCanAddrs <- getCyclicGrpNodeAddrs use
        foldM
          ( \acc useCanAddr -> do
              dirty <- checkIfDirty depAddr useCanAddr
              return $ acc || dirty
          )
          False
          useCanAddrs
    )

{- | Check whether a use-site is \"dirty\" — the dependency's value has changed
since the last time this use-site dereferenced it.

True when the use-site is an actual dependent /and/ the version has changed.
-}
checkIfDirty :: ReferableAddr -> VertexAddr -> RM Bool
checkIfDirty depAddr useCanAddr = do
  extVal <- fetchValMust "checkIfDirty" (rfbAddrToAddr depAddr)
  lastDerefed <- queryLastDerefedVersion useCanAddr depAddr
  ng <- depGraph <$> getRMContext
  let actualUseCanAddrSet = Set.fromList (map (trimCanonicalToVertex . collapseToCanonical) $ queryUsesByDep depAddr ng)
  debugInstStr
    "checkIfDirty"
    fileTopValAddr
    ( do
        userCanAddrT <- tshow useCanAddr
        depAddrT <- tshow depAddr
        extValT <- tshow extVal
        actualUseCanAddrSetT <- mapM tshow (Set.toList actualUseCanAddrSet)
        return $
          printf
            "depAddr: %s, useAddr: %s, ext version: %d, ext val: %s, lastDerefed: %s, actualUseCanAddrSet: %s"
            depAddrT
            userCanAddrT
            extVal.version
            extValT
            (show lastDerefed)
            (show actualUseCanAddrSetT)
    )
  return $ useCanAddr `Set.member` actualUseCanAddrSet && Just extVal.version /= lastDerefed

{- | Append group addresses to the BFS queue, skipping duplicates.

Also builds the companion 'bfsQNodesSet' of all node addresses in the queue.
-}
appendAddrsToBFSQ :: [GrpAddr] -> Seq.Seq GrpAddr -> DepGraph -> BFSState
appendAddrsToBFSQ addrs restBFSQ ng =
  let
    (newQ, _) =
      foldr
        ( \x (qAcc, vAcc) ->
            if Set.member x vAcc
              then (qAcc, vAcc)
              else (qAcc Seq.|> x, Set.insert x vAcc)
        )
        (restBFSQ, Set.fromList (toList restBFSQ))
        addrs
    newQSet =
      foldr
        ( \item acc ->
            let nodes = getNodeAddrsInGrp item ng
             in foldr Set.insert acc nodes
        )
        Set.empty
        newQ
   in
    BFSState
      { bfsQ = newQ
      , bfsQNodesSet = newQSet
      }

-- | Get the vertex addresses belonging to a group (all members for SCC, single-element for acyclic).
getCyclicGrpNodeAddrs :: GrpAddr -> RM [VertexAddr]
getCyclicGrpNodeAddrs gaddr = do
  ng <- depGraph <$> getRMContext
  let compAddrs = getElemAddrInGrp gaddr ng
  return compAddrs

{- | Recalculate a group.

Acyclic: just recalc the node.
SCC: recalc each member in turn, saving results in a local map and restoring afterward (later nodes in the SCC may
overwrite earlier ones).
-}
recalcGroup :: GrpAddr -> RM ()
recalcGroup (IsAcyclicGrpAddr node) = recalcNode node
recalcGroup sccAddr = do
  -- TODO: what if the RC is a dynamic field or a constraint?
  ng <- depGraph <$> getRMContext
  -- Nodes that are structural children of others in the same SCC represent
  -- sub-field reference cycles (pruned elsewhere).
  let compAddrs = getElemAddrInGrp sccAddr ng

  traceSpanArgsTM
    "recalcCyclic"
    fileTopValAddr
    emptySpanValue
    ( do
        compAddrStrs <- mapM tshow compAddrs
        return $ printf "compAddrs: %s" (show compAddrStrs)
    )
    $ do
      store <-
        foldM
          ( \accStore siAddr -> do
              recalcRC siAddr
              -- Save immediately: later nodes in this SCC may depend on it.
              v <- fetchValMust "recalcGroup" (vertexToAddr siAddr)
              debugInstStr
                "recalcCyclic"
                fileTopValAddr
                (msprintfS "recalcCyclic %s done, fetch done, v: %s" [packFmtA siAddr, packFmtA v])
              return (Map.insert siAddr v accStore)
          )
          Map.empty
          compAddrs

      -- Restore all recalculated values and propagate upward.
      mapM_
        (\(siAddr, t) -> storeValUpToRootRecalc (vertexToAddr siAddr) t)
        (Map.toList store)

{- | Recalculate a node that is part of a reference cycle.

Sets up the RC resolver with this node on the stack, runs the stack
recalculation, then resets the resolver.
-}
recalcRC :: VertexAddr -> RM ()
recalcRC siAddr = do
  mapRCResolver (const $ RCResolver{stack = [siAddr], doneRCAddrs = [], resolving = True})
  traceSpanTM "recalcRC" (vertexToAddr siAddr) emptySpanValue recalcRCStack
  mapRCResolver (const emptyRCResolver)

{- | Process the RC resolver stack, recalculating each node in the cycle.

For each node on the stack: recalc it, then check if the stack grew
(new cycle nodes discovered).  If so, recurse immediately; otherwise
move the node to @doneRCAddrs@ and continue with the rest.
-}
recalcRCStack :: RM ()
recalcRCStack = do
  RCResolver{stack} <- getRCResolver
  case stack of
    [] -> return ()
    node : xs -> do
      recalcNode node
      RCResolver{stack = stack', doneRCAddrs} <- getRCResolver
      -- Stack grew: new cycle nodes discovered, process them immediately.
      if length stack' > length stack
        then recalcRCStack
        else do
          mapRCResolver $ \rs -> rs{stack = xs, doneRCAddrs = node : rs.doneRCAddrs}
          debugInstStr
            "recalcRCStack"
            (vertexToAddr node)
            (msprintfS "stack: %s, done: %s" [packFmtA (show xs), packFmtA (show $ node : doneRCAddrs)])
          recalcRCStack

{- | Re-reduce a single node and propagate the change upward to the root.

If the value is a struct, reducing it signals all its fields as reduced.
Safe to call on an already-reduced node (version checks prevent redundancy).
-}
recalcNode :: VertexAddr -> RM ()
recalcNode nodeVAddr = do
  let nodeAddr = vertexToAddr nodeVAddr
  vM <- fetchValFromStore "recalcNode" nodeAddr
  case vM of
    Nothing -> return ()
    Just v -> void $ traceSpanTermsRepTM "recalcNode" nodeAddr v $ do
      r <- reduce nodeAddr v
      storeValUpToRootRecalc nodeAddr r -- propagate to root
      return r

{- | Store a value and propagate changes upward to all ancestors.

At each level, disjunctions are normalized and struct permissions validated.
May enqueue new items into the root recalc queue via 'propValUp'.
-}
storeValUpToRootRecalc :: ValAddr -> VNode -> RM ()
storeValUpToRootRecalc addr v = do
  storeVal addr v
  parentM <- propValUp addr v
  case parentM of
    Nothing -> return ()
    Just (pAddr, parVN) -> do
      parVN' <- case value parVN of
        VDisj d -> normalizeDisj addr d
        _ -> handleSObjChange addr (value parVN) >>= whenStruct (validateStructPerm pAddr)
      storeValUpToRootRecalc pAddr (setVNodeValue parVN' parVN)

{- | Get ancestor group addresses of a group, nearest-ancestor first.

Acyclic: at most one parent.  SCC: collect ancestors from all members.
-}
getAncestorGrpAddrs :: GrpAddr -> RM [GrpAddr]
getAncestorGrpAddrs (IsAcyclicGrpAddr addr) = do
  let rM = getAncGrpFromAddr addr
  return $ maybeToList rM
getAncestorGrpAddrs sccAddr = do
  ng <- depGraph <$> getRMContext
  r <-
    foldM
      ( \acc addr -> do
          let rM = getAncGrpFromAddr addr
          return $ maybe acc (: acc) rM
      )
      []
      (getElemAddrInGrp sccAddr ng)
  return $ reverse r

{- | Get the parent group address of a vertex in the value tree.

Returns 'Nothing' at the root.
The parent is always acyclic since structural containment is a tree relationship.
-}
getAncGrpFromAddr :: VertexAddr -> Maybe GrpAddr
getAncGrpFromAddr raddr
  | fileTopValAddr == vertexToAddr raddr = Nothing
  | otherwise = do
      let parentAddr =
            topReducerToVertexAddr $
              fromJust $
                initTopReducer $
                  trimVertexToTopReducerAddr raddr
      return (GrpAddr (parentAddr, False))

-- | Unwrap a 'TopReducerAddr' newtype to a 'VertexAddr'.
topReducerToVertexAddr :: TopReducerAddr -> VertexAddr
topReducerToVertexAddr (TopReducerAddr c) = VertexAddr c
