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

import Control.Monad (foldM, unless, void, when)
import Data.Aeson (ToJSON (..))
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, maybeToList)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import DepGraph
import EvalAddr
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
  emptyTracePreData,
  emptyTracePreDataRM,
  markFlowEventEnd,
  tpvArgs,
  traceSpanNoPreRM,
  traceSpanRM,
  traceSpanTermsRepTM,
  traceSpanWithRM,
 )
import StringIndex (ShowWTIndexer (tshow))
import Text.Printf (printf)
import Util.Format (msprintfS, packFmtA)
import Value

-- | Start re-calculation by draining the root recalc queue via BFS.
recalc :: RM ()
recalc = do
  rootQueue <- rootRecalcQ <$> getRMContext
  debugInstStr
    "recalc"
    fileTopEvalAddr
    ( do
        rootQueueText <- tshow (toList rootQueue)
        return $ printf "starting queue: %s" rootQueueText
    )

  traceSpanNoPreRM "recalc" fileTopEvalAddr drainQ

{- | Create a 'ReducedSignal' for the given address and enqueue it.

Does nothing if the address is not referable.
-}
sendToRootRecalcQ :: EvalAddr -> RM ()
sendToRootRecalcQ addr = do
  maybeSignal <- createReducedSignal addr
  debugInstStr
    "sendToRootRecalcQ"
    addr
    ( do
        maybeSignalText <- tshow maybeSignal
        return $ printf "created item: %s" maybeSignalText
    )
  case maybeSignal of
    Nothing -> return ()
    Just signal -> modifyRMContext $ \context -> context{rootRecalcQ = rootRecalcQ context Seq.|> signal}

{- | Create a 'ReducedSignal' for a value address, if it is referable.

Returns 'Nothing' for non-referable addresses.
-}
createReducedSignal :: EvalAddr -> RM (Maybe ReducedSignal)
createReducedSignal addr = do
  case addrIsRfbAddr addr of
    Nothing -> return Nothing
    Just rfbAddr -> do
      group <- vertexAddrToDepGroup (rfbAddrToVertex rfbAddr)
      RCResolver{resolving} <- getRCResolver
      return $ Just ReducedSignal{addr, rfbAddr, depGroup = group, createdWithRCResolver = resolving}

{- | Look up the group description for a vertex in the dependency graph.

Returns an acyclic (standalone) group if not found in any existing group.
-}
vertexAddrToDepGroup :: VertexAddr -> RM DepGroupDesc
vertexAddrToDepGroup vertexAddr = do
  graph <- depGraph <$> getRMContext
  let maybeGroup = lookupDepGroup vertexAddr graph
  case maybeGroup of
    Just group -> return group
    -- Not found in any group: the node has no deps or its dependents
    -- haven't been evaluated yet.  It cannot be part of a cycle.
    Nothing -> return $ DepGroupDesc{depGroupRep = vertexAddr, depGroupIsCyclic = False}

-- | Pop the next 'ReducedSignal' from the root recalc queue, or 'Nothing' if empty.
popRootRecalcQ :: RM (Maybe ReducedSignal)
popRootRecalcQ = do
  context <- getRMContext
  case rootRecalcQ context of
    Seq.Empty -> return Nothing
    (signal Seq.:<| remainingQueue) -> do
      putRMContext context{rootRecalcQ = remainingQueue}
      return (Just signal)

{- | Drain the root recalc queue, processing each 'ReducedSignal' in order.

For each popped signal, build its initial state with 'mkBFSState' and run the
BFS traversal. Loops until the queue is empty.
-}
drainQ :: RM ()
drainQ = do
  maybeSignal <- popRootRecalcQ
  queueEmpty <- traceSpanRM
    "drainQ"
    fileTopEvalAddr
    ( do
        remainingRootQueue <- rootRecalcQ <$> getRMContext
        maybeSignalText <- tshow maybeSignal
        remainingRootQueueText <- tshow (toList remainingRootQueue)
        return $
          emptyTracePreData{tpvArgs = Just $ printf "popped item: %s, restQ: %s" maybeSignalText (show remainingRootQueueText)}
    )
    $ case maybeSignal of
      Nothing -> return True
      Just signal -> do
        nextState <- mkBFSState signal
        unless (Seq.null nextState.bfsQ) $ do
          queuedGroupTexts <- mapM (tshow . biGroup) (toList nextState.bfsQ)
          debugInstStr
            "drainQ"
            fileTopEvalAddr
            (msprintfS "new popped item: %s, bfsQ: %s" [packFmtA signal, packFmtA queuedGroupTexts])
          runBFS nextState
        return False

  unless queueEmpty drainQ

{- | Build the initial 'BFSState' for a 'ReducedSignal'.

Acyclic groups, and cyclic groups signaled while the reference-cycle resolver
is active, begin with their affected dependents. Other cyclic signals begin
with the signaled group itself, using that group as the source at version 0.
-}
mkBFSState :: ReducedSignal -> RM BFSState
mkBFSState ReducedSignal{depGroup}
  | not depGroup.depGroupIsCyclic = findNeighbors depGroup Seq.empty
mkBFSState signal = traceSpanWithRM
  "mkBFSState"
  signal.addr
  emptyTracePreDataRM
  (const (return (toJSON ())))
  $ do
    if signal.createdWithRCResolver
      then findNeighbors signal.depGroup Seq.empty
      else
        return $
          appendGroupsToBFSQ
            [ BFSQItem
                { biSourceGroup = signal.depGroup -- set to the group itself since no one caused the recalculation.
                , biSourceVersion = 0
                , biGroup = signal.depGroup
                }
            ]
            Seq.empty

{- | State for the breadth-first traversal of re-calculation.

@bfsQ@ holds groups still to process.
-}
data BFSState = BFSState
  { bfsQ :: Seq.Seq BFSQItem
  -- ^ FIFO queue of groups to process.
  --   Each item records the source group and version that triggered the recalculation.
  }

data BFSQItem = BFSQItem
  { biSourceGroup :: DepGroupDesc
  , biSourceVersion :: Int
  -- ^ For now, the version is the first version of the source group that triggered the recalculation.
  , biGroup :: DepGroupDesc
  }
  deriving (Eq, Ord, Show)

{- | Run BFS re-calculation over the groups in the queue.

For each group: resolve its top reducer, recalculate, then re-lookup —
if the group description changed (e.g., a new cycle was discovered),
recalculate the updated group.  Finally discover dependents and continue.
-}
runBFS :: BFSState -> RM ()
runBFS bfsState = case bfsState.bfsQ of
  Seq.Empty -> return ()
  (queueItem Seq.:<| remainingQueue) -> do
    currentGroup <- getTopReducerGroup queueItem.biGroup
    recalcGroup queueItem{biGroup = currentGroup}
    updatedGroup <- vertexAddrToDepGroup currentGroup.depGroupRep
    -- If the group was restructured during recalculation (e.g., a new cycle discovered), recalculate the updated group.
    when (updatedGroup /= currentGroup) $ do
      debugInstStr
        "runBFS"
        fileTopEvalAddr
        ( do
            currentGroupText <- tshow currentGroup
            updatedGroupText <- tshow updatedGroup
            return $
              printf
                "current group %s is updated to %s during recalculation, need to recalculate it again"
                currentGroupText
                updatedGroupText
        )
      recalcGroup queueItem{biGroup = updatedGroup}
    findNeighbors updatedGroup remainingQueue >>= runBFS

{- | Resolve the top-reducer dependency group.

Cyclic groups reduce themselves; acyclic groups are trimmed to their top
reducer and looked up in the dependency graph.
-}
getTopReducerGroup :: DepGroupDesc -> RM DepGroupDesc
getTopReducerGroup group
  | group.depGroupIsCyclic = return group -- cyclic: self-reducing
  | otherwise = do
      let nodeVertexAddr = VertexAddr $ getTopReducerAddr $ trimVertexToTopReducerAddr group.depGroupRep
      graph <- depGraph <$> getRMContext
      case lookupDepGroup nodeVertexAddr graph of
        Just resolvedGroup -> return resolvedGroup
        Nothing -> return DepGroupDesc{depGroupRep = nodeVertexAddr, depGroupIsCyclic = False}

{- | Discover the dependent groups ("neighbors") of a group and build
the next 'BFSState'.

Only groups whose values have actually changed (determined by 'mkAffectedUseItems') are included.
-}
findNeighbors :: DepGroupDesc -> Seq.Seq BFSQItem -> RM BFSState
findNeighbors currentGroup remainingQueue = traceSpanWithRM
  "findNeighbors"
  fileTopEvalAddr
  emptyTracePreDataRM
  ( \bfsState -> do
      queuedGroupTexts <- mapM (tshow . biGroup) (toList bfsState.bfsQ)
      let
        msg :: String
        msg = printf "next bfsQ: %s" (show queuedGroupTexts)
      return $ toJSON msg
  )
  $ do
    graph <- depGraph <$> getRMContext
    parentGroups <- getAncestorGroups currentGroup
    let dependencyGroups = currentGroup : parentGroups
    nextItems <-
      concat
        <$> mapM
          ( \dependencyGroup -> do
              let dependencyAddr = trimCanonicalToRfb (getVertexAddr dependencyGroup.depGroupRep)
                  useGroups = getDepGroupUses dependencyGroup graph
              mkAffectedUseItems dependencyGroup dependencyAddr useGroups
          )
          dependencyGroups

    debugInstStr
      "findNeighbors"
      fileTopEvalAddr
      ( do
          currentGroupText <- tshow currentGroup
          dependencyGroupTexts <- mapM tshow dependencyGroups
          nextGroupTexts <- mapM (tshow . biGroup) nextItems
          return $
            printf "current group: %s, deps: %s, next groups: %s" currentGroupText (show dependencyGroupTexts) (show nextGroupTexts)
      )

    return $ appendGroupsToBFSQ nextItems remainingQueue

{- | Collect queue items for use groups affected by a change to the dependency.

A group is affected if any of its member nodes are "dirty" — the dependency's version differs from the last version the
group observed.
-}
mkAffectedUseItems :: DepGroupDesc -> ReferableAddr -> [DepGroupDesc] -> RM [BFSQItem]
mkAffectedUseItems sourceGroup dependencyAddr candidateUseGroups = do
  graph <- depGraph <$> getRMContext
  foldM
    ( \affectedItems candidateUseGroup -> do
        let memberAddrs = getDepGroupMembers candidateUseGroup graph
        affectedVersion <-
          foldM
            ( \foundVersion memberAddr -> case foundVersion of
                Just _ -> return foundVersion
                Nothing -> checkIfDirty dependencyAddr memberAddr
            )
            Nothing
            memberAddrs
        case affectedVersion of
          Just version ->
            return $ BFSQItem{biSourceGroup = sourceGroup, biSourceVersion = version, biGroup = candidateUseGroup} : affectedItems
          Nothing -> return affectedItems
    )
    []
    candidateUseGroups

{- | Check whether a use-site is "dirty" — the dependency's value has changed
since the last time this use-site dereferenced it.

True when the use-site is an actual dependent /and/ the version has changed.
-}
checkIfDirty :: ReferableAddr -> VertexAddr -> RM (Maybe Int)
checkIfDirty dependencyAddr useAddr = do
  dependencyNode <- fetchValMust "checkIfDirty" (rfbAddrToAddr dependencyAddr)
  lastDereferencedVersion <- queryLastDerefedVersion useAddr dependencyAddr
  graph <- depGraph <$> getRMContext
  let actualUseAddrs = Set.fromList (map (trimCanonicalToVertex . collapseToCanonical) $ queryUsesByDep dependencyAddr graph)
  debugInstStr
    "checkIfDirty"
    fileTopEvalAddr
    ( do
        useAddrText <- tshow useAddr
        dependencyAddrText <- tshow dependencyAddr
        dependencyNodeText <- tshow dependencyNode
        actualUseAddrTexts <- mapM tshow (Set.toList actualUseAddrs)
        return $
          printf
            "dependencyAddr: %s, useAddr: %s, dependency version: %d, dependency node: %s, lastDereferencedVersion: %s, actualUseAddrs: %s"
            dependencyAddrText
            useAddrText
            dependencyNode.version
            dependencyNodeText
            (show lastDereferencedVersion)
            (show actualUseAddrTexts)
    )
  if useAddr `Set.member` actualUseAddrs && Just dependencyNode.version /= lastDereferencedVersion
    then return $ Just dependencyNode.version
    else return Nothing

-- | Append groups to the BFS queue, skipping duplicates.
appendGroupsToBFSQ :: [BFSQItem] -> Seq.Seq BFSQItem -> BFSState
appendGroupsToBFSQ items remainingQueue =
  let
    (newQueue, _) =
      foldr
        ( \item (queue, seenItems) ->
            if Set.member item seenItems
              then (queue, seenItems)
              else (queue Seq.|> item, Set.insert item seenItems)
        )
        (remainingQueue, Set.fromList (toList remainingQueue))
        items
   in
    BFSState
      { bfsQ = newQueue
      }

{- | Recalculate a group.

Acyclic: just recalc the node.
SCC: recalc each member in turn, saving results in a local map and restoring afterward (later nodes in the SCC may
overwrite earlier ones).
-}
recalcGroup :: BFSQItem -> RM ()
recalcGroup BFSQItem{biSourceGroup, biSourceVersion, biGroup = IsAcyclicDepGroup nodeVertexAddr} =
  recalcNode biSourceGroup biSourceVersion nodeVertexAddr
recalcGroup BFSQItem{biSourceGroup, biSourceVersion, biGroup} = do
  -- TODO: what if the RC is a dynamic field or a constraint?
  graph <- depGraph <$> getRMContext
  -- Nodes that are structural children of others in the same SCC represent
  -- sub-field reference cycles (pruned elsewhere).
  let memberAddrs = getDepGroupMembers biGroup graph

  traceSpanRM
    "recalcCyclic"
    fileTopEvalAddr
    ( do
        memberAddrTexts <- mapM tshow memberAddrs
        return $ emptyTracePreData{tpvArgs = Just $ printf "memberAddrs: %s" (show memberAddrTexts)}
    )
    $ do
      valuesByAddr <-
        foldM
          ( \storedValues memberAddr -> do
              recalcRC biSourceGroup biSourceVersion memberAddr
              -- Save immediately: later nodes in this SCC may depend on it.
              valueNode <- fetchValMust "recalcGroup" (vertexToAddr memberAddr)
              debugInstStr
                "recalcCyclic"
                fileTopEvalAddr
                (msprintfS "recalcCyclic %s done, fetch done, v: %s" [packFmtA memberAddr, packFmtA valueNode])
              return (Map.insert memberAddr valueNode storedValues)
          )
          Map.empty
          memberAddrs

      -- Restore all recalculated values and propagate upward.
      mapM_
        (\(memberAddr, valueNode) -> storeValUpToRootRecalc (vertexToAddr memberAddr) valueNode)
        (Map.toList valuesByAddr)

{- | Recalculate a node that is part of a reference cycle.

Sets up the RC resolver with this node on the stack, runs the stack
recalculation, then resets the resolver.
-}
recalcRC :: DepGroupDesc -> Int -> VertexAddr -> RM ()
recalcRC sourceGroup sourceVersion vertexAddr = do
  mapRCResolver (const $ RCResolver{stack = [vertexAddr], doneRCAddrs = [], resolving = True})
  traceSpanNoPreRM "recalcRC" (vertexToAddr vertexAddr) (recalcRCStack sourceGroup sourceVersion)
  mapRCResolver (const emptyRCResolver)

{- | Process the RC resolver stack, recalculating each node in the cycle.

For each node on the stack: recalc it, then check if the stack grew
(new cycle nodes discovered).  If so, recurse immediately; otherwise
move the node to @doneRCAddrs@ and continue with the rest.
-}
recalcRCStack :: DepGroupDesc -> Int -> RM ()
recalcRCStack sourceGroup sourceVersion = do
  RCResolver{stack} <- getRCResolver
  case stack of
    [] -> return ()
    nodeAddr : remainingStack -> do
      recalcNode sourceGroup sourceVersion nodeAddr
      RCResolver{stack = updatedStack, doneRCAddrs} <- getRCResolver
      -- Stack grew: new cycle nodes discovered, process them immediately.
      if length updatedStack > length stack
        then recalcRCStack sourceGroup sourceVersion
        else do
          mapRCResolver $ \resolver -> resolver{stack = remainingStack, doneRCAddrs = nodeAddr : resolver.doneRCAddrs}
          debugInstStr
            "recalcRCStack"
            (vertexToAddr nodeAddr)
            (msprintfS "stack: %s, done: %s" [packFmtA (show remainingStack), packFmtA (show $ nodeAddr : doneRCAddrs)])
          recalcRCStack sourceGroup sourceVersion

{- | Re-reduce a single node and propagate the change upward to the root.

If the value is a struct, reducing it signals all its fields as reduced.
Safe to call on an already-reduced node (version checks prevent redundancy).
-}
recalcNode :: DepGroupDesc -> Int -> VertexAddr -> RM ()
recalcNode sourceGroup sourceVersion nodeVertexAddr = do
  let nodeAddr = vertexToAddr nodeVertexAddr
  maybeValueNode <- fetchValFromStore "recalcNode" nodeAddr
  case maybeValueNode of
    Nothing -> return ()
    Just valueNode -> void $ traceSpanTermsRepTM "recalcNode" nodeAddr valueNode $ do
      markFlowEventEnd sourceGroup sourceVersion
      reducedNode <- reduce nodeAddr valueNode
      storeValUpToRootRecalc nodeAddr reducedNode -- propagate to root
      return reducedNode

{- | Store a value and propagate changes upward to all ancestors.

At each level, disjunctions are normalized and struct permissions validated.
May enqueue new items into the root recalc queue via 'propValUp'.
-}
storeValUpToRootRecalc :: EvalAddr -> VNode -> RM ()
storeValUpToRootRecalc valueAddr valueNode = do
  storeVal valueAddr valueNode
  maybeParent <- propValUp valueAddr valueNode
  case maybeParent of
    Nothing -> return ()
    Just (parentAddr, parentNode) -> do
      parentValue <- case value parentNode of
        VDisj disjunction -> normalizeDisj valueAddr disjunction
        _ -> handleSObjChange valueAddr (value parentNode) >>= whenStruct (validateStructPerm parentAddr)
      storeValUpToRootRecalc parentAddr (setVNodeValue parentValue parentNode)

{- | Get ancestor groups of a group, nearest-ancestor first.

Acyclic: at most one parent.  SCC: collect ancestors from all members.
-}
getAncestorGroups :: DepGroupDesc -> RM [DepGroupDesc]
getAncestorGroups (IsAcyclicDepGroup vertexAddr) = do
  let maybeAncestorGroup = getAncestorGroupFromAddr vertexAddr
  return $ maybeToList maybeAncestorGroup
getAncestorGroups group = do
  graph <- depGraph <$> getRMContext
  ancestorGroups <-
    foldM
      ( \groups memberAddr -> do
          let maybeAncestorGroup = getAncestorGroupFromAddr memberAddr
          return $ maybe groups (: groups) maybeAncestorGroup
      )
      []
      (getDepGroupMembers group graph)
  return $ reverse ancestorGroups

{- | Get the parent group of a vertex in the value tree.

Returns 'Nothing' at the root.
The parent is always acyclic since structural containment is a tree relationship.
-}
getAncestorGroupFromAddr :: VertexAddr -> Maybe DepGroupDesc
getAncestorGroupFromAddr vertexAddr
  | fileTopEvalAddr == vertexToAddr vertexAddr = Nothing
  | otherwise = do
      let parentAddr =
            topReducerToVertexAddr $
              fromJust $
                initTopReducer $
                  trimVertexToTopReducerAddr vertexAddr
      return DepGroupDesc{depGroupRep = parentAddr, depGroupIsCyclic = False}

-- | Unwrap a 'TopReducerAddr' newtype to a 'VertexAddr'.
topReducerToVertexAddr :: TopReducerAddr -> VertexAddr
topReducerToVertexAddr (TopReducerAddr canonicalAddr) = VertexAddr canonicalAddr
