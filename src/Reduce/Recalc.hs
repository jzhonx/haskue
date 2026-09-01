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
import Data.Maybe (fromMaybe, isNothing, maybeToList)
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
  throwFatal,
 )
import Reduce.Reference (descend)
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
  traceSpanTermTreeTM,
  traceSpanWithRM,
 )
import StringIndex (ShowWTIndexer (tshow))
import Text.Printf (printf)
import Util.Format (msprintfS, packFmtA)
import Value

-- | Start re-calculation by draining the root recalc queue via BFS.
recalc :: RM ()
recalc = do
  debugInstStr
    "recalc"
    fileTopEvalAddr
    ( do
        rootQueue <- rootRecalcQ <$> getRMContext
        rootQueueText <- tshow (toList rootQueue)
        return $ printf "starting queue: %s" rootQueueText
    )

  traceSpanNoPreRM "recalc" fileTopEvalAddr drainQ

{- | Create a 'ReducedSignal' for the given address and enqueue it.

Does nothing if the address cannot serve as a dependency target.
-}
sendToRootRecalcQ :: EvalAddr -> Bool -> RM ()
sendToRootRecalcQ addr depMatchByPrefix = do
  maybeSignal <- createReducedSignal addr depMatchByPrefix
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

{- | Create a 'ReducedSignal' for a value address, if it can be a dependency.

Returns 'Nothing' for addresses that cannot serve as dependency targets.
-}
createReducedSignal :: EvalAddr -> Bool -> RM (Maybe ReducedSignal)
createReducedSignal addr depMatchByPrefix = do
  case addrIsDependency addr of
    Nothing -> return Nothing
    Just dependencyAddr -> do
      group <- vertexAddrToDepGroup (dependencyToVertex dependencyAddr)
      RCResolver{resolving} <- getRCResolver
      return $ Just ReducedSignal{addr, dependencyAddr, depGroup = group, createdWithRCResolver = resolving, depMatchByPrefix}

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
          debugInstStr
            "drainQ"
            fileTopEvalAddr
            ( do
                queuedGroupTexts <- mapM (tshow . biGroup) (toList nextState.bfsQ)
                msprintfS "new popped item: %s, bfsQ: %s" [packFmtA signal, packFmtA queuedGroupTexts]
            )
          runBFS nextState
        return False

  unless queueEmpty drainQ

{- | Build the initial 'BFSState' for a 'ReducedSignal'.

Acyclic groups, and cyclic groups signaled while the reference-cycle resolver
is active, begin with their affected dependents. Other cyclic signals begin
with the signaled group itself, using that group as the source at version 0.
-}
mkBFSState :: ReducedSignal -> RM BFSState
mkBFSState signal@ReducedSignal{depGroup, depMatchByPrefix}
  | not depGroup.depGroupIsCyclic = findNeighbors signal.dependencyAddr depMatchByPrefix depGroup Seq.empty
mkBFSState signal = traceSpanWithRM
  "mkBFSState"
  signal.addr
  emptyTracePreDataRM
  (const (return (toJSON ())))
  $ do
    if signal.createdWithRCResolver
      then findNeighbors signal.dependencyAddr signal.depMatchByPrefix signal.depGroup Seq.empty
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
    let dependencyBaseAddr = trimReducedToDependency $ getVertexAddr updatedGroup.depGroupRep
    findNeighbors dependencyBaseAddr False updatedGroup remainingQueue >>= runBFS

{- | Find the vertex whose reduction owns an evaluator vertex.

Disjunct and object segments enter subtrees that are reduced as part of their
containing value rather than treated as independent top-level recalculation
units. The owning reducer is therefore the prefix before the first disjunct or
object segment. If neither segment occurs, the vertex owns its own reduction.

For example, while reducing:

@b: *{x: *{y: 1} | 2} | {}@

the physical address of @y@ is @/b/dj0/x/dj0/y@. Its owning reducer is @/b@,
because the first @dj0@ enters a disjunct owned by the reduction of @b@.
-}
owningReducerAddr :: VertexAddr -> VertexAddr
owningReducerAddr (VertexAddr (ReducedAddr addr)) =
  VertexAddr $ ReducedAddr $ trimFirstMatchToEnd isNestedReductionSegment addr
 where
  isNestedReductionSegment segment = case addrSegmentTag segment of
    ObjectTag -> True
    DisjTag -> True
    _ -> False

-- | Find the parent vertex of the vertex owning this reduction.
parentOwningReducerAddr :: VertexAddr -> Maybe VertexAddr
parentOwningReducerAddr vertexAddr = do
  parentAddr <- initEvalAddr $ vertexToAddr $ owningReducerAddr vertexAddr
  addrIsVertex parentAddr

{- | Resolve the top-reducer dependency group.

Cyclic groups reduce themselves; acyclic groups are trimmed to their top
reducer and looked up in the dependency graph.
-}
getTopReducerGroup :: DepGroupDesc -> RM DepGroupDesc
getTopReducerGroup group
  | group.depGroupIsCyclic = return group -- cyclic: self-reducing
  | otherwise = do
      let nodeVertexAddr = owningReducerAddr group.depGroupRep
      graph <- depGraph <$> getRMContext
      case lookupDepGroup nodeVertexAddr graph of
        Just resolvedGroup -> return resolvedGroup
        Nothing -> return DepGroupDesc{depGroupRep = nodeVertexAddr, depGroupIsCyclic = False}

{- | Discover the dependent groups ("neighbors") of a group and build the next 'BFSState'.

Only groups whose values have actually changed (determined by 'mkAffectedUseItems') are included.
-}
findNeighbors :: DependencyAddr -> Bool -> DepGroupDesc -> Seq.Seq BFSQItem -> RM BFSState
findNeighbors dependencyBaseAddr depMatchByPrefix currentGroup remainingQueue = traceSpanWithRM
  "findNeighbors"
  (dependencyToAddr dependencyBaseAddr)
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
    let
      directUseGroupPairs :: [DepGroupDesc] -> [(Maybe DependencyAddr, DepGroupDesc, [DepGroupDesc])]
      directUseGroupPairs groups = map (\group -> (Nothing, group, getDepGroupUses group graph)) groups

      prefixUseGroupPairs :: [(Maybe DependencyAddr, DepGroupDesc, [DepGroupDesc])]
      prefixUseGroupPairs =
        map
          (\(group, uses) -> (Just dependencyBaseAddr, group, uses))
          (getDepGroupUsesBy (isDepGroupAtOrBelow dependencyBaseAddr graph) graph)

      useGroupPairs :: [(Maybe DependencyAddr, DepGroupDesc, [DepGroupDesc])]
      useGroupPairs =
        if depMatchByPrefix
          then prefixUseGroupPairs ++ directUseGroupPairs parentGroups
          else directUseGroupPairs (currentGroup : parentGroups)
    nextItems <-
      concat
        <$> mapM
          ( \(dependencyBaseAddrM, dependencyGroup, useGroups) ->
              mkAffectedUseItems dependencyBaseAddrM dependencyGroup useGroups
          )
          useGroupPairs

    debugInstStr
      "findNeighbors"
      fileTopEvalAddr
      ( do
          dependencyBaseAddrText <- tshow dependencyBaseAddr
          currentGroupText <- tshow currentGroup
          dependencyGroupTexts <- mapM (\(_, group, _) -> tshow group) useGroupPairs
          nextGroupTexts <- mapM (tshow . biGroup) nextItems
          return $
            printf
              "dependency base: %s, current group: %s, deps: %s, next groups: %s"
              dependencyBaseAddrText
              currentGroupText
              (show dependencyGroupTexts)
              (show nextGroupTexts)
      )

    return $ appendGroupsToBFSQ nextItems remainingQueue

{- | Whether any member of a dependency group is at or below the logical
dependency base address.
-}
isDepGroupAtOrBelow :: DependencyAddr -> DepGraph -> DepGroupDesc -> Bool
isDepGroupAtOrBelow dependencyBaseAddr graph group =
  any
    (isPrefix (dependencyToAddr dependencyBaseAddr) . vertexToAddr)
    (getDepGroupMembers group graph)

{- | Collect queue items for use groups affected by a change to the dependency.

A group is affected if any of its member nodes are "dirty" — the dependency's version differs from the last version the
group observed.
-}
mkAffectedUseItems :: Maybe DependencyAddr -> DepGroupDesc -> [DepGroupDesc] -> RM [BFSQItem]
mkAffectedUseItems dependencyBaseAddrM sourceGroup candidateUseGroups = do
  graph <- depGraph <$> getRMContext
  let sourceMembers = getDepGroupMembers sourceGroup graph
  foldM
    ( \affectedItems candidateUseGroup -> do
        let memberAddrs = getDepGroupMembers candidateUseGroup graph
        affectedVersion <-
          foldM
            ( \foundVersion memberAddr -> case foundVersion of
                Just _ -> return foundVersion
                Nothing ->
                  foldM
                    ( \innerfoundVersion sourceMemberAddr -> case innerfoundVersion of
                        Just _ -> return innerfoundVersion
                        Nothing -> do
                          let dependencyAddr = trimReducedToDependency $ getVertexAddr sourceMemberAddr
                          checkIfDirty dependencyBaseAddrM dependencyAddr memberAddr
                    )
                    Nothing
                    sourceMembers
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

A 'Nothing' dependency base means that the logical dependency address is also
the base address.
-}
checkIfDirty :: Maybe DependencyAddr -> DependencyAddr -> VertexAddr -> RM (Maybe Int)
checkIfDirty dependencyBaseAddrM dependencyAddr useAddr = do
  let dependencyBaseAddr = fromMaybe dependencyAddr dependencyBaseAddrM
  dependencyNodeM <- fetchDependencyNode dependencyBaseAddr dependencyAddr
  lastDereferencedVersion <- queryLastDerefedVersion useAddr dependencyAddr
  graph <- depGraph <$> getRMContext
  let isActualUse = queryDepUseEdge dependencyAddr useAddr graph
  debugInstStr
    "checkIfDirty"
    fileTopEvalAddr
    ( do
        useAddrText <- tshow useAddr
        dependencyBaseAddrText <- tshow dependencyBaseAddr
        dependencyAddrText <- tshow dependencyAddr
        dependencyNodeMText <- tshow dependencyNodeM
        return $
          printf
            "dependencyBaseAddr: %s, dependencyAddr: %s, useAddr: %s, dependency version: %s, dependency node: %s, lastDereferencedVersion: %s, isActualUse: %s"
            dependencyBaseAddrText
            dependencyAddrText
            useAddrText
            (show $ version <$> dependencyNodeM)
            dependencyNodeMText
            (show lastDereferencedVersion)
            (show isActualUse)
    )
  if isActualUse
    && (isNothing lastDereferencedVersion || (version <$> dependencyNodeM) /= lastDereferencedVersion)
    then return (version <$> dependencyNodeM)
    else return Nothing

{- | Fetch a logical dependency relative to its base address.

When a logical dependency is not materialized in the value store, descend from
the materialized base value using the dependency's relative selectors.
-}
fetchDependencyNode :: DependencyAddr -> DependencyAddr -> RM (Maybe VNode)
fetchDependencyNode dependencyBaseAddr dependencyAddr =
  if isPrefix baseAddr logicalAddr
    then case addrToSelectors (trimPrefixAddr baseAddr logicalAddr) of
      Nothing -> fetchDirect
      Just selectors -> do
        baseNodeM <- fetchValFromStore "checkIfDirty" baseAddr
        case baseNodeM of
          Nothing -> return Nothing
          Just baseNode -> snd <$> descend baseAddr baseNode selectors
    else
      throwFatal $
        printf
          "fetchDependencyNode: dependency base address %s is not a prefix of logical dependency address %s"
          (show dependencyBaseAddr)
          (show dependencyAddr)
 where
  baseAddr = dependencyToAddr dependencyBaseAddr
  logicalAddr = dependencyToAddr dependencyAddr
  fetchDirect = fetchValFromStore "checkIfDirty" logicalAddr

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
    Just valueNode -> void $ traceSpanTermTreeTM "recalcNode" nodeAddr valueNode $ do
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
getAncestorGroupFromAddr vertexAddr = do
  parentAddr <- parentOwningReducerAddr vertexAddr
  return DepGroupDesc{depGroupRep = parentAddr, depGroupIsCyclic = False}
