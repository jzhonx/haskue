{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}

module DepGraph (
  -- * Graph addresses
  VertexAddr (..),
  fileTopVertexAddr,
  trimReducedToVertex,
  vertexToAddr,
  addrIsVertex,
  dependencyToVertex,

  -- * Dependency graph
  DepGraph,
  emptyDepGraph,

  -- * Dependency groups
  DepGroupDesc (..),
  pattern IsAcyclicDepGroup,
  pattern IsCyclicDepGroup,
  getDepGroupMembers,
  getDepGroupUses,
  getDepGroupUsesBy,
  lookupDepGroup,

  -- * Dependency operations
  addNewDepToNG,
  delDGEdgesByUseMatch,
  queryUsesByDepMatch,
  queryDepUseEdge,
)
where

import Control.DeepSeq (NFData)
import Control.Monad (forM_, when)
import Control.Monad.State.Strict (MonadState (..), State, evalState, execState, gets, modify')
import Data.Aeson (ToJSON)
import Data.Aeson.Types (ToJSONKey)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable (..))
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Vector as V
import EvalAddr
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer)
import Text.Printf (printf)

-- Graph addresses

{- | A non-empty reduced address identifying a dependency-graph vertex.

A vertex address may contain disjunct segments, but it cannot end with one. A
terminal disjunct segment selects a value owned by its parent vertex rather
than a separate propagation vertex. For example, @/b/dj0@ is not a vertex
address, while @/b/dj0/x@ is one because it ends at the field @x@.

Every 'DependencyAddr' is a vertex address, but a vertex may end with an
internal reduced segment that cannot be a dependency target.

'addrIsVertex' checks the invariant without changing the address, while
'trimReducedToVertex' removes trailing non-vertex segments to select the
nearest containing vertex.
-}
newtype VertexAddr = VertexAddr {getVertexAddr :: ReducedAddr}
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (NFData, ToJSON, ToJSONWTIndexer, ToJSONKey)

instance ShowWTIndexer VertexAddr where
  tshow (VertexAddr addr) = tshow addr

instance Hashable VertexAddr where
  hashWithSalt salt (VertexAddr (ReducedAddr addr)) = hashWithSalt salt addr

-- | The file root represented as a dependency-graph vertex.
fileTopVertexAddr :: VertexAddr
fileTopVertexAddr = VertexAddr (ReducedAddr fileTopEvalAddr)

isSegmentVertex :: AddrSegment -> Bool
isSegmentVertex segment = case addrSegmentTag segment of
  DisjTag -> False
  _ -> isSegmentReduced segment

trimReducedToVertex :: ReducedAddr -> VertexAddr
trimReducedToVertex (ReducedAddr (EvalAddr segments)) =
  let reversedSegments = V.reverse segments
      vertexSegments = V.dropWhile (not . isSegmentVertex) reversedSegments
   in VertexAddr (ReducedAddr (EvalAddr $ V.reverse vertexSegments))

vertexToAddr :: VertexAddr -> EvalAddr
vertexToAddr (VertexAddr reducedAddr) = getReducedAddr reducedAddr

addrIsVertex :: EvalAddr -> Maybe VertexAddr
addrIsVertex addr = do
  reducedAddr <- addrIsReduced addr
  finalSegment <- lastSeg (getReducedAddr reducedAddr)
  if isSegmentVertex finalSegment
    then return $ VertexAddr reducedAddr
    else Nothing

-- | Every dependency address is also a vertex address.
dependencyToVertex :: DependencyAddr -> VertexAddr
dependencyToVertex (DependencyAddr reducedAddr) = VertexAddr reducedAddr

-- Dependency graph

data DepGraph = DepGraph
  { vgraph :: VGraph
  , cgraph :: CGraph
  -- ^ The component graph representing the strongly connected components (SCCs) of the propagation graph.
  , vidMapping :: VIDMapping
  }
  deriving (Eq, Generic, NFData)

instance Show DepGraph where
  show graph = printf "G(Deps: %s)" (show $ vUsesByDep graph.vgraph)

instance ShowWTIndexer DepGraph where
  tshow graph = do
    let
      depEntries =
        map
          (\(depVertexID, useVertexIDs) -> (getVertexAddrFromVIDMust depVertexID graph.vidMapping, useVertexIDs))
          (HashMap.toList $ vUsesByDep graph.vgraph)
    depTexts <-
      mapM
        ( \(depAddr, useVertexIDs) -> do
            depAddrText <- tshow depAddr
            useAddrTexts <- mapM (\useVertexID -> tshow $ getVertexAddrFromVIDMust useVertexID graph.vidMapping) useVertexIDs
            return $ T.pack $ printf "%s: %s" (T.unpack depAddrText) (show useAddrTexts)
        )
        depEntries
    return $ T.pack $ printf "G(Deps: %s)" (show depTexts)

mapVGraph :: (VGraph -> VGraph) -> DepGraph -> DepGraph
mapVGraph transform graph = graph{vgraph = transform graph.vgraph}

mapCGraph :: (CGraph -> CGraph) -> DepGraph -> DepGraph
mapCGraph transform graph = graph{cgraph = transform graph.cgraph}

emptyDepGraph :: DepGraph
emptyDepGraph =
  DepGraph
    { vgraph = emptyVGraph
    , cgraph = emptyCGraph
    , vidMapping = defaultVIDMapping
    }

-- Vertex identity

-- | The integer identity of a propagation-graph vertex.
newtype VertexID = VertexID {getVertexID :: Int} deriving (Eq, Ord, Hashable, Generic, NFData)

instance Show VertexID where
  show (VertexID vertexID) = "v_" ++ show vertexID
instance ShowWTIndexer VertexID

-- | Bidirectional mapping between graph vertex IDs and value-store vertex addresses.
data VIDMapping = VIDMapping
  { vidToAddr :: HashMap.HashMap VertexID VertexAddr
  , addrToVid :: HashMap.HashMap VertexAddr VertexID
  , nextVID :: VertexID
  }
  deriving (Eq, Generic, NFData)

getVID :: VertexAddr -> VIDMapping -> (VertexID, Maybe VIDMapping)
getVID vertexAddr mapping =
  case lookupVID vertexAddr mapping of
    Just vertexID -> (vertexID, Nothing)
    Nothing ->
      let vertexID = nextVID mapping
          newVidToAddr = HashMap.insert vertexID vertexAddr (vidToAddr mapping)
          newAddrToVid = HashMap.insert vertexAddr vertexID (addrToVid mapping)
       in ( vertexID
          , Just $
              VIDMapping
                { vidToAddr = newVidToAddr
                , addrToVid = newAddrToVid
                , nextVID = VertexID (getVertexID vertexID + 1)
                }
          )

-- | Look up the ID already assigned to a vertex address.
lookupVID :: VertexAddr -> VIDMapping -> Maybe VertexID
lookupVID vertexAddr mapping = HashMap.lookup vertexAddr mapping.addrToVid

getVertexAddrFromVIDMust :: (HasCallStack) => VertexID -> VIDMapping -> VertexAddr
getVertexAddrFromVIDMust vertexID mapping = case HashMap.lookup vertexID (vidToAddr mapping) of
  Just vertexAddr -> vertexAddr
  Nothing -> error $ printf "VID %d not found in VIDMapping" (getVertexID vertexID)

defaultVIDMapping :: VIDMapping
defaultVIDMapping =
  VIDMapping
    { vidToAddr = HashMap.fromList [(rootVID, fileTopVertexAddr)]
    , addrToVid = HashMap.fromList [(fileTopVertexAddr, rootVID)]
    , nextVID = VertexID (getVertexID rootVID + 1)
    }

rootVID :: VertexID
rootVID = VertexID 0

liftGetVIDForG :: VertexAddr -> State DepGraph VertexID
liftGetVIDForG vertexAddr = state $ \graph ->
  let (vertexID, maybeMapping) = getVID vertexAddr graph.vidMapping
   in case maybeMapping of
        Just mapping -> (vertexID, graph{vidMapping = mapping})
        Nothing -> (vertexID, graph)

-- Vertex-level propagation graph

{- | The vertex-level propagation graph.

This is the uncollapsed graph from which 'CGraph' is derived.  An edge
@dependency -> use@ records that a change to the dependency may require the use
to be recalculated. Only vertices corresponding to dependency addresses may be
keys in 'vUsesByDep'; dependent uses may be any irreducible expression address.

The adjacency map alone does not describe the complete vertex universe, since
a vertex need not have outgoing edges.  'vVertices' therefore records every
edge endpoint separately for SCC discovery.  Removing edges does not remove
vertices from this set.
-}
data VGraph = VGraph
  { vUsesByDep :: HashMap.HashMap VertexID [VertexID]
  -- ^ Maps each dependency vertex to its dependent vertices.
  , vVertices :: Set.Set VertexID
  -- ^ All vertices known to the graph, including vertices with no outgoing edges.
  }
  deriving (Eq, Generic, NFData)

emptyVGraph :: VGraph
emptyVGraph =
  VGraph
    { vUsesByDep = HashMap.empty
    , vVertices = Set.empty
    }

{- | Insert a propagation edge from a dependency to a dependent use.

The dependency vertex must correspond to a dependency address. Both endpoints
are added to 'vVertices'.
-}
insertVGraphEdge :: VertexID -> VertexID -> VGraph -> VGraph
insertVGraphEdge depVertex useVertex vertexGraph =
  vertexGraph
    { vUsesByDep = insertHMUnique depVertex useVertex vertexGraph.vUsesByDep
    , vVertices = Set.union (Set.fromList [depVertex, useVertex]) vertexGraph.vVertices
    }

-- | Delete all edges that have the given vertex by matching the use vertex with the given predicate.
delVGEdgeByUseMatch :: (VertexID -> Bool) -> VGraph -> VGraph
delVGEdgeByUseMatch useMatch vertexGraph =
  vertexGraph
    { vUsesByDep = HashMap.map (filter (not . useMatch)) vertexGraph.vUsesByDep
    }

queryVGUsesByDepMatch :: (VertexID -> Bool) -> VGraph -> [(VertexID, VertexID)]
queryVGUsesByDepMatch depMatches vertexGraph =
  let matchingEntries = filter (depMatches . fst) (HashMap.toList vertexGraph.vUsesByDep)
   in concatMap
        (\(depVertex, useVertices) -> map (\useVertex -> (depVertex, useVertex)) useVertices)
        matchingEntries

-- Component graph

{- | The condensation graph of 'VGraph'.

Each strongly connected component (SCC) of the propagation graph is collapsed
to one representative 'VertexID'. Edges between those representatives form
a DAG and retain the propagation direction: an edge @dependency -> use@ means
that a change in the dependency may require recalculating the use.  The choice
of representative is an implementation detail and may change when the graph is
rebuilt.

The component membership is indexed in both directions to support the graph's
main lookup patterns.  The maps must satisfy these invariants:

* Every vertex in 'compToRep' occurs in exactly one component in 'repToComps'.
* Every key in 'repToComps' is the representative stored for all members of
  that component, including itself.
* The cyclic flag is identical in both indexes and is 'True' exactly for a
  cyclic SCC (a multi-vertex SCC or a singleton with a self-cycle).
* Every key and value in 'cgUsesByDep' is an SCC representative, and
  'cgUsesByDep' has no intra-component edges.
-}
data CGraph = CGraph
  { cgUsesByDep :: HashMap.HashMap VertexID [VertexID]
  -- ^ Propagation edges between SCC representatives, from a dependency to its dependent uses.
  , repToComps :: HashMap.HashMap VertexID (Set.Set VertexID, Bool)
  -- ^ Maps each SCC representative to its member vertices and cyclic flag.
  , compToRep :: HashMap.HashMap VertexID (VertexID, Bool)
  -- ^ Reverse index from each vertex to its SCC representative and cyclic flag.
  }
  deriving (Eq, Generic, NFData)

emptyCGraph :: CGraph
emptyCGraph =
  CGraph
    { cgUsesByDep = HashMap.empty
    , repToComps = HashMap.empty
    , compToRep = HashMap.empty
    }

{- | Get the representative vertex of a given vertex in the component graph.

If the vertex is not found in the compToRep map, it means it is not yet added to the graph, so we create a new entry for
it.
-}
getOrCreateRepVtx :: VertexID -> CGraph -> (VertexID, CGraph)
getOrCreateRepVtx vertex componentGraph = case HashMap.lookup vertex componentGraph.compToRep of
  Just (rep, _) -> (rep, componentGraph)
  Nothing ->
    ( vertex
    , componentGraph
        { compToRep = HashMap.insert vertex (vertex, False) componentGraph.compToRep
        , repToComps = HashMap.insert vertex (Set.singleton vertex, False) componentGraph.repToComps
        }
    )

{- | Check if there is a path from one vertex to another in the component graph.

If from and to are the same, return True.
-}
hasPathInCG :: VertexID -> VertexID -> DepGraph -> Bool
hasPathInCG fromVertex toVertex graph = dfs fromVertex Set.empty
 where
  dfs :: VertexID -> Set.Set VertexID -> Bool
  dfs currentVertex visitedVertices
    | currentVertex == toVertex = True
    | Set.member currentVertex visitedVertices = False
    | otherwise =
        let neighbors = HashMap.findWithDefault [] currentVertex graph.cgraph.cgUsesByDep
            updatedVisited = Set.insert currentVertex visitedVertices
         in any (\neighbor -> dfs neighbor updatedVisited) neighbors

-- Dependency groups

{- | A compact description of a dependency group.

Membership is resolved against the current 'DepGraph' rather than stored here,
so the description remains lightweight for queues and map keys.
-}
data DepGroupDesc = DepGroupDesc
  { depGroupRep :: !VertexAddr
  -- ^ Representative vertex address used to identify the group.
  , depGroupIsCyclic :: !Bool
  -- ^ Whether the group must be recalculated as a reference cycle.
  }
  deriving (Eq, Ord, Generic, NFData)

instance Show DepGroupDesc where
  show DepGroupDesc{depGroupRep = repAddr, depGroupIsCyclic = isCyclic} =
    if isCyclic
      then "Cyclic " ++ show repAddr
      else show repAddr

instance ShowWTIndexer DepGroupDesc where
  tshow DepGroupDesc{depGroupRep = repAddr, depGroupIsCyclic = isCyclic} = do
    addrText <- tshow repAddr
    let cyclicText = if isCyclic then "Cyclic " else ""
    return $ cyclicText <> addrText

pattern IsAcyclicDepGroup :: VertexAddr -> DepGroupDesc
pattern IsAcyclicDepGroup vertexAddr <- DepGroupDesc vertexAddr False

pattern IsCyclicDepGroup :: VertexAddr -> DepGroupDesc
pattern IsCyclicDepGroup vertexAddr <- DepGroupDesc vertexAddr True

-- | Get the current member addresses of a dependency group.
getDepGroupMembers :: DepGroupDesc -> DepGraph -> [VertexAddr]
getDepGroupMembers group graph = case groupMembers of
  Nothing -> [group.depGroupRep]
  Just (memberVertexIDs, _) -> map (`getVertexAddrFromVIDMust` graph.vidMapping) (Set.toList memberVertexIDs)
 where
  groupMembers = do
    repID <- lookupVID group.depGroupRep graph.vidMapping
    HashMap.lookup repID graph.cgraph.repToComps

-- | Get the dependency groups that use a given group.
getDepGroupUses :: DepGroupDesc -> DepGraph -> [DepGroupDesc]
getDepGroupUses group graph = case lookupVID group.depGroupRep graph.vidMapping of
  Nothing -> []
  Just repID -> case HashMap.lookup repID graph.cgraph.cgUsesByDep of
    Nothing -> []
    Just useReps ->
      mapMaybe (`lookupDepGroupByVertexID` graph) useReps

{- | Get the direct use groups of every dependency group matching a predicate.

Only dependency groups with outgoing edges are considered. Result order follows
the component graph's internal hash map and is not stable.
-}
getDepGroupUsesBy :: (DepGroupDesc -> Bool) -> DepGraph -> [(DepGroupDesc, [DepGroupDesc])]
getDepGroupUsesBy matches graph =
  mapMaybe matchingUses (HashMap.toList graph.cgraph.cgUsesByDep)
 where
  matchingUses (depRep, useReps) = do
    depGroup <- lookupDepGroupByVertexID depRep graph
    if matches depGroup
      then return (depGroup, mapMaybe (`lookupDepGroupByVertexID` graph) useReps)
      else Nothing

-- | Look up the dependency group containing a graph vertex.
lookupDepGroupByVertexID :: VertexID -> DepGraph -> Maybe DepGroupDesc
lookupDepGroupByVertexID vertexID graph = do
  (repVertexID, isCyclic) <- HashMap.lookup vertexID graph.cgraph.compToRep
  return
    DepGroupDesc
      { depGroupRep = getVertexAddrFromVIDMust repVertexID graph.vidMapping
      , depGroupIsCyclic = isCyclic
      }

-- | Look up the dependency group containing a vertex address.
lookupDepGroup :: VertexAddr -> DepGraph -> Maybe DepGroupDesc
lookupDepGroup vertexAddr graph = do
  vertexID <- lookupVID vertexAddr graph.vidMapping
  lookupDepGroupByVertexID vertexID graph

-- Dependency operations

{- | Add a new dependency to the propagation graph and update the component graph.

The dependency is represented as an edge from the dependency address (dep) to the dependent address (use).

- The use address does not need to be a dependency address.
- The dep address will later notify the dependent address if it changes. It must be a dependency address.

Some cases:

1. sub-field RC: x: x.f. Resolving "x.f.g" gets dependency relationships: /x/f/g -> /x/f, /x/f -> /x.
    From the x -> x.f.g we get /x -> /x/f/g. So we have a cycle, which contains /x, /x/f, /x/f/g.
-}
addNewDepToNG :: (HasCallStack) => EvalAddr -> DependencyAddr -> DepGraph -> DepGraph
addNewDepToNG useAddr depAddr =
  execState
    ( do
        let
          depVertexAddr = dependencyToVertex depAddr
          useVertexAddr = trimReducedToVertex $ toReducedAddr useAddr
        depVertexID <- liftGetVIDForG depVertexAddr
        useVertexID <- liftGetVIDForG useVertexAddr
        let useVertex = useVertexID
            depVertex = depVertexID
        modify' $
          mapVGraph $
            insertVGraphEdge depVertex useVertex
        depRep <- state (getOrCreateGraphRep depVertex)
        useRep <- state (getOrCreateGraphRep useVertex)

        graph <- get
        if
          -- If both addresses are in the same SCC, do nothing.
          | depRep == useRep -> return ()
          -- If there is no edge from useRep to depRep in the component graph, meaning there is no cycle formed, we
          -- can simply add the depRep -> useRep edge to the component graph.
          | not (hasPathInCG useRep depRep graph) -> do
              let updatedUsesByDep = insertHMUnique depRep useRep graph.cgraph.cgUsesByDep
              modify' $ mapCGraph (\componentGraph -> componentGraph{cgUsesByDep = updatedUsesByDep})
          -- The new edge forms a cycle in the component graph, we need to recompute the component graph.
          | otherwise -> modify' updateCGraph
    )
 where
  getOrCreateGraphRep vertex graph =
    let (rep, updatedCGraph) = getOrCreateRepVtx vertex graph.cgraph
     in (rep, graph{cgraph = updatedCGraph})

-- | Remove all edges from the dependency graph that match the given predicate on the use vertex.
delDGEdgesByUseMatch :: (HasCallStack) => (EvalAddr -> Bool) -> DepGraph -> DepGraph
delDGEdgesByUseMatch useMatch =
  execState
    ( do
        mapping <- gets vidMapping
        modify' $ \graph -> updateCGraph (mapVGraph (delVGEdgeByUseMatch (useMatchAdapt mapping)) graph)
    )
 where
  useMatchAdapt :: VIDMapping -> VertexID -> Bool
  useMatchAdapt mapping useVertexID = useMatch (vertexToAddr $ getVertexAddrFromVIDMust useVertexID mapping)

{- | Query the dependents by matching the use vertex with the given predicate.

It returns a list of (dependency, use) pairs that match the predicate.
-}
queryUsesByDepMatch :: (HasCallStack) => (EvalAddr -> Bool) -> DepGraph -> [(EvalAddr, EvalAddr)]
queryUsesByDepMatch depMatches =
  evalState
    ( do
        mapping <- gets vidMapping
        vertexGraph <- gets vgraph
        let matchingEdges = queryVGUsesByDepMatch (adaptDepMatch mapping) vertexGraph
        return $
          map
            ( \(depVertex, useVertex) ->
                ( vertexToAddr $ getVertexAddrFromVIDMust depVertex mapping
                , vertexToAddr $ getVertexAddrFromVIDMust useVertex mapping
                )
            )
            matchingEdges
    )
 where
  adaptDepMatch :: VIDMapping -> VertexID -> Bool
  adaptDepMatch mapping depVertex =
    depMatches (vertexToAddr $ getVertexAddrFromVIDMust depVertex mapping)

{- | Test whether the vertex-level propagation graph contains the exact edge
@dependency -> use@.

Both endpoints are resolved through 'VIDMapping' without allocating vertex
IDs. The use address must already be normalized to the 'VertexAddr' form stored
by 'addNewDepToNG'. The result is 'False' if either endpoint is unknown.

This performs two average-case constant-time hash lookups followed by a linear
search through the dependency's direct-use list.
-}
queryDepUseEdge :: DependencyAddr -> VertexAddr -> DepGraph -> Bool
queryDepUseEdge depAddr useAddr graph = case do
  depVID <- lookupVID (dependencyToVertex depAddr) graph.vidMapping
  useVID <- lookupVID useAddr graph.vidMapping
  return (depVID, useVID) of
  Nothing -> False
  Just (depVID, useVID) ->
    useVID `elem` HashMap.findWithDefault [] depVID graph.vgraph.vUsesByDep

-- Component graph rebuilding

-- | Update the component graph based on the current propagation graph.
updateCGraph :: (HasCallStack) => DepGraph -> DepGraph
updateCGraph graph =
  graph
    { cgraph =
        CGraph
          { cgUsesByDep = newUsesByDepRep
          , repToComps = newMembersByRep
          , compToRep = newRepByMember
          }
    }
 where
  tarjanState = scc graph.vgraph.vUsesByDep graph.vgraph.vVertices
  newMembersByRep =
    foldr
      ( \component membersByRep -> case component of
          AcyclicSCC vertex -> HashMap.insert vertex (Set.singleton vertex, False) membersByRep
          -- Use the first member vertex as the component representative.
          CyclicSCC memberVertices -> HashMap.insert (head memberVertices) (Set.fromList memberVertices, True) membersByRep
      )
      HashMap.empty
      tarjanState.tsSCCs
  newRepByMember =
    HashMap.foldrWithKey
      ( \rep (memberVertices, isCyclic) repByMember ->
          foldr
            (\memberVertex updatedRepByMember -> HashMap.insert memberVertex (rep, isCyclic) updatedRepByMember)
            repByMember
            (Set.toList memberVertices)
      )
      HashMap.empty
      newMembersByRep
  -- Convert the vertex-level dependency-to-use edges to SCC-level edges.
  -- Dependencies in the same SCC share a representative, so merge their uses
  -- and discard edges whose dependency and use belong to the same SCC.
  newUsesByDepRep =
    HashMap.map Set.toList $
      HashMap.foldrWithKey
        ( \depVertex useVertices usesByDepRep ->
            let (depRep, _) = newRepByMember `lookupMust` depVertex
                useReps = Set.fromList $ map (\useVertex -> fst $ newRepByMember `lookupMust` useVertex) useVertices
                externalUseReps = Set.delete depRep useReps
             in HashMap.insertWith Set.union depRep externalUseReps usesByDepRep
        )
        HashMap.empty
        graph.vgraph.vUsesByDep

-- Tarjan SCC decomposition

data NeighborType
  = RegularNeighbor
  | -- | RCNeighbor means the neighbor is added through a child-to-parent edge.
    --     If later it turns out that there is no cycle formed through this edge, meaning there is no path from the neighbor
    --     back to the original node, this edge can be ignored.
    RCNeighbor
  deriving (Eq, Show)

data TarjanNodeMeta = TarjanNodeMeta
  { dnmLowLink :: !Int
  , dnmIndex :: !Int
  , dnmOnStack :: !Bool
  , dnmNType :: !NeighborType
  }
  deriving (Show)

emptyTarjanNodeMeta :: TarjanNodeMeta
emptyTarjanNodeMeta = TarjanNodeMeta 0 0 False RegularNeighbor

data TarjanState = TarjanState
  { tsUsesByDep :: HashMap.HashMap VertexID [VertexID]
  , tsIndex :: !Int
  , tsStack :: [VertexID]
  , tsMetaMap :: HashMap.HashMap VertexID TarjanNodeMeta
  , tsSCCs :: [SCC]
  }

emptyTarjanState :: HashMap.HashMap VertexID [VertexID] -> [VertexID] -> TarjanState
emptyTarjanState usesByDep vertices =
  TarjanState
    { tsUsesByDep = usesByDep
    , tsIndex = 0
    , tsStack = []
    , tsMetaMap = HashMap.fromList $ map (\vertex -> (vertex, emptyTarjanNodeMeta)) vertices
    , tsSCCs = []
    }

data SCC
  = AcyclicSCC VertexID
  | CyclicSCC [VertexID]
  deriving (Show)

scc :: (HasCallStack) => HashMap.HashMap VertexID [VertexID] -> Set.Set VertexID -> TarjanState
scc usesByDep vertices = execState go initialState
 where
  initialState = emptyTarjanState usesByDep (Set.toList vertices)

  go :: (HasCallStack) => State TarjanState ()
  go = do
    forM_ vertices $ \vertex -> do
      vertexIndex <- gets $ \tarjanState -> dnmIndex $ tarjanState.tsMetaMap `lookupMust` vertex
      when (vertexIndex == 0) $
        sccDFS vertex

-- | Perform a depth-first search to find strongly connected components (SCCs) using Tarjan's algorithm.
sccDFS :: (HasCallStack) => VertexID -> State TarjanState ()
sccDFS vertex = do
  modify' $ \tarjanState ->
    let nextIndex = tarjanState.tsIndex + 1
        vertexMeta =
          TarjanNodeMeta
            { dnmLowLink = nextIndex
            , dnmIndex = nextIndex
            , dnmOnStack = True
            , dnmNType = RegularNeighbor
            }
     in tarjanState
          { tsIndex = nextIndex
          , tsStack = vertex : tarjanState.tsStack
          , tsMetaMap = HashMap.insert vertex vertexMeta tarjanState.tsMetaMap
          }
  neighbors <- getNeighbors vertex
  forM_ neighbors $ \neighbor -> do
    -- If the current node finds itself as a neighbor, mark it as a RCNeighbor.
    when (neighbor `elem` neighbors) $ modify' $ \tarjanState ->
      let metaMap = tarjanState.tsMetaMap
          neighborMeta = metaMap `lookupMust` neighbor
          updatedNeighborMeta = neighborMeta{dnmNType = RCNeighbor}
       in tarjanState{tsMetaMap = HashMap.insert neighbor updatedNeighborMeta metaMap}

    neighborVisited <-
      gets (\tarjanState -> (\metadata -> dnmIndex metadata /= 0) $ tarjanState.tsMetaMap `lookupMust` neighbor)
    neighborOnStack <- gets (\tarjanState -> dnmOnStack $ tarjanState.tsMetaMap `lookupMust` neighbor)
    if
      | not neighborVisited -> do
          sccDFS neighbor
          modify' $ \tarjanState ->
            let metaMap = tarjanState.tsMetaMap
                vertexLowLink = dnmLowLink $ metaMap `lookupMust` vertex
                neighborLowLink = dnmLowLink $ metaMap `lookupMust` neighbor
             in tarjanState
                  { tsMetaMap =
                      HashMap.adjust (\metadata -> metadata{dnmLowLink = min vertexLowLink neighborLowLink}) vertex metaMap
                  }
      | neighborOnStack -> modify' $ \tarjanState ->
          let metaMap = tarjanState.tsMetaMap
              vertexLowLink = dnmLowLink $ metaMap `lookupMust` vertex
              neighborIndex = dnmIndex $ metaMap `lookupMust` neighbor
           in tarjanState
                { tsMetaMap = HashMap.adjust (\metadata -> metadata{dnmLowLink = min vertexLowLink neighborIndex}) vertex metaMap
                }
      | otherwise -> return ()

  isComponentRoot <- gets $ \tarjanState ->
    let vertexMeta = tarjanState.tsMetaMap `lookupMust` vertex
     in dnmLowLink vertexMeta == dnmIndex vertexMeta
  when isComponentRoot $ do
    modify' $ \tarjanState ->
      let (verticesBeforeRoot, stackFromRoot) = span (/= vertex) tarjanState.tsStack
          remainingStack = tail stackFromRoot
          componentVertices = vertex : verticesBeforeRoot
          component =
            if dnmNType (tarjanState.tsMetaMap `lookupMust` vertex) == RCNeighbor
              then CyclicSCC componentVertices
              else AcyclicSCC vertex
          updatedMetaMap =
            foldr
              ( \memberVertex metaMap ->
                  -- Mark all nodes in the SCC as not on stack.
                  HashMap.adjust (\metadata -> metadata{dnmOnStack = False}) memberVertex metaMap
              )
              tarjanState.tsMetaMap
              componentVertices
       in tarjanState
            { tsStack = remainingStack
            , tsMetaMap = updatedMetaMap
            , tsSCCs = component : tarjanState.tsSCCs
            }

getNeighbors :: VertexID -> State TarjanState [VertexID]
getNeighbors vertex = gets (HashMap.findWithDefault [] vertex . tsUsesByDep)

-- Collection helpers

lookupMust :: (HasCallStack, Show k, Show a, Hashable k) => HashMap.HashMap k a -> k -> a
lookupMust hashMap key = case HashMap.lookup key hashMap of
  Just value -> value
  Nothing -> error $ printf "key %s not found in map %s" (show key) (show hashMap)

insertHMUnique :: (Eq k, Hashable k, Eq a) => k -> a -> HashMap.HashMap k [a] -> HashMap.HashMap k [a]
insertHMUnique key value =
  HashMap.insertWith
    (\_ oldValues -> if value `elem` oldValues then oldValues else value : oldValues)
    key
    [value]
