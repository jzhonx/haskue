{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}

module DepGraph where

import Control.DeepSeq (NFData)
import Control.Monad (forM_, when)
import Control.Monad.State.Strict (MonadState (..), State, evalState, execState, gets, modify')
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import EvalAddr
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)

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
          (\(depVertex, useVertices) -> (getVertexAddrFromVIDMust (getVertex depVertex) graph.vidMapping, useVertices))
          (HashMap.toList $ vUsesByDep graph.vgraph)
    depTexts <-
      mapM
        ( \(depAddr, useVertices) -> do
            depAddrText <- tshow depAddr
            useAddrTexts <- mapM (\useVertex -> tshow $ getVertexAddrFromVtxMust useVertex graph.vidMapping) useVertices
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

-- | A propagation-graph vertex representing an irreducible address.
newtype Vertex = Vertex {getVertex :: Int} deriving (Eq, Ord, Hashable, Generic, NFData)

instance Show Vertex where
  show (Vertex vertexID) = "v_" ++ show vertexID
instance ShowWTIndexer Vertex

-- | Bidirectional mapping between graph vertex IDs and value-store vertex addresses.
data VIDMapping = VIDMapping
  { vidToAddr :: HashMap.HashMap Int VertexAddr
  , addrToVid :: HashMap.HashMap VertexAddr Int
  , nextVid :: Int
  }
  deriving (Eq, Generic, NFData)

getVID :: VertexAddr -> VIDMapping -> (Int, Maybe VIDMapping)
getVID vertexAddr mapping =
  case lookupVID vertexAddr mapping of
    Just vertexID -> (vertexID, Nothing)
    Nothing ->
      let vertexID = nextVid mapping
          newVidToAddr = HashMap.insert vertexID vertexAddr (vidToAddr mapping)
          newAddrToVid = HashMap.insert vertexAddr vertexID (addrToVid mapping)
       in ( vertexID
          , Just $
              VIDMapping
                { vidToAddr = newVidToAddr
                , addrToVid = newAddrToVid
                , nextVid = vertexID + 1
                }
          )

-- | Look up the ID already assigned to a vertex address.
lookupVID :: VertexAddr -> VIDMapping -> Maybe Int
lookupVID vertexAddr mapping = HashMap.lookup vertexAddr mapping.addrToVid

getVertexAddrFromVIDMust :: (HasCallStack) => Int -> VIDMapping -> VertexAddr
getVertexAddrFromVIDMust vertexID mapping = case HashMap.lookup vertexID (vidToAddr mapping) of
  Just vertexAddr -> vertexAddr
  Nothing -> error $ printf "VID %d not found in VIDMapping" vertexID

getVertexAddrFromVtxMust :: (HasCallStack) => Vertex -> VIDMapping -> VertexAddr
getVertexAddrFromVtxMust vertex = getVertexAddrFromVIDMust (getVertex vertex)

defaultVIDMapping :: VIDMapping
defaultVIDMapping =
  VIDMapping
    { vidToAddr = HashMap.fromList [(rootVID, fileTopVertexAddr)]
    , addrToVid = HashMap.fromList [(fileTopVertexAddr, rootVID)]
    , nextVid = rootVID + 1
    }

rootVID :: Int
rootVID = 0

liftGetVIDForG :: VertexAddr -> State DepGraph Int
liftGetVIDForG vertexAddr = state $ \graph ->
  let (vertexID, maybeMapping) = getVID vertexAddr graph.vidMapping
   in case maybeMapping of
        Just mapping -> (vertexID, graph{vidMapping = mapping})
        Nothing -> (vertexID, graph)

-- Vertex-level propagation graph

{- | The vertex-level propagation graph.

This is the uncollapsed graph from which 'CGraph' is derived.  An edge
@dependency -> use@ records that a change to the dependency may require the use
to be recalculated.  Only vertices corresponding to referable addresses may be
keys in 'vUsesByDep'; dependent uses may be any irreducible expression address.

The adjacency map alone does not describe the complete vertex universe, since
a vertex need not have outgoing edges.  'vVertices' therefore records every
edge endpoint separately for SCC discovery.  Removing edges does not remove
vertices from this set.
-}
data VGraph = VGraph
  { vUsesByDep :: HashMap.HashMap Vertex [Vertex]
  -- ^ Maps each referable dependency vertex to its dependent vertices.
  , vVertices :: Set.Set Vertex
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

The dependency vertex must correspond to a referable address.  Both endpoints
are added to 'vVertices'.
-}
insertVGraphEdge :: Vertex -> Vertex -> VGraph -> VGraph
insertVGraphEdge depVertex useVertex vertexGraph =
  vertexGraph
    { vUsesByDep = insertHMUnique depVertex useVertex vertexGraph.vUsesByDep
    , vVertices = Set.union (Set.fromList [depVertex, useVertex]) vertexGraph.vVertices
    }

-- | Delete all edges that have the given vertex by matching the use vertex with the given predicate.
delVGEdgeByUseMatch :: (Vertex -> Bool) -> VGraph -> VGraph
delVGEdgeByUseMatch useMatch vertexGraph =
  vertexGraph
    { vUsesByDep = HashMap.map (filter (not . useMatch)) vertexGraph.vUsesByDep
    }

queryVGUsesByDepMatch :: (Vertex -> Bool) -> VGraph -> [(Vertex, Vertex)]
queryVGUsesByDepMatch depMatches vertexGraph =
  let matchingEntries = filter (depMatches . fst) (HashMap.toList vertexGraph.vUsesByDep)
   in concatMap
        (\(depVertex, useVertices) -> map (\useVertex -> (depVertex, useVertex)) useVertices)
        matchingEntries

-- Component graph

{- | The condensation graph of 'VGraph'.

Each strongly connected component (SCC) of the propagation graph is collapsed
to one representative 'Vertex'.  Edges between those representatives form
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
  { cgUsesByDep :: HashMap.HashMap Vertex [Vertex]
  -- ^ Propagation edges between SCC representatives, from a dependency to its dependent uses.
  , repToComps :: HashMap.HashMap Vertex (Set.Set Vertex, Bool)
  -- ^ Maps each SCC representative to its member vertices and cyclic flag.
  , compToRep :: HashMap.HashMap Vertex (Vertex, Bool)
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
getOrCreateRepVtx :: Vertex -> CGraph -> (Vertex, CGraph)
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
hasPathInCG :: Vertex -> Vertex -> DepGraph -> Bool
hasPathInCG fromVertex toVertex graph = dfs fromVertex Set.empty
 where
  dfs :: Vertex -> Set.Set Vertex -> Bool
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
  Nothing -> []
  Just (memberVertices, _) -> map (`getVertexAddrFromVtxMust` graph.vidMapping) (Set.toList memberVertices)
 where
  groupMembers = do
    repID <- lookupVID group.depGroupRep graph.vidMapping
    HashMap.lookup (Vertex repID) graph.cgraph.repToComps

-- | Get the dependency groups that use a given group.
getDepGroupUses :: DepGroupDesc -> DepGraph -> [DepGroupDesc]
getDepGroupUses group graph = case lookupVID group.depGroupRep graph.vidMapping of
  Nothing -> []
  Just repID -> case HashMap.lookup (Vertex repID) graph.cgraph.cgUsesByDep of
    Nothing -> []
    Just useReps ->
      mapMaybe (`lookupDepGroupByVertex` graph) useReps

-- | Look up the dependency group containing a graph vertex.
lookupDepGroupByVertex :: Vertex -> DepGraph -> Maybe DepGroupDesc
lookupDepGroupByVertex vertex graph = do
  (repVertex, isCyclic) <- HashMap.lookup vertex graph.cgraph.compToRep
  return
    DepGroupDesc
      { depGroupRep = getVertexAddrFromVtxMust repVertex graph.vidMapping
      , depGroupIsCyclic = isCyclic
      }

-- | Look up the dependency group containing a vertex address.
lookupDepGroup :: VertexAddr -> DepGraph -> Maybe DepGroupDesc
lookupDepGroup vertexAddr graph = do
  vertexID <- lookupVID vertexAddr graph.vidMapping
  lookupDepGroupByVertex (Vertex vertexID) graph

-- Dependency operations

{- | Add a new dependency to the propagation graph and update the component graph.

The dependency is represented as an edge from the dependency address (dep) to the dependent address (use).

- The use address does not need to be referable.
- The dep address will later notify the dependent address if it changes. It should be a referable address.

Some cases:

1. sub-field RC: x: x.f. Resolving "x.f.g" gets dependency relationships: /x/f/g -> /x/f, /x/f -> /x.
    From the x -> x.f.g we get /x -> /x/f/g. So we have a cycle, which contains /x, /x/f, /x/f/g.
-}
addNewDepToNG :: (HasCallStack) => EvalAddr -> ReferableAddr -> DepGraph -> DepGraph
addNewDepToNG useAddr depAddr =
  execState
    ( do
        let
          depVertexAddr = rfbAddrToVertex depAddr
          useVertexAddr = trimCanonicalToVertex $ collapseToCanonical useAddr
        depVertexID <- liftGetVIDForG depVertexAddr
        useVertexID <- liftGetVIDForG useVertexAddr
        let useVertex = Vertex useVertexID
            depVertex = Vertex depVertexID
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
  useMatchAdapt :: VIDMapping -> Vertex -> Bool
  useMatchAdapt mapping useVertex = useMatch (vertexToAddr $ getVertexAddrFromVtxMust useVertex mapping)

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
                ( vertexToAddr $ getVertexAddrFromVtxMust depVertex mapping
                , vertexToAddr $ getVertexAddrFromVtxMust useVertex mapping
                )
            )
            matchingEdges
    )
 where
  adaptDepMatch :: VIDMapping -> Vertex -> Bool
  adaptDepMatch mapping depVertex =
    depMatches (vertexToAddr $ getVertexAddrFromVtxMust depVertex mapping)

queryUsesByDep :: (HasCallStack) => ReferableAddr -> DepGraph -> [EvalAddr]
queryUsesByDep depAddr graph = map snd $ queryUsesByDepMatch (== rfbAddrToAddr depAddr) graph

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
  { tsUsesByDep :: HashMap.HashMap Vertex [Vertex]
  , tsIndex :: !Int
  , tsStack :: [Vertex]
  , tsMetaMap :: HashMap.HashMap Vertex TarjanNodeMeta
  , tsSCCs :: [SCC]
  }

emptyTarjanState :: HashMap.HashMap Vertex [Vertex] -> [Vertex] -> TarjanState
emptyTarjanState usesByDep vertices =
  TarjanState
    { tsUsesByDep = usesByDep
    , tsIndex = 0
    , tsStack = []
    , tsMetaMap = HashMap.fromList $ map (\vertex -> (vertex, emptyTarjanNodeMeta)) vertices
    , tsSCCs = []
    }

data SCC
  = AcyclicSCC Vertex
  | CyclicSCC [Vertex]
  deriving (Show)

scc :: (HasCallStack) => HashMap.HashMap Vertex [Vertex] -> Set.Set Vertex -> TarjanState
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
sccDFS :: (HasCallStack) => Vertex -> State TarjanState ()
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

getNeighbors :: Vertex -> State TarjanState [Vertex]
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
