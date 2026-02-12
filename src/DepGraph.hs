{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}

module DepGraph where

import Control.DeepSeq (NFData)
import Control.Monad (forM_, when)
import Control.Monad.State.Strict (MonadState (..), State, evalState, execState, gets, modify', runState)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Vector as V
import Debug.Trace
import Feature
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)

data DepGraph = DepGraph
  { nodesByUseFunc :: Map.Map SuffixIrredAddr [ValAddr]
  -- ^ Groups lists of dependent vertex IDs by their function addresses.
  -- If the function does not have an argument, it maps to itself.
  -- For example, /a -> [/a/fa0, /a/fa1] if /a/fa0 and /a/fa1 are dependents.
  -- Or /a -> [/a] if /a is a reference.
  , vgraph :: VGraph
  , cgraph :: CGraph
  -- ^ The component graph representing the strongly connected components (SCCs) of the propagation graph.
  , vidMapping :: VIDMapping
  }
  deriving (Eq, Generic, NFData)

instance Show DepGraph where
  show ng = printf "G(Deps: %s)" (show $ vEdges ng.vgraph)

instance ShowWTIndexer DepGraph where
  tshow ng = do
    let
      xs = map (\(k, v) -> (getAddrFromVIDMust (getRefVertex k) ng.vidMapping, v)) (HashMap.toList $ vEdges ng.vgraph)
    deps <-
      mapM
        ( \(k, v) -> do
            kt <- tshow k
            vt <- mapM (\x -> tshow $ getIrredAddrFromIVMust x ng.vidMapping) v
            return $ T.pack $ printf "%s: %s" (T.unpack kt) (show vt)
        )
        xs
    return $ T.pack $ printf "G(Deps: %s)" (show deps)

mapVGraph :: (VGraph -> VGraph) -> DepGraph -> DepGraph
mapVGraph f ng = ng{vgraph = f (vgraph ng)}

mapCGraph :: (CGraph -> CGraph) -> DepGraph -> DepGraph
mapCGraph f ng = ng{cgraph = f (cgraph ng)}

data VGraph = VGraph
  { vEdges :: HashMap.HashMap RefVertex [ExprVertex]
  -- ^ The propagation edges maps a dependency vertexes to a list of dependent vertexes, all of which are irreducible.
  -- The irreducible edges are used to compute the strongly connected components (SCCs) in the propagation graph.
  , vVertexes :: Set.Set ExprVertex
  }
  deriving (Eq, Generic, NFData)

emptyVGraph :: VGraph
emptyVGraph =
  VGraph
    { vEdges = HashMap.empty
    , vVertexes = Set.empty
    }

insertVGraphEdge :: RefVertex -> ExprVertex -> VGraph -> VGraph
insertVGraphEdge depVtx useVtx g =
  g
    { vEdges = insertHMUnique depVtx useVtx (vEdges g)
    , vVertexes = Set.union (Set.fromList [useVtx, ExprVertex (getRefVertex depVtx)]) g.vVertexes
    }

{- | Insert a selection edge.

It does not add to the deptsMap because selection edges are not used for notification.
-}
insertVGraphSelEdge :: RefVertex -> ExprVertex -> VGraph -> VGraph
insertVGraphSelEdge depVtx useVtx g =
  g
    { vEdges = insertHMUnique depVtx useVtx (vEdges g)
    , vVertexes = Set.union (Set.fromList [useVtx, ExprVertex (getRefVertex depVtx)]) g.vVertexes
    }

-- | Delete all edges that have the given vertex as the dependency.
delVGEdgeByDep :: RefVertex -> VGraph -> VGraph
delVGEdgeByDep depVtx g =
  g
    { vEdges = HashMap.delete depVtx (vEdges g)
    }

-- | Delete all edges that have the given vertex by matching the use vertex with the given predicate.
delVGEdgeByUseMatch :: (ExprVertex -> Bool) -> VGraph -> VGraph
delVGEdgeByUseMatch useMatch g =
  g
    { vEdges = HashMap.map (filter (not . useMatch)) (vEdges g)
    }

queryVGUsesByDepMatch :: (RefVertex -> Bool) -> VGraph -> [ExprVertex]
queryVGUsesByDepMatch depMatch g = concatMap snd $ filter (depMatch . fst) (HashMap.toList $ vEdges g)

-- delVGVertexes :: (Int -> Bool) -> VGraph -> VGraph
-- delVGVertexes keep g =
--   g
--     { vEdges =
--         HashMap.map
--           -- Then filter the values.
--           (filter (\v -> keep (getExprVertex v)))
--           $ HashMap.filterWithKey (\k _ -> keep (getRefVertex k)) (vEdges g)
--     , vVertexes =
--         Set.filter
--           (\v -> (keep (getExprVertex v)))
--           (vVertexes g)
--     }

data CGraph = CGraph
  { pDAG :: HashMap.HashMap ExprVertex [ExprVertex]
  -- ^ Maps from an SCC rep address to a list of SCC rep addresses that represents the dependencies.
  , repToComps :: HashMap.HashMap ExprVertex (Set.Set ExprVertex, Bool)
  -- ^ Maps from a base address to a list of component addresses in the same strongly connected component.
  , compToRep :: HashMap.HashMap ExprVertex (ExprVertex, Bool)
  -- ^ Maps from an expression address to its SCC representative address.
  -- The Bool indicates whether the SCC is cyclic.
  }
  deriving (Eq, Generic, NFData)

emptyCGraph :: CGraph
emptyCGraph =
  CGraph
    { pDAG = HashMap.empty
    , repToComps = HashMap.empty
    , compToRep = HashMap.empty
    }

{- | Get the representative vertex of a given vertex in the component graph.

If the vertex is not found in the compToRep map, it means it is not yet added to the graph, so we create a new entry for
it.
-}
getOrCreateRepVtx :: ExprVertex -> CGraph -> (ExprVertex, CGraph)
getOrCreateRepVtx v g = case HashMap.lookup v (compToRep g) of
  Just (rep, _) -> (rep, g)
  Nothing ->
    ( v
    , g
        { compToRep = HashMap.insert v (v, False) (compToRep g)
        , repToComps = HashMap.insert v (Set.singleton v, False) (repToComps g)
        }
    )

{- | A group address representing a strongly connected component (SCC) in the propagation graph.

The Bool indicates whether the SCC is cyclic.
-}
newtype GrpAddr = GrpAddr {getGrpAddr :: (SuffixIrredAddr, Bool)} deriving (Eq, Ord, Generic, NFData)

instance Show GrpAddr where
  show (GrpAddr (addr, isCyclic)) =
    if isCyclic
      then "Cyclic " ++ show addr
      else show addr

instance ShowWTIndexer GrpAddr where
  tshow (GrpAddr (addr, isCyclic)) = do
    addrText <- tshow addr
    let cyclicText = if isCyclic then "Cyclic " else ""
    return $ cyclicText <> addrText

pattern IsAcyclicGrpAddr :: SuffixIrredAddr -> GrpAddr
pattern IsAcyclicGrpAddr addr <- GrpAddr (addr, False)

pattern IsCyclicGrpAddr :: SuffixIrredAddr -> GrpAddr
pattern IsCyclicGrpAddr addr <- GrpAddr (addr, True)

emptyPropGraph :: DepGraph
emptyPropGraph =
  DepGraph
    { nodesByUseFunc = Map.empty
    , vgraph = emptyVGraph
    , cgraph = emptyCGraph
    , vidMapping = defaultVIDMapping
    }

-- | Expression vertex representing an irreducible address.
newtype ExprVertex = ExprVertex {getExprVertex :: Int} deriving (Eq, Ord, Hashable, Generic, NFData)

instance Show ExprVertex where
  show (ExprVertex i) = "ev_" ++ show i
instance ShowWTIndexer ExprVertex

newtype RefVertex = RefVertex {getRefVertex :: Int} deriving (Eq, Ord, Hashable, Generic, NFData)
instance Show RefVertex where
  show (RefVertex i) = "rv_" ++ show i
instance ShowWTIndexer RefVertex

data VIDMapping = VIDMapping
  { vidToAddr :: HashMap.HashMap Int ValAddr
  , addrToVid :: HashMap.HashMap ValAddr Int
  , nextVid :: Int
  }
  deriving (Eq, Generic, NFData)

getVID :: ValAddr -> VIDMapping -> (Int, Maybe VIDMapping)
getVID addr m =
  case HashMap.lookup addr (addrToVid m) of
    Just vid -> (vid, Nothing)
    Nothing ->
      let vid = nextVid m
          newVidToAddr = HashMap.insert vid addr (vidToAddr m)
          newAddrToVid = HashMap.insert addr vid (addrToVid m)
       in ( vid
          , Just $
              VIDMapping
                { vidToAddr = newVidToAddr
                , addrToVid = newAddrToVid
                , nextVid = vid + 1
                }
          )

getAddrFromVID :: Int -> VIDMapping -> Maybe ValAddr
getAddrFromVID vid m = HashMap.lookup vid (vidToAddr m)

getAddrFromVIDMust :: (HasCallStack) => Int -> VIDMapping -> ValAddr
getAddrFromVIDMust vid m = case HashMap.lookup vid (vidToAddr m) of
  Just addr -> addr
  Nothing -> error $ printf "VID %d not found in VIDMapping" vid

getIrredAddrFromVIDMust :: (HasCallStack) => Int -> VIDMapping -> SuffixIrredAddr
getIrredAddrFromVIDMust vid m = case getAddrFromVID vid m >>= addrIsSufIrred of
  Just addr -> addr
  Nothing -> error $ printf "VID %s does not correspond to an irreducible address" (show vid)

getIrredAddrFromIVMust :: (HasCallStack) => ExprVertex -> VIDMapping -> SuffixIrredAddr
getIrredAddrFromIVMust iv = getIrredAddrFromVIDMust (getExprVertex iv)

defaultVIDMapping :: VIDMapping
defaultVIDMapping =
  VIDMapping
    { vidToAddr = HashMap.fromList [(rootVID, rootValAddr)]
    , addrToVid = HashMap.fromList [(rootValAddr, rootVID)]
    , nextVid = rootVID + 1
    }

irredVToRefV :: ExprVertex -> VIDMapping -> (Maybe RefVertex, Maybe VIDMapping)
irredVToRefV iv m = case irredVToRefAddr iv m of
  Just rAddr -> do
    let (rid, m1) = getVID (rfbAddrToAddr rAddr) m
    (Just (RefVertex rid), m1)
  Nothing -> (Nothing, Nothing)

irredVToRefAddr :: ExprVertex -> VIDMapping -> Maybe ReferableAddr
irredVToRefAddr iv m = do
  addr <- getAddrFromVID (getExprVertex iv) m
  addrIsRfbAddr addr

{- | Convert a referable vertex to an expression vertex.

There is no need to use the VIDMapping here because referable addresses are a subset of expression addresses.
-}
refVToIrredV :: RefVertex -> ExprVertex
refVToIrredV rv = ExprVertex (getRefVertex rv)

rootVID :: Int
rootVID = 0

-- | Get the component addresses of a given group address in the propagation graph.
getElemAddrInGrp :: GrpAddr -> DepGraph -> [SuffixIrredAddr]
getElemAddrInGrp gaddr ng = case ( do
                                    (baseID, _) <- HashMap.lookup (ExprVertex gaddrID) (compToRep ng.cgraph)
                                    HashMap.lookup baseID (repToComps ng.cgraph)
                                 ) of
  Nothing -> []
  Just (comps, _) -> map (`getIrredAddrFromIVMust` ng.vidMapping) (Set.toList comps)
 where
  addr = fst $ getGrpAddr gaddr
  (gaddrID, _) = getVID (sufIrredToAddr addr) ng.vidMapping

-- | Get all node addresses of a given group address in the propagation graph.
getNodeAddrsInGrp :: GrpAddr -> DepGraph -> [ValAddr]
getNodeAddrsInGrp gaddr ng =
  let irredAddrs = getElemAddrInGrp gaddr ng
   in Set.toList $
        foldr
          ( \siAddr acc ->
              let nodes = Map.findWithDefault [] siAddr ng.nodesByUseFunc
               in Set.union (Set.fromList nodes) acc
          )
          Set.empty
          irredAddrs

getNodeAddrsByFunc :: SuffixIrredAddr -> DepGraph -> [ValAddr]
getNodeAddrsByFunc funcAddr ng = Map.findWithDefault [] funcAddr ng.nodesByUseFunc

-- | Get all use components of a given component address in the propagation graph.
getUseGroups :: GrpAddr -> DepGraph -> [GrpAddr]
getUseGroups gaddr ng = case HashMap.lookup (ExprVertex repAddrID) (pDAG ng.cgraph) of
  Nothing -> []
  Just uses ->
    map
      ( \use ->
          GrpAddr
            ( getIrredAddrFromIVMust use ng.vidMapping
            , snd $ fromJust $ HashMap.lookup use ng.cgraph.compToRep
            )
      )
      uses
 where
  repAddr = fst $ getGrpAddr gaddr
  (repAddrID, _) = getVID (sufIrredToAddr repAddr) ng.vidMapping

-- | Look up the SCC address of a given address (which should be irreducible) in the propagation graph.
lookupGrpAddr :: SuffixIrredAddr -> DepGraph -> Maybe GrpAddr
lookupGrpAddr rfbAddr ng = case HashMap.lookup (ExprVertex rfbAddrID) (compToRep ng.cgraph) of
  Nothing -> Nothing
  Just (baseID, isCyclic) ->
    Just $
      -- The baseID must have its corresponding irreducible address.
      GrpAddr (getIrredAddrFromIVMust baseID ng.vidMapping, isCyclic)
 where
  (rfbAddrID, _) = getVID (sufIrredToAddr rfbAddr) ng.vidMapping

{- | Add a new dependency to the propagation graph and update the component graph.

The dependency is represented as an edge from the dependency address (dep) to the dependent address (use).

- The use address does not need to be referable.
- The dep address will later notify the dependent address if it changes. It should be a referable address.

Some cases:

1. sub-field RC: x: x.f. Resolving "x.f.g" gets dependency relationships: /x/f/g -> /x/f, /x/f -> /x.
    From the x -> x.f.g we get /x -> /x/f/g. So we have a cycle, which contains /x, /x/f, /x/f/g.
-}
addNewDepToNG :: (HasCallStack) => ValAddr -> (ReferableAddr, ReferableAddr) -> DepGraph -> DepGraph
addNewDepToNG use (depIdent, dep) =
  execState
    ( do
        let
          normDepAddr = sufIrredToAddr $ trimAddrToSufIrred (rfbAddrToAddr dep)
          normUseAddr = sufIrredToAddr $ trimAddrToSufIrred use
        irDepID <- liftGetVIDForG normDepAddr
        irUseID <- liftGetVIDForG normUseAddr
        let useVtx = ExprVertex irUseID
            depVtx = ExprVertex irDepID
        modify' $
          mapVGraph $
            insertVGraphEdge
              (RefVertex irDepID)
              useVtx
        modify' $ \g -> g{nodesByUseFunc = insertMUnique (trimAddrToSufIrred use) use g.nodesByUseFunc}
        addSelDepToG depIdent dep
        depRep <- state (liftGetRepVtx depVtx)
        useRep <- state (liftGetRepVtx useVtx)

        ng <- get
        if
          -- If both addresses are in the same SCC and they are not the same, do nothing.
          | depRep == useRep
          , depVtx /= useVtx ->
              return ()
          -- If there is no edge from useRep to depRep in the component graph, meaning there is no cycle formed, we
          -- can simply add the depRep -> useRep edge to the component graph.
          -- Notice that if depRep == useRep, there is still a path from useRep to depRep.
          | not (hasPathInCG useRep depRep ng)
          , -- Also make sure that the use is not referencing a child of itself, which would form a reference cycle.
            not (isPrefix normUseAddr normDepAddr && normUseAddr /= normDepAddr) -> do
              let newCDAG = insertHMUnique depRep useRep (pDAG ng.cgraph)
              modify' $ mapCGraph (\cg -> cg{pDAG = newCDAG})
          -- The new edge forms a cycle in the component graph, we need to recompute the component graph.
          | otherwise -> modify' updateCGraph
    )
 where
  liftGetRepVtx v g = let (rep, newCG) = getOrCreateRepVtx v g.cgraph in (rep, g{cgraph = newCG})

{- | Add a selection dependency to the propagation graph.

The selection dependency is represented as an edge from the parent to the child.

For example, if we have a selection dependency `a.b.c`, we add notification edges from `a` to `a.b`, and from `a.b` to
`a.b.c`.
-}
addSelDepToG :: (HasCallStack) => ReferableAddr -> ReferableAddr -> State DepGraph ()
addSelDepToG depIdent dep
  | depIdent == dep = return ()
  | otherwise = do
      let depPar = fromJust $ initRfbAddr dep
      dParID <- liftGetVIDForG (rfbAddrToAddr depPar)
      did <- liftGetVIDForG (rfbAddrToAddr dep)
      modify' $ mapVGraph $ insertVGraphSelEdge (RefVertex dParID) (ExprVertex did)
      addSelDepToG depIdent depPar

{- | Check if there is a path from one vertex to another in the component graph.

If from and to are the same, return True.
-}
hasPathInCG :: ExprVertex -> ExprVertex -> DepGraph -> Bool
hasPathInCG from to ng = dfs from Set.empty
 where
  dfs :: ExprVertex -> Set.Set ExprVertex -> Bool
  dfs current visited
    | current == to = True
    | Set.member current visited = False
    | otherwise =
        let neighbors = HashMap.findWithDefault [] current (pDAG ng.cgraph)
            newVisited = Set.insert current visited
         in any (\neighbor -> dfs neighbor newVisited) neighbors

liftGetVIDForG :: ValAddr -> State DepGraph Int
liftGetVIDForG addr = state $ \g ->
  let (i, newM) = getVID addr g.vidMapping
   in case newM of
        Just new -> (i, g{vidMapping = new})
        Nothing -> (i, g)

-- | Remove all edges from the dependency graph that match the given predicate on the use vertex.
delDGEdgesByUseMatch :: (HasCallStack) => (ValAddr -> Bool) -> DepGraph -> DepGraph
delDGEdgesByUseMatch useMatch =
  execState
    ( do
        m <- gets vidMapping
        modify' $ \g -> updateCGraph (mapVGraph (delVGEdgeByUseMatch (useMatchAdapt m)) g)
        -- modify' $ \g ->
        --   g
        --     { nodesByUseFunc =
        --         Map.map
        --           -- Then filter the values.
        --           (filter (not . match))
        --           -- First filter the keys.
        --           ( Map.filterWithKey
        --               (\k _ -> not (match (sufIrredToAddr k)))
        --               (nodesByUseFunc g)
        --           )
        --     }
    )
 where
  useMatchAdapt :: VIDMapping -> ExprVertex -> Bool
  useMatchAdapt m x = useMatch (getAddrFromVIDMust (getExprVertex x) m)

-- | Query the dependents by matching the use vertex with the given predicate.
queryUsesByDepMatch :: (HasCallStack) => (ValAddr -> Bool) -> DepGraph -> [ValAddr]
queryUsesByDepMatch depMatch =
  evalState
    ( do
        m <- gets vidMapping
        g <- gets vgraph
        let l = queryVGUsesByDepMatch (depMatchAdapt m) g
        return $ map (\x -> getAddrFromVIDMust (getExprVertex x) m) l
    )
 where
  depMatchAdapt :: VIDMapping -> RefVertex -> Bool
  depMatchAdapt m x = depMatch (getAddrFromVIDMust (getRefVertex x) m)

-- -- | Remove all vertexes from the dependency graph that match the given predicate.
-- delDGVertexes :: (HasCallStack) => (ValAddr -> Bool) -> DepGraph -> DepGraph
-- delDGVertexes match =
--   execState
--     ( do
--         m <- gets vidMapping
--         modify' $ \g -> updateCGraph (mapVGraph (delVGVertexes (keep m)) g)
--         modify' $ \g ->
--           g
--             { nodesByUseFunc =
--                 Map.map
--                   -- Then filter the values.
--                   (filter (not . match))
--                   -- First filter the keys.
--                   ( Map.filterWithKey
--                       (\k _ -> not (match (sufIrredToAddr k)))
--                       (nodesByUseFunc g)
--                   )
--             }
--     )
--  where
--   keep :: VIDMapping -> Int -> Bool
--   keep m x = not (match (getAddrFromVIDMust x m))

-- | Update the component graph based on the current propagation graph.
updateCGraph :: (HasCallStack) => DepGraph -> DepGraph
updateCGraph graph =
  let
    x = graph
    y =
      -- trace
      --   (printf "updateCGraph, g: %s" (show x))
      x
   in
    y
      { cgraph =
          CGraph
            { pDAG = newSCCDAG
            , repToComps = newBaseToComps
            , compToRep = newVToSCCBase
            }
      , vidMapping = newMapping
      }
 where
  newTarjanState = scc (vEdges graph.vgraph) (vVertexes graph.vgraph) graph.vidMapping
  newMapping = newTarjanState.tsVIDMapping
  newBaseToComps =
    foldr
      ( \a acc -> case a of
          AcyclicSCC x -> HashMap.insert x (Set.singleton x, False) acc
          -- Use the first element of the SCC as the base address
          CyclicSCC xs -> HashMap.insert (head xs) (Set.fromList xs, True) acc
      )
      HashMap.empty
      -- (trace (printf "newGraphSCCs: %s" (show newGraphSCCs)) newGraphSCCs)
      newTarjanState.tsSCCs
  newVToSCCBase =
    HashMap.foldrWithKey
      ( \base (comps, isCyclic) acc ->
          foldr
            (\addr nacc -> HashMap.insert addr (base, isCyclic) nacc)
            acc
            (Set.toList comps)
      )
      HashMap.empty
      newBaseToComps
  -- Convert the propagation graph edges to SCC graph edges.
  -- For each edge from src to deps, find the SCC address of src and each dep.
  -- If two keys map to the same SCC address, we merge the values of the two keys.
  newSCCDAG =
    HashMap.map Set.toList $
      HashMap.foldrWithKey
        ( \src deps acc ->
            let (srcBase, _) = newVToSCCBase `lookupMust` refVToIrredV src
                depBaseAddrs = Set.fromList $ map (\dep -> fst $ newVToSCCBase `lookupMust` dep) deps
                -- Remove the source SCC address from the dependent SCC addresses.
                -- This is because the source SCC address is not a dependency of itself.
                depSccAddrsWoSrc :: Set.Set ExprVertex
                depSccAddrsWoSrc = Set.delete srcBase depBaseAddrs
             in HashMap.insertWith Set.union srcBase depSccAddrsWoSrc acc
        )
        HashMap.empty
        (vEdges graph.vgraph)

scc :: (HasCallStack) => HashMap.HashMap RefVertex [ExprVertex] -> Set.Set ExprVertex -> VIDMapping -> TarjanState
scc edges vertexes m = execState go initState
 where
  initState = emptyTarjanState edges (Set.toList vertexes) m

  go :: (HasCallStack) => State TarjanState ()
  go = do
    forM_ vertexes $ \v -> do
      vIndex <- gets $ \ts -> dnmIndex $ tsMetaMap ts `lookupMust` v
      when (vIndex == 0) $
        sccDFS v

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
  { tsEdges :: HashMap.HashMap RefVertex [ExprVertex]
  , tsIndex :: !Int
  , tsStack :: [ExprVertex]
  , tsMetaMap :: HashMap.HashMap ExprVertex TarjanNodeMeta
  , tsSCCs :: [SCC]
  , tsAncLinks :: HashMap.HashMap ExprVertex [RefVertex]
  , tsVIDMapping :: VIDMapping
  }

emptyTarjanState :: HashMap.HashMap RefVertex [ExprVertex] -> [ExprVertex] -> VIDMapping -> TarjanState
emptyTarjanState edges vertexes m =
  TarjanState
    { tsEdges = edges
    , tsIndex = 0
    , tsStack = []
    , tsMetaMap = HashMap.fromList $ map (\v -> (v, emptyTarjanNodeMeta)) vertexes
    , tsSCCs = []
    , tsAncLinks = HashMap.empty
    , tsVIDMapping = m
    }

data SCC
  = AcyclicSCC ExprVertex
  | CyclicSCC [ExprVertex]
  deriving (Show)

-- | Perform a depth-first search to find strongly connected components (SCCs) using Tarjan's algorithm.
sccDFS :: (HasCallStack) => ExprVertex -> State TarjanState ()
sccDFS v = do
  modify' $ \ts ->
    let index = tsIndex ts
        newIndex = index + 1
        newMeta =
          TarjanNodeMeta
            { dnmLowLink = newIndex
            , dnmIndex = newIndex
            , dnmOnStack = True
            , dnmNType = RegularNeighbor
            }
     in ts{tsIndex = newIndex, tsStack = v : tsStack ts, tsMetaMap = HashMap.insert v newMeta (tsMetaMap ts)}
  neighbors <- getNeighbors v
  forM_ neighbors $ \w -> do
    -- If the current node finds itself as a neighbor, mark it as a RCNeighbor.
    when (w `elem` neighbors) $ modify' $ \ts ->
      let tm = tsMetaMap ts
          elemW = tm `lookupMust` w
          newMeta = elemW{dnmNType = RCNeighbor}
       in ts{tsMetaMap = HashMap.insert w newMeta tm}

    isWVisited <- gets (\ts -> (\m -> dnmIndex m /= 0) $ tsMetaMap ts `lookupMust` w)
    isWOnStack <- gets (\ts -> dnmOnStack $ tsMetaMap ts `lookupMust` w)
    if
      | not isWVisited -> do
          sccDFS w
          modify' $ \ts ->
            let tm = tsMetaMap ts
                lowlinkV = dnmLowLink $ tm `lookupMust` v
                lowlinkW = dnmLowLink $ tm `lookupMust` w
             in ts{tsMetaMap = HashMap.adjust (\entry -> entry{dnmLowLink = min lowlinkV lowlinkW}) v tm}
      | isWOnStack -> modify' $ \ts ->
          let tm = tsMetaMap ts
              lowlinkV = dnmLowLink $ tm `lookupMust` v
              indexW = dnmIndex $ tm `lookupMust` w
           in ts{tsMetaMap = HashMap.adjust (\entry -> entry{dnmLowLink = min lowlinkV indexW}) v tm}
      | otherwise -> return ()

  isRoot <- gets (\ts -> let m = tsMetaMap ts `lookupMust` v in dnmLowLink m == dnmIndex m)
  -- m <- gets tsVIDMapping
  -- let vAddr = getIrredAddrFromIVMust v m
  -- trace
  --   (printf "sccDFS: v=%s, %s, isRoot=%s, neighbors=%s" (show v) (show vAddr) (show isRoot) (show neighbors))
  --   (return ())
  when isRoot $ do
    modify' $ \ts ->
      let (sccRestNodes, restStack) = span (/= v) (tsStack ts)
          newStack = tail restStack
          curNodes = v : sccRestNodes
          newSCC =
            if dnmNType (tsMetaMap ts `lookupMust` v) == RCNeighbor
              then CyclicSCC curNodes
              else AcyclicSCC v
          newMetaMap =
            foldr
              ( \addr accMetaMap ->
                  -- Mark all nodes in the SCC as not on stack.
                  ( HashMap.adjust (\m -> m{dnmOnStack = False}) addr accMetaMap
                  )
              )
              (tsMetaMap ts)
              curNodes
       in -- trace
          --   (printf "Found SCC: %s, curNodes: %s" (show newSCC) (show curNodesAddrs))
          ts
            { tsStack = newStack
            , tsMetaMap = newMetaMap
            , tsSCCs = newSCC : tsSCCs ts
            }

getNeighbors :: ExprVertex -> State TarjanState [ExprVertex]
getNeighbors v = do
  edges <- gets tsEdges
  vRefM <- getRefVFromV v
  case vRefM of
    Nothing -> return []
    Just vRef -> return $ HashMap.findWithDefault [] vRef edges

data NeighborType
  = RegularNeighbor
  | -- | RCNeighbor means the neighbor is added through a child-to-parent edge.
    -- If later it turns out that there is no cycle formed through this edge, meaning there is no path from the neighbor
    -- back to the original node, this edge can be ignored.
    RCNeighbor
  deriving (Eq, Show)

{- | Check if the first address is a parent of the second address.

A parent address being a prefix of the child means that there must be at least one more referable segment in the
child address after the parent address.
-}
isSufIrredParent :: SuffixIrredAddr -> SuffixIrredAddr -> Bool
isSufIrredParent parent child =
  let
    parentAddr = sufIrredToAddr parent
    childAddr = sufIrredToAddr child
    isParentPrefix = isPrefix parentAddr childAddr
   in
    isParentPrefix
      && ( let diff = trimPrefixAddr parentAddr childAddr
               rest = V.filter isFeatureReferable diff.vFeatures
            in not (V.null rest)
         )

liftGetVIDForTS :: ValAddr -> State TarjanState Int
liftGetVIDForTS addr = state $ \ts ->
  let (i, newM) = getVID addr ts.tsVIDMapping
   in case newM of
        Just new -> (i, ts{tsVIDMapping = new})
        Nothing -> (i, ts)

getRefVFromV :: ExprVertex -> State TarjanState (Maybe RefVertex)
getRefVFromV x = do
  m <- gets tsVIDMapping
  let xAddrM = getAddrFromVID (getExprVertex x) m
  case xAddrM >>= addrIsRfbAddr of
    Just xAddrRef -> do
      i <- liftGetVIDForTS (rfbAddrToAddr xAddrRef)
      return $ Just (RefVertex i)
    Nothing -> return Nothing

lookupMust :: (HasCallStack, Show k, Show a, Hashable k) => HashMap.HashMap k a -> k -> a
lookupMust m k = case HashMap.lookup k m of
  Just v -> v
  Nothing -> error $ printf "key %s not found in map %s" (show k) (show m)

removeChildSIAddrs :: [SuffixIrredAddr] -> [SuffixIrredAddr]
removeChildSIAddrs addrs =
  -- If there is an address that is a child of another address, remove it.
  filter (\a -> not $ or [isSufIrredParent x a | x <- addrs]) addrs

insertHMUnique :: (Eq k, Hashable k, Eq a) => k -> a -> HashMap.HashMap k [a] -> HashMap.HashMap k [a]
insertHMUnique key val =
  HashMap.insertWith
    (\_ old -> if val `elem` old then old else val : old)
    key
    [val]

insertMUnique :: (Eq a, Ord k) => k -> a -> Map.Map k [a] -> Map.Map k [a]
insertMUnique key val =
  Map.insertWith
    (\_ old -> if val `elem` old then old else val : old)
    key
    [val]