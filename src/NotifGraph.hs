{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}

module NotifGraph where

import Control.DeepSeq (NFData)
import Control.Monad (forM_, when)
import Control.Monad.State.Strict (MonadState (..), State, execState, gets, modify')
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Vector as V
import Debug.Trace
import Feature
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)

data NotifGraph = NotifGraph
  { vgraph :: VGraph
  , -- == Below are the SCC graph representation.
    -- ==
    cDAG :: HashMap.HashMap ExprVertex [ExprVertex]
  -- ^ Maps from an SCC rep address to a list of SCC rep addresses that represents the dependencies.
  , repToComps :: HashMap.HashMap ExprVertex (Set.Set ExprVertex, Bool)
  -- ^ Maps from a base address to a list of component addresses in the same strongly connected component.
  , compToRep :: HashMap.HashMap ExprVertex (ExprVertex, Bool)
  -- ^ Maps from an expression address to its SCC representative address.
  -- The Bool indicates whether the SCC is cyclic.
  , vidMapping :: VIDMapping
  }
  deriving (Eq, Generic, NFData)

instance Show NotifGraph where
  show ng = printf "G(Deps: %s)" (show $ deptsMap ng.vgraph)

instance ShowWTIndexer NotifGraph where
  tshow ng = do
    let
      xs = map (\(k, v) -> (getAddrFromVIDMust (getRefVertex k) ng.vidMapping, v)) (HashMap.toList $ deptsMap ng.vgraph)
    deps <-
      mapM
        ( \(k, v) -> do
            kt <- tshow k
            vt <- mapM (\x -> tshow $ getAddrFromVIDMust x ng.vidMapping) v
            return $ T.pack $ printf "%s: %s" (T.unpack kt) (show vt)
        )
        xs
    return $ T.pack $ printf "G(Deps: %s)" (show deps)

mapVGraph :: (VGraph -> VGraph) -> NotifGraph -> NotifGraph
mapVGraph f ng = ng{vgraph = f (vgraph ng)}

data VGraph = VGraph
  { deptsMap :: HashMap.HashMap RefVertex [Int]
  -- ^ The notification edges maps a dependency vertex to a list of dependent addresses, which are not necessarily
  -- irreducible or referable.
  , vEdges :: HashMap.HashMap RefVertex [ExprVertex]
  -- ^ The notification edges maps a dependency vertexes to a list of dependent vertexes, all of which are irreducible.
  -- The irreducible edges are used to compute the strongly connected components (SCCs) in the notification graph.
  , vVertexes :: Set.Set ExprVertex
  }
  deriving (Eq, Generic, NFData)

emptyVGraph :: VGraph
emptyVGraph =
  VGraph
    { deptsMap = HashMap.empty
    , vEdges = HashMap.empty
    , vVertexes = Set.empty
    }

insertVGraphEdge :: RefVertex -> (ExprVertex, Int) -> VGraph -> VGraph
insertVGraphEdge defVtx (refVtx, refID) g =
  g
    { deptsMap = insertUnique defVtx refID (deptsMap g)
    , vEdges = insertUnique defVtx refVtx (vEdges g)
    , vVertexes = Set.union (Set.fromList [refVtx, ExprVertex (getRefVertex defVtx)]) g.vVertexes
    }

delVGVertexes :: (Int -> Bool) -> VGraph -> VGraph
delVGVertexes keep g =
  g
    { deptsMap =
        HashMap.map
          -- Then filter the values.
          (filter keep)
          -- First filter the keys.
          (HashMap.filterWithKey (\k _ -> keep (getRefVertex k)) $ deptsMap g)
    , vEdges =
        HashMap.map
          -- Then filter the values.
          (filter (\v -> keep (getIrredVertex v)))
          $ HashMap.filterWithKey (\k _ -> keep (getRefVertex k)) (vEdges g)
    , vVertexes =
        Set.filter
          (\v -> (keep (getIrredVertex v)))
          (vVertexes g)
    }

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

emptyNotifGraph :: NotifGraph
emptyNotifGraph =
  NotifGraph
    { repToComps = HashMap.empty
    , compToRep = HashMap.empty
    , vgraph = emptyVGraph
    , cDAG = HashMap.empty
    , vidMapping = defaultVIDMapping
    }

-- | Expression vertex representing an irreducible address.
newtype ExprVertex = ExprVertex {getIrredVertex :: Int} deriving (Eq, Ord, Hashable, Generic, NFData)

newtype RefVertex = RefVertex {getRefVertex :: Int} deriving (Eq, Ord, Hashable, Generic, NFData)

instance Show ExprVertex where
  show (ExprVertex i) = "ev_" ++ show i

instance Show RefVertex where
  show (RefVertex i) = "rv_" ++ show i

instance ShowWTIndexer ExprVertex

instance ShowWTIndexer RefVertex

data VIDMapping = VIDMapping
  { vidToAddr :: HashMap.HashMap Int TreeAddr
  , addrToVid :: HashMap.HashMap TreeAddr Int
  , nextVid :: Int
  }
  deriving (Eq, Generic, NFData)

getVID :: TreeAddr -> VIDMapping -> (Int, Maybe VIDMapping)
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

getAddrFromVID :: Int -> VIDMapping -> Maybe TreeAddr
getAddrFromVID vid m = HashMap.lookup vid (vidToAddr m)

getAddrFromVIDMust :: (HasCallStack) => Int -> VIDMapping -> TreeAddr
getAddrFromVIDMust vid m = case HashMap.lookup vid (vidToAddr m) of
  Just addr -> addr
  Nothing -> error $ printf "VID %d not found in VIDMapping" vid

getIrredAddrFromVIDMust :: (HasCallStack) => Int -> VIDMapping -> SuffixIrredAddr
getIrredAddrFromVIDMust vid m = case getAddrFromVID vid m >>= addrIsSufIrred of
  Just addr -> addr
  Nothing -> error $ printf "VID %s does not correspond to an irreducible address" (show vid)

getIrredAddrFromIVMust :: (HasCallStack) => ExprVertex -> VIDMapping -> SuffixIrredAddr
getIrredAddrFromIVMust iv = getIrredAddrFromVIDMust (getIrredVertex iv)

defaultVIDMapping :: VIDMapping
defaultVIDMapping =
  VIDMapping
    { vidToAddr = HashMap.fromList [(rootVID, rootTreeAddr)]
    , addrToVid = HashMap.fromList [(rootTreeAddr, rootVID)]
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
  addr <- getAddrFromVID (getIrredVertex iv) m
  addrIsRfbAddr addr

{- | Convert a referable vertex to an expression vertex.

There is no need to use the VIDMapping here because referable addresses are a subset of expression addresses.
-}
refVToIrredV :: RefVertex -> ExprVertex
refVToIrredV rv = ExprVertex (getRefVertex rv)

rootVID :: Int
rootVID = 0

-- | Get the dependents of a given dependency address (which should be referable) in the notification graph.
getDependents :: ReferableAddr -> NotifGraph -> [TreeAddr]
getDependents rfbAddr ng = case HashMap.lookup (RefVertex rfbAddrID) (deptsMap ng.vgraph) of
  Nothing -> []
  Just deps -> map (`getAddrFromVIDMust` ng.vidMapping) deps
 where
  (rfbAddrID, _) = getVID (rfbAddrToAddr rfbAddr) ng.vidMapping

-- | Get the component addresses of a given SCC address in the notification graph.
getElemAddrInGrp :: GrpAddr -> NotifGraph -> [SuffixIrredAddr]
getElemAddrInGrp gaddr ng = case ( do
                                    (baseID, _) <- HashMap.lookup (ExprVertex gaddrID) (compToRep ng)
                                    HashMap.lookup baseID (repToComps ng)
                                 ) of
  Nothing -> []
  Just (comps, _) -> map (`getIrredAddrFromIVMust` ng.vidMapping) (Set.toList comps)
 where
  addr = fst $ getGrpAddr gaddr
  (gaddrID, _) = getVID (sufIrredToAddr addr) ng.vidMapping

getDependentGroups :: GrpAddr -> NotifGraph -> [GrpAddr]
getDependentGroups gaddr ng = case HashMap.lookup (ExprVertex srcAddrID) (cDAG ng) of
  Nothing -> []
  Just deps ->
    map
      ( \dep ->
          GrpAddr (getIrredAddrFromIVMust dep ng.vidMapping, snd $ fromJust $ HashMap.lookup dep ng.compToRep)
      )
      deps
 where
  addr = fst $ getGrpAddr gaddr
  (srcAddrID, _) = getVID (sufIrredToAddr addr) ng.vidMapping

-- | Get all dependents of a given SCC address in the notification graph.
getDependentsFromGroup :: GrpAddr -> NotifGraph -> [TreeAddr]
getDependentsFromGroup sccAddr ng =
  let
    compsAddrs = getElemAddrInGrp sccAddr ng
    dependents =
      concat $
        mapMaybe
          ( \compAddr -> do
              -- If the component address is referable, get its dependents.
              referable <- sufIrredIsRfb compAddr
              return $ getDependents referable ng
          )
          compsAddrs
   in
    dependents

-- | Look up the SCC address of a given address (which should be irreducible) in the notification graph.
lookupGrpAddr :: SuffixIrredAddr -> NotifGraph -> Maybe GrpAddr
lookupGrpAddr rfbAddr ng = case HashMap.lookup (ExprVertex rfbAddrID) (compToRep ng) of
  Nothing -> Nothing
  Just (baseID, isCyclic) ->
    Just $
      -- The baseID must have its corresponding irreducible address.
      GrpAddr (getIrredAddrFromIVMust baseID ng.vidMapping, isCyclic)
 where
  (rfbAddrID, _) = getVID (sufIrredToAddr rfbAddr) ng.vidMapping

{- | Add a new dependency to the notification graph and Update the component graph.

The dependency is represented as an edge from the dependency address (def) to the dependent address (ref).

- The dependent (ref) address does not need to be referable.
- The dependency (def) address will later notify the dependent address if it changes.
- The dependency (def) address should be a referable address.
-}
addNewDepToNG :: (HasCallStack) => (TreeAddr, ReferableAddr) -> NotifGraph -> NotifGraph
addNewDepToNG (ref, def) =
  execState
    ( do
        irDefID <- liftGetVIDForG (sufIrredToAddr $ trimAddrToSufIrred (rfbAddrToAddr def))
        refID <- liftGetVIDForG ref
        irRefID <- liftGetVIDForG (sufIrredToAddr $ trimAddrToSufIrred ref)
        let refVtx = ExprVertex irRefID
            defVtx = ExprVertex irDefID
        modify' $
          mapVGraph $
            insertVGraphEdge
              (RefVertex irDefID)
              (refVtx, refID)
        defRep <- state (getOrCreateRepVtx defVtx)
        refRep <- state (getOrCreateRepVtx refVtx)

        ng <- get
        if
          -- If both addresses are in the same SCC and they are not the same, do nothing.
          | defRep == refRep
          , defVtx /= refVtx ->
              return ()
          | not (hasPathInCG refRep defRep ng) -> do
              -- If there is no edge from refRep to defRep in the component graph, meaning there is no cycle formed,
              -- we can simply add the defRep -> refRep edge to the component graph.
              let newCDAG = insertUnique defRep refRep (cDAG ng)
              put $ ng{cDAG = newCDAG}
          -- The new edge forms a cycle in the component graph, we need to recompute the component graph.
          | otherwise -> modify' updateCGraph
    )

-- | Check if there is a path from one vertex to another in the component graph.
hasPathInCG :: ExprVertex -> ExprVertex -> NotifGraph -> Bool
hasPathInCG from to ng = dfs from Set.empty
 where
  dfs :: ExprVertex -> Set.Set ExprVertex -> Bool
  dfs current visited
    | current == to = True
    | Set.member current visited = False
    | otherwise =
        let neighbors = HashMap.findWithDefault [] current (cDAG ng)
            newVisited = Set.insert current visited
         in any (\neighbor -> dfs neighbor newVisited) neighbors

{- | Get the representative vertex of a given vertex in the notification graph.

If the vertex is not found in the compToRep map, it means it is not yet added to the graph, so we create a new entry for
it.
-}
getOrCreateRepVtx :: ExprVertex -> NotifGraph -> (ExprVertex, NotifGraph)
getOrCreateRepVtx v ng = case HashMap.lookup v (compToRep ng) of
  Just (rep, _) -> (rep, ng)
  Nothing ->
    ( v
    , ng
        { compToRep = HashMap.insert v (v, False) (compToRep ng)
        , repToComps = HashMap.insert v (Set.singleton v, False) (repToComps ng)
        }
    )

liftGetVIDForG :: TreeAddr -> State NotifGraph Int
liftGetVIDForG addr = state $ \g ->
  let (i, newM) = getVID addr g.vidMapping
   in case newM of
        Just new -> (i, g{vidMapping = new})
        Nothing -> (i, g)

-- | Remove all vertexes from the notification graph that start with the given prefix.
delNGVertexPrefix :: (HasCallStack) => TreeAddr -> NotifGraph -> NotifGraph
delNGVertexPrefix prefix =
  execState
    ( do
        m <- gets vidMapping
        modify' $ \g -> updateCGraph (mapVGraph (delVGVertexes (keep m)) g)
    )
 where
  keep :: VIDMapping -> Int -> Bool
  keep m x = not (isPrefix prefix (getAddrFromVIDMust x m))

-- | Update the component graph based on the current notification graph.
updateCGraph :: (HasCallStack) => NotifGraph -> NotifGraph
updateCGraph graph =
  let
    x = graph
    y =
      -- trace
      --   (printf "updateCGraph, g: %s" (show x))
      x
   in
    y
      { cDAG = newSCCDAG
      , repToComps = newBaseToComps
      , compToRep = newVToSCCBase
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
  -- Convert the notification graph edges to SCC graph edges.
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
  , dnmSCDescendant :: !(Maybe ExprVertex)
  -- ^ It contains the descendant address of the node that forms a structural cycle.
  }
  deriving (Show)

emptyTarjanNodeMeta :: TarjanNodeMeta
emptyTarjanNodeMeta = TarjanNodeMeta 0 0 False Nothing

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
            , dnmSCDescendant = Nothing
            }
     in ts{tsIndex = newIndex, tsStack = v : tsStack ts, tsMetaMap = HashMap.insert v newMeta (tsMetaMap ts)}
  neighbors <- getNeighbors v
  forM_ neighbors $ \(w, isWParent) -> do
    -- If the neighbor is a parent, mark it with v being its structural cycle descendant.
    when isWParent $ modify' $ \ts ->
      let tm = tsMetaMap ts
          elemW = tm `lookupMust` w
          newMeta = elemW{dnmSCDescendant = Just v}
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
  -- trace
  --   (printf "sccDFS: v=%s, isRoot=%s, neighbors=%s" (show v) (show isRoot) (show neighbors))
  --   (return ())
  mapping <- gets tsVIDMapping
  when isRoot $ do
    rvM <- liftIrredVToRefV v
    modify' $ \ts ->
      let (sccRestNodes, restStack) = span (/= v) (tsStack ts)
          newStack = tail restStack
          (newMetaMap, sCycleM) =
            foldr
              ( \addr (accMetaMap, accSCycleM) ->
                  ( HashMap.adjust (\m -> m{dnmOnStack = False}) addr accMetaMap
                  , if isJust accSCycleM
                      then accSCycleM
                      else do
                        scDescendant <- (accMetaMap `lookupMust` addr).dnmSCDescendant
                        rDesc <- irredVToRefAddr scDescendant mapping
                        return (addr, rDesc)
                  )
              )
              (tsMetaMap ts, Nothing)
              (v : sccRestNodes)
          newSCC =
            if
              | null sccRestNodes
              , Just rv <- rvM
              , -- If the only address in the SCC leads to itself, it is still a cyclic SCC.
                fromMaybe
                  False
                  ( do
                      dependents <- HashMap.lookup rv (tsEdges ts)
                      return $ length dependents == 1 && head dependents == v
                  ) ->
                  CyclicSCC [v]
              | null sccRestNodes -> AcyclicSCC v
              | otherwise -> CyclicSCC (v : sccRestNodes)
       in ts
            { tsStack = newStack
            , tsMetaMap = newMetaMap
            , tsSCCs = newSCC : tsSCCs ts
            }

{- | Get the neighbors of a node in the notification graph.

Returns a list of neighbors. Each neighbor is a tuple of the neighbor address and a boolean indicating whether the
neighbor is the parent of the current address.

In the notification graph, an edge from the child node to the parent ndoe is implied by the tree structure, but is not
recorded in the edges map. Therefore, we need to traverse up the tree to find all neighbors so that structural cycles
can be detected.

For example, p: a: p. There is only one edge /p -> /p/a. If we are in a, clearly a has no outgoing edges. But a should
have p as its neighbor because a is a child of p and p depends on a's finishness. Then we can detect the structural
cycle a -> p -> a.

Or p: {(p): 1}. The edge is /p -> /p/dyn_0.
-}
getNeighbors :: ExprVertex -> State TarjanState [(ExprVertex, Bool)]
getNeighbors v = do
  edges <- gets tsEdges
  go v True edges []
 where
  -- start is True if the current address is the getNeighbor address.
  go ::
    ExprVertex ->
    Bool ->
    HashMap.HashMap RefVertex [ExprVertex] ->
    [(ExprVertex, Bool)] ->
    State TarjanState [(ExprVertex, Bool)]
  go x start edges acc
    | getIrredVertex x == rootVID = return acc
    | otherwise = do
        parV <- getParentVertex x
        m <- gets tsVIDMapping
        let xAddrM = getAddrFromVID (getIrredVertex x) m
        if
          | start
          , Just xAddrRef <- xAddrM >>= addrIsRfbAddr -> do
              y <- liftGetVIDForTS (rfbAddrToAddr xAddrRef)
              let
                vIrredAddr = addMustBeSufIrred $ getAddrFromVIDMust (getIrredVertex v) m
                newAcc =
                  maybe
                    acc
                    ( foldr
                        ( \w nacc ->
                            let
                              wIrredAddr = addMustBeSufIrred $ getAddrFromVIDMust (getIrredVertex w) m
                             in
                              (w, isSufIrredParent wIrredAddr vIrredAddr) : nacc
                        )
                        acc
                    )
                    (HashMap.lookup (RefVertex y) edges)
              go parV False edges newAcc
          | not start
          , Just xAddrRef <- xAddrM >>= addrIsRfbAddr -> do
              y <- liftGetVIDForTS (rfbAddrToAddr xAddrRef)
              let newAcc = if HashMap.member (RefVertex y) edges then (x, True) : acc else acc
              go parV False edges newAcc
          | otherwise -> go parV False edges acc

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
      && ( let diff = trimPrefixTreeAddr parentAddr childAddr
               rest = V.filter isFeatureReferable diff.vFeatures
            in not (V.null rest)
         )

liftGetVIDForTS :: TreeAddr -> State TarjanState Int
liftGetVIDForTS addr = state $ \ts ->
  let (i, newM) = getVID addr ts.tsVIDMapping
   in case newM of
        Just new -> (i, ts{tsVIDMapping = new})
        Nothing -> (i, ts)

liftIrredVToRefV :: ExprVertex -> State TarjanState (Maybe RefVertex)
liftIrredVToRefV iv = state $ \s ->
  let (r, newM) = irredVToRefV iv s.tsVIDMapping
   in case newM of
        Just new -> (r, s{tsVIDMapping = new})
        Nothing -> (r, s)

{- | Get the parent referable address of a given expression address.

It first converts the expression address to a referable address, then get the parent of the referable address.
-}
getParentVertex :: ExprVertex -> State TarjanState ExprVertex
getParentVertex v = do
  addr <- gets (fromJust . getAddrFromVID (getIrredVertex v) . tsVIDMapping)
  let r = go (trimAddrToRfb addr)
  rid <- liftGetVIDForTS (rfbAddrToAddr r)
  return $ ExprVertex rid
 where
  go x
    | rootTreeAddr == rfbAddrToAddr x = x
    | otherwise = trimAddrToRfb (fromJust $ initTreeAddr (rfbAddrToAddr x))

lookupMust :: (HasCallStack, Show k, Show a, Hashable k) => HashMap.HashMap k a -> k -> a
lookupMust m k = case HashMap.lookup k m of
  Just v -> v
  Nothing -> error $ printf "key %s not found in map %s" (show k) (show m)

removeChildSIAddrs :: [SuffixIrredAddr] -> [SuffixIrredAddr]
removeChildSIAddrs addrs =
  -- If there is an address that is a child of another address, remove it.
  filter (\a -> not $ or [isSufIrredParent x a | x <- addrs]) addrs

removeParentSIAddrs :: [SuffixIrredAddr] -> [SuffixIrredAddr]
removeParentSIAddrs addrs =
  -- If there is an address that is a parent of another address, remove it.
  filter (\a -> not $ or [isSufIrredParent a x | x <- addrs]) addrs

insertUnique :: (Eq k, Hashable k, Eq a) => k -> a -> HashMap.HashMap k [a] -> HashMap.HashMap k [a]
insertUnique key val =
  HashMap.insertWith
    (\_ old -> if val `elem` old then old else val : old)
    key
    [val]