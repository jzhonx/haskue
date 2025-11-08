{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}

module NotifGraph where

import Control.Monad (forM_, when)
import Control.Monad.State.Strict (MonadState (..), State, execState, gets, modify)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Vector as V
import Debug.Trace
import Feature
import GHC.Stack (HasCallStack)
import StringIndex (ShowWithTextIndexer (..))
import Text.Printf (printf)

data NotifGraph = NotifGraph
  { deptsMap :: HashMap.HashMap RefVertex [Int]
  -- ^ The notification edges maps a dependency vertex to a list of dependent addresses, which are not necessarily
  -- irreducible or referable.
  , notifGEdges :: HashMap.HashMap RefVertex [IrredVertex]
  -- ^ The notification edges maps a dependency vertexes to a list of dependent vertexes, all of which are irreducible.
  -- The irreducible edges are used to compute the strongly connected components (SCCs) in the notification graph.
  , notifGVertexes :: Set.Set IrredVertex
  -- ^ Above all three fields are used to represent the notification graph before computing the SCCs.
  -- == Below are the SCC graph representation.
  , dagEdges :: HashMap.HashMap IrredVertex [IrredVertex]
  -- ^ Maps from an SCC address of a strongly connected component to a list of SCC addresses that represents
  -- the dependencies.
  , baseToComps :: HashMap.HashMap IrredVertex (Set.Set IrredVertex, Bool)
  -- ^ Maps from a base address to a list of component addresses in the same strongly connected component.
  , vToSCCBase :: HashMap.HashMap IrredVertex (IrredVertex, Bool)
  -- ^ Maps from an irreducible address to its SCC representative address.
  -- The Bool indicates whether the SCC is cyclic.
  , vidMapping :: VIDMapping
  }
  deriving (Eq)

instance Show NotifGraph where
  show ng = printf "G(Deps: %s)" (show $ deptsMap ng)

instance ShowWithTextIndexer NotifGraph where
  tshow ng = do
    let
      xs = map (\(k, v) -> (getAddrFromVIDMust (getRefVertex k) ng.vidMapping, v)) (HashMap.toList $ deptsMap ng)
    deps <-
      mapM
        ( \(k, v) -> do
            kt <- tshow k
            vt <- mapM (\x -> tshow $ getAddrFromVIDMust x ng.vidMapping) v
            return $ T.pack $ printf "%s: %s" (T.unpack kt) (show vt)
        )
        xs
    return $ T.pack $ printf "G(Deps: %s)" (show deps)

newtype GrpAddr = GrpAddr {getGrpAddr :: (SuffixIrredAddr, Bool)} deriving (Eq, Ord)

instance Show GrpAddr where
  show (GrpAddr (addr, isCyclic)) =
    if isCyclic
      then "Cyclic " ++ show addr
      else show addr

instance ShowWithTextIndexer GrpAddr where
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
    { deptsMap = HashMap.empty
    , baseToComps = HashMap.empty
    , vToSCCBase = HashMap.empty
    , notifGEdges = HashMap.empty
    , notifGVertexes = Set.empty
    , dagEdges = HashMap.empty
    , vidMapping = defaultVIDMapping
    }

newtype IrredVertex = IrredVertex {getIrredVertex :: Int} deriving (Eq, Ord, Hashable)

newtype RefVertex = RefVertex {getRefVertex :: Int} deriving (Eq, Ord, Hashable)

instance Show IrredVertex where
  show (IrredVertex i) = "iv_" ++ show i

instance Show RefVertex where
  show (RefVertex i) = "rv_" ++ show i

instance ShowWithTextIndexer IrredVertex

instance ShowWithTextIndexer RefVertex

data VIDMapping = VIDMapping
  { vidToAddr :: HashMap.HashMap Int TreeAddr
  , addrToVid :: HashMap.HashMap TreeAddr Int
  , nextVid :: Int
  }
  deriving (Eq)

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

getIrredAddrFromIVMust :: (HasCallStack) => IrredVertex -> VIDMapping -> SuffixIrredAddr
getIrredAddrFromIVMust iv = getIrredAddrFromVIDMust (getIrredVertex iv)

defaultVIDMapping :: VIDMapping
defaultVIDMapping =
  VIDMapping
    { vidToAddr = HashMap.fromList [(rootVID, rootTreeAddr)]
    , addrToVid = HashMap.fromList [(rootTreeAddr, rootVID)]
    , nextVid = rootVID + 1
    }

irredVToRefV :: IrredVertex -> VIDMapping -> (Maybe RefVertex, Maybe VIDMapping)
irredVToRefV iv m = case irredVToRefAddr iv m of
  Just rAddr -> do
    let (rid, m1) = getVID (sufRefToAddr rAddr) m
    (Just (RefVertex rid), m1)
  Nothing -> (Nothing, Nothing)

irredVToRefAddr :: IrredVertex -> VIDMapping -> Maybe SuffixReferableAddr
irredVToRefAddr iv m = do
  addr <- getAddrFromVID (getIrredVertex iv) m
  addrIsSufRef addr

{- | Convert a referable vertex to an irreducible vertex.

There is no need to use the VIDMapping here because referable addresses are a subset of irreducible addresses.
-}
refVToIrredV :: RefVertex -> IrredVertex
refVToIrredV rv = IrredVertex (getRefVertex rv)

rootVID :: Int
rootVID = 0

-- | Get the dependents of a given dependency address (which should be referable) in the notification graph.
getDependents :: SuffixReferableAddr -> NotifGraph -> [TreeAddr]
getDependents rfbAddr ng = case HashMap.lookup (RefVertex rfbAddrID) (deptsMap ng) of
  Nothing -> []
  Just deps -> map (`getAddrFromVIDMust` ng.vidMapping) deps
 where
  (rfbAddrID, _) = getVID (sufRefToAddr rfbAddr) ng.vidMapping

-- | Get the component addresses of a given SCC address in the notification graph.
getElemAddrInGrp :: GrpAddr -> NotifGraph -> [SuffixIrredAddr]
getElemAddrInGrp gaddr ng = case ( do
                                    (baseID, _) <- HashMap.lookup (IrredVertex gaddrID) (vToSCCBase ng)
                                    HashMap.lookup baseID (baseToComps ng)
                                 ) of
  Nothing -> []
  Just (comps, _) -> map (`getIrredAddrFromIVMust` ng.vidMapping) (Set.toList comps)
 where
  addr = fst $ getGrpAddr gaddr
  (gaddrID, _) = getVID (sufIrredToAddr addr) ng.vidMapping

getDependentGroups :: GrpAddr -> NotifGraph -> [GrpAddr]
getDependentGroups gaddr ng = case HashMap.lookup (IrredVertex srcAddrID) (dagEdges ng) of
  Nothing -> []
  Just deps ->
    map
      ( \dep ->
          GrpAddr (getIrredAddrFromIVMust dep ng.vidMapping, snd $ fromJust $ HashMap.lookup dep ng.vToSCCBase)
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
              referable <- sufIrredIsSufRef compAddr
              return $ getDependents referable ng
          )
          compsAddrs
   in
    dependents

-- | Look up the SCC address of a given address (which should be irreducible) in the notification graph.
lookupGrpAddr :: SuffixIrredAddr -> NotifGraph -> Maybe GrpAddr
lookupGrpAddr rfbAddr ng = case HashMap.lookup (IrredVertex rfbAddrID) (vToSCCBase ng) of
  Nothing -> Nothing
  Just (baseID, isCyclic) ->
    Just $
      -- The baseID must have its corresponding irreducible address.
      GrpAddr (getIrredAddrFromIVMust baseID ng.vidMapping, isCyclic)
 where
  (rfbAddrID, _) = getVID (sufIrredToAddr rfbAddr) ng.vidMapping

{- | Add a new dependency to the notification graph and Update the SCC graph.

- The dependent (ref) address does not need to be referable.
- The dependency (def) address will later notify the dependent address if it changes.
- The dependency (def) address should be a referable address.
-}
addNewDepToNG :: (HasCallStack) => (TreeAddr, SuffixReferableAddr) -> NotifGraph -> NotifGraph
addNewDepToNG (ref, def) ng = updateNotifGraph $ addDepToNGRaw (ref, def) ng

{- | Add a new dependency to the notification graph without updating the SCC graph.

- The dependent (ref) address does not need to be referable.
- The def address will later notify the dependent address if it changes.
- The def address should be a referable address.
-}
addDepToNGRaw :: (TreeAddr, SuffixReferableAddr) -> NotifGraph -> NotifGraph
addDepToNGRaw (ref, def) =
  execState
    ( do
        refID <- liftGetVIDForG ref
        irRefID <- liftGetVIDForG (sufIrredToAddr $ trimAddrToSufIrred ref)
        irDefID <- liftGetVIDForG (sufIrredToAddr $ trimAddrToSufIrred (sufRefToAddr def))
        modify $ \g ->
          g
            { deptsMap =
                HashMap.insertWith
                  (\old _ -> if refID `elem` old then old else refID : old)
                  (RefVertex irDefID)
                  [refID]
                  (deptsMap g)
            , notifGEdges =
                HashMap.insertWith
                  (\old _ -> if IrredVertex irRefID `elem` old then old else IrredVertex irRefID : old)
                  (RefVertex irDefID)
                  [IrredVertex irRefID]
                  (notifGEdges g)
            , notifGVertexes = Set.union (Set.fromList [IrredVertex irRefID, IrredVertex irDefID]) g.notifGVertexes
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
        modify $ \g ->
          updateNotifGraph
            ( g
                { deptsMap =
                    HashMap.map
                      -- Then filter the values.
                      (filter (keep m))
                      -- First filter the keys.
                      (HashMap.filterWithKey (\k _ -> keep m (getRefVertex k)) $ deptsMap g)
                , notifGEdges =
                    HashMap.map
                      -- Then filter the values.
                      (filter (\v -> keep m (getIrredVertex v)))
                      $ HashMap.filterWithKey (\k _ -> keep m (getRefVertex k)) (notifGEdges g)
                , notifGVertexes =
                    Set.filter
                      (\v -> (keep m (getIrredVertex v)))
                      (notifGVertexes g)
                }
            )
    )
 where
  keep :: VIDMapping -> Int -> Bool
  keep m x = not (isPrefix prefix (getAddrFromVIDMust x m))

-- | Update the SCC graph based on the current notification graph.
updateNotifGraph :: (HasCallStack) => NotifGraph -> NotifGraph
updateNotifGraph graph =
  let
    x = graph
    y =
      -- trace
      --   (printf "updateNotifGraph, g: %s" (show x))
      x
   in
    y
      { dagEdges = newSCCDAG
      , baseToComps = newBaseToComps
      , vToSCCBase = newVToSCCBase
      , vidMapping = newMapping
      }
 where
  newTarjanState = scc (notifGEdges graph) (notifGVertexes graph) graph.vidMapping
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
                depSccAddrsWoSrc :: Set.Set IrredVertex
                depSccAddrsWoSrc = Set.delete srcBase depBaseAddrs
             in HashMap.insertWith Set.union srcBase depSccAddrsWoSrc acc
        )
        HashMap.empty
        (notifGEdges graph)

scc :: (HasCallStack) => HashMap.HashMap RefVertex [IrredVertex] -> Set.Set IrredVertex -> VIDMapping -> TarjanState
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
  , dnmSCDescendant :: !(Maybe IrredVertex)
  -- ^ It contains the descendant address of the node that forms a structural cycle.
  }
  deriving (Show)

emptyTarjanNodeMeta :: TarjanNodeMeta
emptyTarjanNodeMeta = TarjanNodeMeta 0 0 False Nothing

data TarjanState = TarjanState
  { tsEdges :: HashMap.HashMap RefVertex [IrredVertex]
  , tsIndex :: !Int
  , tsStack :: [IrredVertex]
  , tsMetaMap :: HashMap.HashMap IrredVertex TarjanNodeMeta
  , tsSCCs :: [SCC]
  , tsAncLinks :: HashMap.HashMap IrredVertex [RefVertex]
  , tsVIDMapping :: VIDMapping
  }

emptyTarjanState :: HashMap.HashMap RefVertex [IrredVertex] -> [IrredVertex] -> VIDMapping -> TarjanState
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
  = AcyclicSCC IrredVertex
  | CyclicSCC [IrredVertex]
  deriving (Show)

-- | Perform a depth-first search to find strongly connected components (SCCs) using Tarjan's algorithm.
sccDFS :: (HasCallStack) => IrredVertex -> State TarjanState ()
sccDFS v = do
  modify $ \ts ->
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
    when isWParent $ modify $ \ts ->
      let tm = tsMetaMap ts
          elemW = tm `lookupMust` w
          newMeta = elemW{dnmSCDescendant = Just v}
       in ts{tsMetaMap = HashMap.insert w newMeta tm}
    isWVisited <- gets (\ts -> (\m -> dnmIndex m /= 0) $ tsMetaMap ts `lookupMust` w)
    isWOnStack <- gets (\ts -> dnmOnStack $ tsMetaMap ts `lookupMust` w)
    if
      | not isWVisited -> do
          sccDFS w
          modify $ \ts ->
            let tm = tsMetaMap ts
                lowlinkV = dnmLowLink $ tm `lookupMust` v
                lowlinkW = dnmLowLink $ tm `lookupMust` w
             in ts{tsMetaMap = HashMap.adjust (\entry -> entry{dnmLowLink = min lowlinkV lowlinkW}) v tm}
      | isWOnStack -> modify $ \ts ->
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
    modify $ \ts ->
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
getNeighbors :: IrredVertex -> State TarjanState [(IrredVertex, Bool)]
getNeighbors v = do
  edges <- gets tsEdges
  go v True edges []
 where
  -- start is True if the current address is the getNeighbor address.
  go ::
    IrredVertex ->
    Bool ->
    HashMap.HashMap RefVertex [IrredVertex] ->
    [(IrredVertex, Bool)] ->
    State TarjanState [(IrredVertex, Bool)]
  go x start edges acc
    | getIrredVertex x == rootVID = return acc
    | otherwise = do
        parV <- getParentVertex x
        m <- gets tsVIDMapping
        let xAddrM = getAddrFromVID (getIrredVertex x) m
        if
          | start
          , Just xAddrRef <- xAddrM >>= addrIsSufRef -> do
              y <- liftGetVIDForTS (sufRefToAddr xAddrRef)
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
          , Just xAddrRef <- xAddrM >>= addrIsSufRef -> do
              y <- liftGetVIDForTS (sufRefToAddr xAddrRef)
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

liftIrredVToRefV :: IrredVertex -> State TarjanState (Maybe RefVertex)
liftIrredVToRefV iv = state $ \s ->
  let (r, newM) = irredVToRefV iv s.tsVIDMapping
   in case newM of
        Just new -> (r, s{tsVIDMapping = new})
        Nothing -> (r, s)

{- | Get the parent referable address of a given irreducible address.

It first converts the irreducible address to a referable address, then get the parent of the referable address.
-}
getParentVertex :: IrredVertex -> State TarjanState IrredVertex
getParentVertex v = do
  addr <- gets (fromJust . getAddrFromVID (getIrredVertex v) . tsVIDMapping)
  let r = go (trimAddrToSufRef addr)
  rid <- liftGetVIDForTS (sufRefToAddr r)
  return $ IrredVertex rid
 where
  go x
    | rootTreeAddr == sufRefToAddr x = x
    | otherwise = trimAddrToSufRef (fromJust $ initTreeAddr (sufRefToAddr x))

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
