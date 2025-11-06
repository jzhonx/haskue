{-# LANGUAGE MultiWayIf #-}

module NotifGraph where

import Control.Monad (forM_, when)
import Control.Monad.State.Strict (MonadState (..), State, execState, gets, modify)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Debug.Trace
import GHC.Stack (HasCallStack)
import Path
import Text.Printf (printf)

data NotifGraph = NotifGraph
  { deptsMap :: Map.Map SuffixReferableAddr [TreeAddr]
  -- ^ The notification edges maps a dependency address to a list of dependent addresses.
  , dagEdges :: Map.Map GrpAddr [GrpAddr]
  -- ^ Maps from a SCC address of a strongly connected component to a list of SCC addresses that represents
  -- the dependencies.
  , sccMap :: Map.Map GrpAddr (Set.Set SuffixIrredAddr)
  -- ^ Maps from a base address to a list of component addresses in the same strongly connected component.
  , notifGEdges :: Map.Map RefVertex [IrredVertex]
  -- ^ The notification edges maps a dependency vertexes to a list of dependent vertexes, all of which are irreducible.
  -- The irreducible edges are used to compute the strongly connected components (SCCs) in the notification graph.
  , notifGVertexes :: Set.Set IrredVertex
  , addrToGrpAddr :: Map.Map SuffixIrredAddr GrpAddr
  -- ^ Maps from an address to its base address in the SCC graph.
  , vidMapping :: VIDMapping
  }
  deriving (Eq)

instance Show NotifGraph where
  show ng =
    "NotifGraph\n"
      ++ "Dependents: "
      ++ show (deptsMap ng)
      ++ "\n"
      ++ "SCCGraph: "
      ++ show (dagEdges ng)
      ++ "\n"
      ++ "SCCs: "
      ++ show (sccMap ng)
      ++ "\n"
      ++ "AddrToGrpAddr: "
      ++ show (addrToGrpAddr ng)

data GrpAddr
  = ACyclicGrpAddr SuffixIrredAddr
  | CyclicBaseAddr SuffixIrredAddr
  deriving (Eq, Ord)

instance Show GrpAddr where
  show (ACyclicGrpAddr addr) = show addr
  show (CyclicBaseAddr addr) = printf "Cyclic %s" (show addr)

emptyNotifGraph :: NotifGraph
emptyNotifGraph =
  NotifGraph
    { deptsMap = Map.empty
    , notifGEdges = Map.empty
    , notifGVertexes = Set.empty
    , dagEdges = Map.empty
    , sccMap = Map.empty
    , addrToGrpAddr = Map.empty
    , vidMapping = defaultVIDMapping
    }

newtype IrredVertex = IrredVertex {getIrredVertex :: Int} deriving (Eq, Ord, Show)

newtype RefVertex = RefVertex {getRefVertex :: Int} deriving (Eq, Ord, Show)

data VIDMapping = VIDMapping
  { vidToAddr :: Map.Map Int TreeAddr
  , addrToVid :: Map.Map TreeAddr Int
  , nextVid :: Int
  }
  deriving (Eq)

getVID :: TreeAddr -> VIDMapping -> (Int, VIDMapping)
getVID addr m =
  case Map.lookup addr (addrToVid m) of
    Just vid -> (vid, m)
    Nothing ->
      let vid = nextVid m
          newVidToAddr = Map.insert vid addr (vidToAddr m)
          newAddrToVid = Map.insert addr vid (addrToVid m)
       in ( vid
          , VIDMapping
              { vidToAddr = newVidToAddr
              , addrToVid = newAddrToVid
              , nextVid = vid + 1
              }
          )

getAddrFromVID :: Int -> VIDMapping -> Maybe TreeAddr
getAddrFromVID vid m = Map.lookup vid (vidToAddr m)

getAddrFromVIDMust :: (HasCallStack) => Int -> VIDMapping -> TreeAddr
getAddrFromVIDMust vid m = case Map.lookup vid (vidToAddr m) of
  Just addr -> addr
  Nothing -> error $ printf "VID %d not found in VIDMapping" vid

getIrredAddrFromVIDMust :: (HasCallStack) => IrredVertex -> VIDMapping -> SuffixIrredAddr
getIrredAddrFromVIDMust iv m = case getAddrFromVID (getIrredVertex iv) m >>= addrIsSufIrred of
  Just addr -> addr
  Nothing -> error $ printf "VID %s does not correspond to an irreducible address" (show iv)

defaultVIDMapping :: VIDMapping
defaultVIDMapping =
  VIDMapping
    { vidToAddr = Map.fromList [(rootVID, rootTreeAddr)]
    , addrToVid = Map.fromList [(rootTreeAddr, rootVID)]
    , nextVid = rootVID + 1
    }

irredVToRefV :: IrredVertex -> VIDMapping -> (Maybe RefVertex, VIDMapping)
irredVToRefV iv m = case irredVToRefAddr iv m of
  Just rAddr -> do
    let (rid, m1) = getVID (sufRefToAddr rAddr) m
    (Just (RefVertex rid), m1)
  Nothing -> (Nothing, m)

irredVToRefAddr :: IrredVertex -> VIDMapping -> Maybe SuffixReferableAddr
irredVToRefAddr iv m = do
  addr <- getAddrFromVID (getIrredVertex iv) m
  addrIsSufRef addr

rootVID :: Int
rootVID = 0

-- | Get the dependents of a given dependency address (which should be referable) in the notification graph.
getDependents :: SuffixReferableAddr -> NotifGraph -> [TreeAddr]
getDependents rfbAddr ng = fromMaybe [] $ Map.lookup rfbAddr (deptsMap ng)

-- | Get the component addresses of a given SCC address in the notification graph.
getElemAddrInGrp :: GrpAddr -> NotifGraph -> [SuffixIrredAddr]
getElemAddrInGrp sccAddr ng = maybe [] Set.toList $ Map.lookup sccAddr (sccMap ng)

getDependentGroups :: GrpAddr -> NotifGraph -> [GrpAddr]
getDependentGroups sccAddr ng = fromMaybe [] $ Map.lookup sccAddr (dagEdges ng)

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
lookupGrpAddr rfbAddr ng = Map.lookup rfbAddr (addrToGrpAddr ng)

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
        -- refID <- liftGetVIDForG ref
        refTrimmedID <- liftGetVIDForG (sufIrredToAddr $ trimAddrToSufIrred ref)
        -- defID <- liftGetVIDForG (sufRefToAddr def)
        defTrimmedID <- liftGetVIDForG (sufIrredToAddr $ trimAddrToSufIrred (sufRefToAddr def))
        modify $ \g ->
          g
            { deptsMap =
                Map.insertWith
                  (\old _ -> if ref `elem` old then old else ref : old)
                  def
                  [ref]
                  (deptsMap g)
            , notifGEdges =
                Map.insertWith
                  (\old _ -> if IrredVertex refTrimmedID `elem` old then old else IrredVertex refTrimmedID : old)
                  (RefVertex defTrimmedID)
                  [IrredVertex refTrimmedID]
                  (notifGEdges g)
            , notifGVertexes = Set.union (Set.fromList [IrredVertex refTrimmedID, IrredVertex defTrimmedID]) (notifGVertexes g)
            }
    )

liftGetVIDForG :: TreeAddr -> State NotifGraph Int
liftGetVIDForG addr = state $ \g -> let (i, m) = getVID addr g.vidMapping in (i, g{vidMapping = m})

-- | Remove all dependents from the notification graph that start with the given prefix.
delDepPrefixFromNG :: (HasCallStack) => TreeAddr -> NotifGraph -> NotifGraph
delDepPrefixFromNG prefix =
  execState
    ( do
        m <- gets vidMapping
        modify $ \g ->
          updateNotifGraph
            ( g
                { deptsMap = Map.map (filter isAncestor) (deptsMap g)
                , notifGEdges =
                    Map.filterWithKey
                      (\k _ -> isAncestor (getAddrFromVIDMust (getRefVertex k) m))
                      (notifGEdges g)
                }
            )
    )
 where
  isAncestor x = not (isPrefix prefix x)

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
      , sccMap = newSCCs
      , addrToGrpAddr = newAddrToGrpAddr
      , vidMapping = newMapping
      }
 where
  newTarjanState = scc (notifGEdges graph) (notifGVertexes graph) graph.vidMapping
  newMapping = newTarjanState.tsVIDMapping
  newSCCs =
    foldr
      ( \a acc -> case a of
          AcyclicSCC x ->
            let addr = getIrredAddrFromVIDMust x newMapping
             in Map.insert
                  (ACyclicGrpAddr addr)
                  (Set.singleton addr)
                  acc
          -- Use the first element of the SCC as the base address
          CyclicSCC xs ->
            Map.insert
              (CyclicBaseAddr $ getIrredAddrFromVIDMust (head xs) newMapping)
              (Set.fromList $ [getIrredAddrFromVIDMust x newMapping | x <- xs])
              acc
      )
      Map.empty
      -- (trace (printf "newGraphSCCs: %s" (show newGraphSCCs)) newGraphSCCs)
      newTarjanState.tsSCCs
  newAddrToGrpAddr =
    Map.fromList
      [ (addr, rep)
      | (rep, addrs) <- Map.toList newSCCs
      , addr <- Set.toList addrs
      ]
  newSCCDAG =
    Map.map Set.toList $
      Map.foldrWithKey
        ( \src deps acc ->
            let srcGrpAddr = newAddrToGrpAddr `lookupMust` sufRefToSufIrred src
                depGrpAddrs = Set.fromList $ map (\dep -> newAddrToGrpAddr `lookupMust` trimAddrToSufIrred dep) deps
                -- Remove the source SCC address from the dependent SCC addresses.
                -- This is because the source SCC address is not a dependency of itself.
                depSccAddrsWoSrc :: Set.Set GrpAddr
                depSccAddrsWoSrc = Set.delete srcGrpAddr depGrpAddrs
             in Map.insertWith Set.union srcGrpAddr depSccAddrsWoSrc acc
        )
        Map.empty
        (deptsMap graph)

scc :: (HasCallStack) => Map.Map RefVertex [IrredVertex] -> Set.Set IrredVertex -> VIDMapping -> TarjanState
scc edges vertexes m = execState ({-# SCC "sccGo" #-} go) initState
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
  { tsEdges :: Map.Map RefVertex [IrredVertex]
  , tsIndex :: !Int
  , tsStack :: [IrredVertex]
  , tsMetaMap :: Map.Map IrredVertex TarjanNodeMeta
  , tsSCCs :: [SCC]
  , tsAncLinks :: Map.Map IrredVertex [RefVertex]
  , tsVIDMapping :: VIDMapping
  }

emptyTarjanState :: Map.Map RefVertex [IrredVertex] -> [IrredVertex] -> VIDMapping -> TarjanState
emptyTarjanState edges vertexes m =
  TarjanState
    { tsEdges = edges
    , tsIndex = 0
    , tsStack = []
    , tsMetaMap = Map.fromList $ map (\v -> (v, emptyTarjanNodeMeta)) vertexes
    , tsSCCs = []
    , tsAncLinks = Map.empty
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
     in ts{tsIndex = newIndex, tsStack = v : tsStack ts, tsMetaMap = Map.insert v newMeta (tsMetaMap ts)}
  neighbors <- getNeighbors v
  forM_ neighbors $ \(w, isWParent) -> do
    -- If the neighbor is a parent, mark it with v being its structural cycle descendant.
    when isWParent $ modify $ \ts ->
      let tm = tsMetaMap ts
          elemW = tm `lookupMust` w
          newMeta = elemW{dnmSCDescendant = Just v}
       in ts{tsMetaMap = Map.insert w newMeta tm}
    isWVisited <- gets (\ts -> (\m -> dnmIndex m /= 0) $ tsMetaMap ts `lookupMust` w)
    isWOnStack <- gets (\ts -> dnmOnStack $ tsMetaMap ts `lookupMust` w)
    if
      | not isWVisited -> do
          sccDFS w
          modify $ \ts ->
            let tm = tsMetaMap ts
                lowlinkV = dnmLowLink $ tm `lookupMust` v
                lowlinkW = dnmLowLink $ tm `lookupMust` w
             in ts{tsMetaMap = Map.adjust (\entry -> entry{dnmLowLink = min lowlinkV lowlinkW}) v tm}
      | isWOnStack -> modify $ \ts ->
          let tm = tsMetaMap ts
              lowlinkV = dnmLowLink $ tm `lookupMust` v
              indexW = dnmIndex $ tm `lookupMust` w
           in ts{tsMetaMap = Map.adjust (\entry -> entry{dnmLowLink = min lowlinkV indexW}) v tm}
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
                  ( Map.adjust (\m -> m{dnmOnStack = False}) addr accMetaMap
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
                      dependents <- Map.lookup rv (tsEdges ts)
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
    Map.Map RefVertex [IrredVertex] ->
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
                    (Map.lookup (RefVertex y) edges)
              go parV False edges newAcc
          | not start
          , Just xAddrRef <- xAddrM >>= addrIsSufRef -> do
              y <- liftGetVIDForTS (sufRefToAddr xAddrRef)
              let newAcc = if Map.member (RefVertex y) edges then (x, True) : acc else acc
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
      && ( let TreeAddr diff = trimPrefixTreeAddr parentAddr childAddr
               rest = V.filter isFeatureReferable diff
            in not (V.null rest)
         )

liftGetVIDForTS :: TreeAddr -> State TarjanState Int
liftGetVIDForTS addr = state $ \ts -> let (i, m) = getVID addr ts.tsVIDMapping in (i, ts{tsVIDMapping = m})

liftIrredVToRefV :: IrredVertex -> State TarjanState (Maybe RefVertex)
liftIrredVToRefV iv = state $ \s -> let (r, m) = irredVToRefV iv s.tsVIDMapping in (r, s{tsVIDMapping = m})

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

lookupMust :: (HasCallStack, Ord k, Show k, Show a) => Map.Map k a -> k -> a
lookupMust m k = case Map.lookup k m of
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