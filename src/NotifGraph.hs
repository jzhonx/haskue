{-# LANGUAGE MultiWayIf #-}

module NotifGraph where

import Control.Monad (forM_, when)
import Control.Monad.State.Strict (State, execState, gets, modify)
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
  , notifGEdges :: Map.Map SuffixReferableAddr [SuffixIrredAddr]
  -- ^ The notification edges maps a dependency address to a list of dependent addresses, all of which are irreducible.
  -- The irreducible edges are used to compute the strongly connected components (SCCs) in the notification graph.
  , notifGVertexes :: Set.Set SuffixIrredAddr
  , dagEdges :: Map.Map GrpAddr [GrpAddr]
  -- ^ Maps from a SCC address of a strongly connected component to a list of SCC addresses that represents
  -- the dependencies.
  , sccMap :: Map.Map GrpAddr (Set.Set SuffixIrredAddr)
  -- ^ Maps from a base address to a list of component addresses in the same strongly connected component.
  , addrToGrpAddr :: Map.Map SuffixIrredAddr GrpAddr
  -- ^ Maps from an address to its base address in the SCC graph.
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
    }

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
addNewDepToNG (ref, def) ng = updateNotifGraph $ addNewDepToNGNoUpdate (ref, def) ng

{- | Add a new dependency to the notification graph.

This is mainly used for internal purposes.

- The dependent (ref) address does not need to be referable.
- The def address will later notify the dependent address if it changes.
- The def address should be a referable address.
-}
addNewDepToNGNoUpdate :: (TreeAddr, SuffixReferableAddr) -> NotifGraph -> NotifGraph
addNewDepToNGNoUpdate (ref, def) ng = ng{deptsMap = edges, notifGEdges = irredEdges, notifGVertexes = vertexes}
 where
  oldRefList = fromMaybe [] $ Map.lookup def (deptsMap ng)
  newRefList = if ref `elem` oldRefList then oldRefList else ref : oldRefList
  edges = Map.insert def newRefList (deptsMap ng)

  irredEdges =
    Map.insert
      def
      ( fst $
          foldr
            ( \x (acc, visited) ->
                let s = trimAddrToSufIrred x
                 in if s `elem` visited
                      then (acc, visited)
                      else (s : acc, Set.insert s visited)
            )
            ([], Set.empty)
            newRefList
      )
      (notifGEdges ng)
  vertexes =
    Set.union
      (Set.fromList [trimAddrToSufIrred ref, sufRefToSufIrred def])
      (notifGVertexes ng)

-- | Remove all dependents from the notification graph that start with the given prefix.
delDepPrefixFromNG :: (HasCallStack) => TreeAddr -> NotifGraph -> NotifGraph
delDepPrefixFromNG prefix ng =
  updateNotifGraph
    (ng{deptsMap = edges, notifGEdges = irredEdges})
 where
  isAncestor x = not (isPrefix prefix x)
  -- vertexes = Set.filter (isAncestor . sufIrredToAddr) (notifGVertexes ng)
  irredEdges = Map.filterWithKey (\k _ -> isAncestor (sufRefToAddr k)) (notifGEdges ng)
  edges =
    Map.map
      (\l -> filter isAncestor l)
      (deptsMap ng)

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
      }
 where
  newTarjanState = scc (notifGEdges graph) (notifGVertexes graph)
  newSCCs =
    foldr
      ( \a acc -> case a of
          AcyclicSCC x -> Map.insert (ACyclicGrpAddr x) (Set.singleton x) acc
          -- Use the first element of the SCC as the base address
          CyclicSCC xs ->
            Map.insert
              (CyclicBaseAddr (head xs))
              (Set.fromList xs)
              acc
              -- SCyclicSCC (x, y) xs ->
              --   Map.insert
              --     (SCyclicGrpAddr (x, y))
              --     (Set.fromList xs)
              --     acc
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

scc :: (HasCallStack) => Map.Map SuffixReferableAddr [SuffixIrredAddr] -> Set.Set SuffixIrredAddr -> TarjanState
scc edges vertexes = execState go initState
 where
  initState = emptyTarjanState edges (Set.toList vertexes)

  go :: (HasCallStack) => State TarjanState ()
  go = do
    forM_ vertexes $ \v -> do
      vIndex <- gets $ \ts -> dnmIndex $ tsMetaMap ts `lookupMust` v
      when (vIndex == 0) $
        sccDFS v

data TarjanNodeMeta = TarjanNodeMeta
  { dnmLowLink :: Int
  , dnmIndex :: Int
  , dnmOnStack :: Bool
  , dnmSCDescendant :: Maybe SuffixIrredAddr
  -- ^ It contains the descendant address of the node that forms a structural cycle.
  }
  deriving (Show)

emptyTarjanNodeMeta :: TarjanNodeMeta
emptyTarjanNodeMeta = TarjanNodeMeta 0 0 False Nothing

data TarjanState = TarjanState
  { tsEdges :: Map.Map SuffixReferableAddr [SuffixIrredAddr]
  , tsIndex :: Int
  , tsStack :: [SuffixIrredAddr]
  , tsMetaMap :: Map.Map SuffixIrredAddr TarjanNodeMeta
  , tsSCCs :: [SCC]
  , tsAncLinks :: Map.Map SuffixIrredAddr [SuffixReferableAddr]
  }

emptyTarjanState :: Map.Map SuffixReferableAddr [SuffixIrredAddr] -> [SuffixIrredAddr] -> TarjanState
emptyTarjanState edges vertexes =
  TarjanState edges 0 [] (Map.fromList $ map (\v -> (v, emptyTarjanNodeMeta)) vertexes) [] Map.empty

data SCC
  = AcyclicSCC SuffixIrredAddr
  | CyclicSCC [SuffixIrredAddr]
  deriving (Show)

-- \| -- | The pair is (descendant, ancestor).
-- SCyclicSCC (SuffixIrredAddr, SuffixReferableAddr) [SuffixIrredAddr]

-- | Perform a depth-first search to find strongly connected components (SCCs) using Tarjan's algorithm.
sccDFS :: (HasCallStack) => SuffixIrredAddr -> State TarjanState ()
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
  when isRoot $ do
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
                        rDesc <- sufIrredIsSufRef scDescendant
                        return (addr, rDesc)
                  )
              )
              (tsMetaMap ts, Nothing)
              (v : sccRestNodes)
          newSCC =
            if
              | null sccRestNodes
              , Just rv <- sufIrredIsSufRef v
              , -- If the only address in the SCC leads to itself, it is still a cyclic SCC.
                fromMaybe
                  False
                  ( do
                      dependents <- Map.lookup rv (tsEdges ts)
                      return $ length dependents == 1 && head dependents == v
                  ) ->
                  CyclicSCC [v]
              | null sccRestNodes -> AcyclicSCC v
              -- \| Just sc <- sCycleM -> SCyclicSCC sc (v : sccRestNodes)
              | otherwise -> CyclicSCC (v : sccRestNodes)
       in ts
            { tsStack = newStack
            , tsMetaMap = newMetaMap
            , tsSCCs = newSCC : tsSCCs ts
            -- , tsAncLinks = case sCycleM of
            --     Nothing -> ts.tsAncLinks
            --     Just (desc, anc) ->
            --       Map.insertWith (++) desc [anc] ts.tsAncLinks
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
getNeighbors :: SuffixIrredAddr -> State TarjanState [(SuffixIrredAddr, Bool)]
getNeighbors v = do
  edges <- gets tsEdges
  return $ go v True edges []
 where
  -- start is True if the current address is the getNeighbor address.
  go ::
    SuffixIrredAddr ->
    Bool ->
    Map.Map SuffixReferableAddr [SuffixIrredAddr] ->
    [(SuffixIrredAddr, Bool)] ->
    [(SuffixIrredAddr, Bool)]
  go x start edges acc
    | sufIrredToAddr x == rootTreeAddr = acc
    | start
    , Just rx <- sufIrredIsSufRef x =
        let newAcc = acc ++ maybe [] (map (\w -> (w, isSufIrredParent w v))) (Map.lookup rx edges)
         in go (sufRefToSufIrred $ getParentSufRefAddr x) False edges newAcc
    | not start
    , Just rx <- sufIrredIsSufRef x =
        let newAcc = acc ++ ([(x, True) | Map.member rx edges])
         in go (sufRefToSufIrred $ getParentSufRefAddr x) False edges newAcc
    | otherwise = go (sufRefToSufIrred $ getParentSufRefAddr x) False edges acc

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
               rest = V.filter isSegReferable diff
            in not (V.null rest)
         )

{- | Get the parent referable address of a given irreducible address.

It first converts the irreducible address to a referable address, then get the parent of the referable address.
-}
getParentSufRefAddr :: SuffixIrredAddr -> SuffixReferableAddr
getParentSufRefAddr addr = go (trimAddrToSufRef (sufIrredToAddr addr))
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