{-# LANGUAGE MultiWayIf #-}

module NotifGraph where

import Control.Monad (forM_, when)
import Control.Monad.State.Strict (State, execState, gets, modify)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust)
import qualified Data.Set as Set
import Debug.Trace
import GHC.Stack (HasCallStack)
import Path
import Text.Printf (printf)

data NotifGraph = NotifGraph
  { ngNotifEdges :: Map.Map TreeAddr [TreeAddr]
  -- ^ The notification edges maps a source referable address to a list of dependent addresses, which are not
  -- necessarily referable.
  , ngSCCDAGEdges :: Map.Map SCCAddr [SCCAddr]
  -- ^ Maps from a SCC address of a strongly connected component to a list of SCC addresses that represents
  -- the dependencies.
  , ngSCCs :: Map.Map SCCAddr (Set.Set TreeAddr)
  -- ^ Maps from a base address to a list of dependent addresses in the same strongly connected component.
  , ngAddrToSCCAddr :: Map.Map TreeAddr SCCAddr
  -- ^ Maps from a referable address to its base address in the SCC graph.
  }
  deriving (Eq)

instance Show NotifGraph where
  show ng =
    "NotifGraph\n"
      ++ "Edges: "
      ++ show (ngNotifEdges ng)
      ++ "\n"
      ++ "SCCGraph: "
      ++ show (ngSCCDAGEdges ng)
      ++ "\n"
      ++ "SCCs: "
      ++ show (ngSCCs ng)
      ++ "\n"
      ++ "AddrToSCCAddr: "
      ++ show (ngAddrToSCCAddr ng)

data SCCAddr
  = ACyclicSCCAddr TreeAddr
  | CyclicSCCAddr SCCBaseAddr
  | -- | The pair is (descendant, ancestor)
    SCyclicSCCAddr SCCBaseAddr (TreeAddr, TreeAddr)
  deriving (Eq, Ord, Show)

{- | A strongly connected component (SCC) base address is a base address of a cyclic SCC.

- It is used to represent cyclic SCCs in the notification graph.
- It is also in the referable form.
-}
newtype SCCBaseAddr = SCCBaseAddr TreeAddr deriving (Eq, Ord, Show)

emptyNotifGraph :: NotifGraph
emptyNotifGraph =
  NotifGraph
    { ngNotifEdges = Map.empty
    , ngSCCDAGEdges = Map.empty
    , ngSCCs = Map.empty
    , ngAddrToSCCAddr = Map.empty
    }

-- | Get the dependents of a given dependency address in the notification graph.
getDependents :: TreeAddr -> NotifGraph -> [TreeAddr]
getDependents addr ng = fromMaybe [] $ Map.lookup (trimToReferable addr) (ngNotifEdges ng)

-- | Get the component addresses of a given SCC address in the notification graph.
getSCCAddrs :: SCCAddr -> NotifGraph -> [TreeAddr]
getSCCAddrs sccAddr ng = maybe [] Set.toList $ Map.lookup sccAddr (ngSCCs ng)

getDependentSCCs :: SCCAddr -> NotifGraph -> [SCCAddr]
getDependentSCCs sccAddr ng = fromMaybe [] $ Map.lookup sccAddr (ngSCCDAGEdges ng)

-- | Look up the SCC address of a given address in the notification graph.
lookupSCCAddr :: TreeAddr -> NotifGraph -> Maybe SCCAddr
lookupSCCAddr addr ng = Map.lookup (trimToReferable addr) (ngAddrToSCCAddr ng)

{- | Add a new dependency to the notification graph and Update the SCC graph.

- The dependent (ref) address does not need to be referable.
- The dependency (def) address will later notify the dependent address if it changes.
- The dependency (def) address should be a referable address.
-}
addNewDepToNG :: (HasCallStack) => (TreeAddr, TreeAddr) -> NotifGraph -> NotifGraph
addNewDepToNG (ref, def) ng = updateNotifGraph $ addNewDepToNGNoUpdate (ref, def) ng

-- | Given a referable address in an cyclic SCC, find all dependent addresses that belong to the same SCC.
findRCDependents :: TreeAddr -> NotifGraph -> [TreeAddr]
findRCDependents addr ng = dependents
 where
  dependencies = fromMaybe Set.empty $ do
    sccAddr <- Map.lookup addr (ngAddrToSCCAddr ng)
    case sccAddr of
      CyclicSCCAddr _ -> Map.lookup sccAddr (ngSCCs ng)
      _ -> return Set.empty

  dependents =
    fst $
      foldr
        ( \defAddr (acc, accFound) ->
            case Map.lookup defAddr (ngNotifEdges ng) of
              Nothing -> (acc, accFound)
              Just refs ->
                let
                  rcRefs =
                    filter
                      ( \r ->
                          trimToReferable r `Set.member` dependencies
                            && not (r `Set.member` accFound)
                      )
                      refs
                 in
                  (rcRefs ++ acc, Set.union accFound (Set.fromList rcRefs))
        )
        ([], Set.empty)
        dependencies

{- | Add a new dependency to the notification graph.

This is mainly used for internal purposes.

- The dependent (ref) address does not need to be referable.
- The def address will later notify the dependent address if it changes.
- The def address should be a referable address.
-}
addNewDepToNGNoUpdate :: (TreeAddr, TreeAddr) -> NotifGraph -> NotifGraph
addNewDepToNGNoUpdate (ref, def) ng = ng{ngNotifEdges = edgesWithDep}
 where
  rfbRef = trimToReferable ref
  rfbDef = trimToReferable def
  oldRefList = fromMaybe [] $ Map.lookup rfbDef (ngNotifEdges ng)
  newRefList = if ref `elem` oldRefList then oldRefList else ref : oldRefList
  edges = Map.insert rfbDef newRefList (ngNotifEdges ng)
  edgesWithDep = if Map.member rfbRef edges then edges else Map.insert rfbRef [] edges

-- | Remove all dependents from the notification graph that start with the given prefix.
delDepWithPrefixFromNG :: (HasCallStack) => TreeAddr -> NotifGraph -> NotifGraph
delDepWithPrefixFromNG prefix ng = updateNotifGraph (ng{ngNotifEdges = edges})
 where
  edges =
    Map.map
      (\l -> filter (\dependent -> not $ isPrefix prefix dependent) l)
      (ngNotifEdges ng)

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
      { ngSCCDAGEdges = newSCCDAG
      , ngSCCs = newSCCs
      , ngAddrToSCCAddr = newAddrToSCCAddr
      }
 where
  newGraphSCCs = scc (ngNotifEdges graph)
  newSCCs =
    foldr
      ( \a acc -> case a of
          AcyclicSCC x -> Map.insert (ACyclicSCCAddr x) (Set.singleton x) acc
          -- Use the first element of the SCC as the base address
          CyclicSCC xs -> Map.insert (CyclicSCCAddr $ SCCBaseAddr (head xs)) (Set.fromList xs) acc
          SCyclicSCC (x, y) xs -> Map.insert (SCyclicSCCAddr (SCCBaseAddr y) (x, y)) (Set.fromList xs) acc
      )
      Map.empty
      ( -- trace
        -- (printf "newGraphSCCs: %s" (show newGraphSCCs))
        newGraphSCCs
      )
  newAddrToSCCAddr =
    Map.fromList
      [ (addr, rep)
      | (rep, addrs) <- Map.toList newSCCs
      , addr <- Set.toList addrs
      ]
  newSCCDAG =
    Map.map Set.toList $
      Map.foldrWithKey
        ( \src deps acc ->
            let srcSCCAddr = newAddrToSCCAddr `lookupMust` src
                depSCCAddrs = Set.fromList $ map (\dep -> newAddrToSCCAddr `lookupMust` trimToReferable dep) deps
                -- Remove the source SCC address from the dependent SCC addresses.
                -- This is because the source SCC address is not a dependency of itself.
                depSccAddrsWoSrc = Set.delete srcSCCAddr depSCCAddrs
             in Map.insertWith Set.union srcSCCAddr depSccAddrsWoSrc acc
        )
        Map.empty
        (ngNotifEdges graph)

scc :: (HasCallStack) => Map.Map TreeAddr [TreeAddr] -> [SCC]
scc edges = tsSCCs $ execState go initState
 where
  vertexes = Map.keys edges
  initState = emptyTarjanState edges

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
  , dnmSCyclicDesc :: Maybe TreeAddr
  -- ^ It contains the descendant address of the node that forms a structural cycle.
  }
  deriving (Show)

emptyTarjanNodeMeta :: TarjanNodeMeta
emptyTarjanNodeMeta = TarjanNodeMeta 0 0 False Nothing

data TarjanState = TarjanState
  { tsEdges :: Map.Map TreeAddr [TreeAddr]
  , tsIndex :: Int
  , tsStack :: [TreeAddr]
  , tsMetaMap :: Map.Map TreeAddr TarjanNodeMeta
  , tsSCCs :: [SCC]
  }

emptyTarjanState :: Map.Map TreeAddr [TreeAddr] -> TarjanState
emptyTarjanState edges =
  TarjanState edges 0 [] (Map.fromList $ map (\v -> (v, emptyTarjanNodeMeta)) (Map.keys edges)) []

data SCC
  = AcyclicSCC TreeAddr
  | CyclicSCC [TreeAddr]
  | -- | The pair is (descendant, ancestor).
    SCyclicSCC (TreeAddr, TreeAddr) [TreeAddr]
  deriving (Show)

{- | Perform a depth-first search to find strongly connected components (SCCs) using Tarjan's algorithm.

The input vertex is in the referable form.
-}
sccDFS :: (HasCallStack) => TreeAddr -> State TarjanState ()
sccDFS v = do
  modify $ \ts ->
    let index = tsIndex ts
        newIndex = index + 1
        newMeta =
          TarjanNodeMeta
            { dnmLowLink = newIndex
            , dnmIndex = newIndex
            , dnmOnStack = True
            , dnmSCyclicDesc = Nothing
            }
     in ts{tsIndex = newIndex, tsStack = v : tsStack ts, tsMetaMap = Map.insert v newMeta (tsMetaMap ts)}
  neighbors <- getNeighbors v
  forM_ neighbors $ \(rawW, isWPrefix) -> do
    let w = trimToReferable rawW
    -- If the neighbor is a prefix, mark it with v being its structural cycle descendant.
    when isWPrefix $ modify $ \ts ->
      let tm = tsMetaMap ts
          elemW = tm `lookupMust` w
          newMeta = elemW{dnmSCyclicDesc = Just v}
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
  -- (return ())
  when isRoot $ do
    modify $ \ts ->
      let (sccRestNodes, restStack) = span (/= v) (tsStack ts)
          newStack = tail restStack
          (newMetaMap, scM) =
            foldr
              ( \addr (accMM, accSCM) ->
                  ( Map.adjust (\m -> m{dnmOnStack = False}) addr accMM
                  , if isJust accSCM
                      then accSCM
                      else do
                        desc <- dnmSCyclicDesc $ accMM `lookupMust` addr
                        return (addr, desc)
                  )
              )
              (tsMetaMap ts, Nothing)
              (v : sccRestNodes)
          newSCC =
            if
              | null sccRestNodes
              , -- If the only address in the SCC leads to itself, it is a cyclic SCC.
                fromMaybe
                  False
                  ( do
                      dependents <- Map.lookup v (tsEdges ts)
                      return $ length dependents == 1 && trimToReferable (head dependents) == v
                  ) ->
                  CyclicSCC [v]
              | null sccRestNodes -> AcyclicSCC v
              | Just sc <- scM -> SCyclicSCC sc (v : sccRestNodes)
              | otherwise -> CyclicSCC (v : sccRestNodes)
       in ts
            { tsStack = newStack
            , tsMetaMap = newMetaMap
            , tsSCCs = newSCC : tsSCCs ts
            }

{- | Get the neighbors of a node in the notification graph.

Each of the neighbors is a tuple of the neighbor address and a boolean indicating whether the neighbor is an ancestor
of the input address.
-}
getNeighbors :: TreeAddr -> State TarjanState [(TreeAddr, Bool)]
getNeighbors v = do
  edges <- gets tsEdges
  return $ go v True edges []
 where
  -- start is True if the current address is the getNeighbor address.
  go x start edges acc
    | x == rootTreeAddr = acc
    | start =
        let newAcc = acc ++ maybe [] (map (\w -> (w, isPrefix w v))) (Map.lookup x edges)
         in go (fromJust (initTreeAddr x)) False edges newAcc
    | otherwise =
        let newAcc = acc ++ ([(x, True) | Map.member x edges])
         in go (fromJust (initTreeAddr x)) False edges newAcc

lookupMust :: (HasCallStack, Ord k, Show k, Show a) => Map.Map k a -> k -> a
lookupMust m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ printf "key %s not found in map %s" (show k) (show m)
