{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Recalc where

import Control.Monad (filterM, foldM, unless, void, when)
import Data.Aeson (ToJSON (..))
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, maybeToList)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import DepGraph
import Feature
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
  withNoSignalReduced,
 )
import Reduce.Store (fetchValFromStore, fetchValMust, propValUp, queryLastDerefedVal, storeVal)
import Reduce.Struct (handleSObjChange, validateStructPerm, whenStruct)
import Reduce.TraceSpan (
  debugInstStr,
  emptySpanValue,
  traceSpanAdaptTM,
  traceSpanArgsTM,
  traceSpanTM,
  traceSpanTermsRepTM,
 )
import StringIndex (ShowWTIndexer (tshow))
import Text.Printf (printf)
import Util.Format (msprintfS, packFmtA)
import Value

-- | Start re-calculation.
recalc :: RM ()
recalc = do
  q <- rootRecalcQ <$> getRMContext
  debugInstStr
    "recalc"
    fileTopValAddr
    ( do
        qT <- tshow (toList q)
        return $ printf "starting queue: %s" qT
    )

  traceSpanTM "recalc" fileTopValAddr emptySpanValue drainQ

sendToRootRecalcQ :: ValAddr -> RM ()
sendToRootRecalcQ addr = do
  itemM <- createReducedSignal addr
  debugInstStr
    "sendToRootRecalcQ"
    addr
    ( do
        itemMT <- tshow itemM
        return $ printf "created item: %s" itemMT
    )
  case itemM of
    Nothing -> return ()
    Just item -> modifyRMContext $ \ctx -> ctx{rootRecalcQ = rootRecalcQ ctx Seq.|> item}

createReducedSignal :: ValAddr -> RM (Maybe ReducedSignal)
createReducedSignal addr = do
  case addrIsRfbAddr addr of
    Nothing -> return Nothing
    Just rfbAddr -> do
      gAddr <- vertexAddrToGrpAddr (rfbAddrToVertex rfbAddr)
      return $ Just ReducedSignal{addr, rfbAddr, grpAddr = gAddr}

vertexAddrToGrpAddr :: VertexAddr -> RM GrpAddr
vertexAddrToGrpAddr siAddr = do
  ng <- depGraph <$> getRMContext
  let r = lookupGrpAddr siAddr ng
  case r of
    Just gAddr -> return gAddr
    -- If its gaddr can not be found, it means:
    -- 1) it does not depend on others
    -- 2) dependents have not been evaluated yet
    -- So it can not be an cyclic node.
    Nothing -> return $ GrpAddr (siAddr, False)

popRootRecalcQ :: RM (Maybe ReducedSignal)
popRootRecalcQ = do
  ctx <- getRMContext
  case rootRecalcQ ctx of
    Seq.Empty -> return Nothing
    (x Seq.:<| xs) -> do
      putRMContext ctx{rootRecalcQ = xs}
      return (Just x)

drainQ :: RM ()
drainQ = do
  itemM <- popRootRecalcQ
  stop <- traceSpanArgsTM
    "drainQ"
    fileTopValAddr
    emptySpanValue
    ( do
        restQ <- rootRecalcQ <$> getRMContext
        itemMT <- tshow itemM
        restQT <- tshow (toList restQ)
        return $ printf "popped item: %s, restQ: %s" itemMT (show restQT)
    )
    $ case itemM of
      Nothing -> return True
      Just item -> do
        let gAddr = item.grpAddr
        next <-
          -- If the item is reduced and its gAddr is not acyclic, then it means we can generate the new BFSState from the
          -- current item.
          if not (snd $ getGrpAddr gAddr)
            then findNeighbors gAddr Seq.empty
            else mkCyclicBFSState item
        unless (Seq.null next.bfsQ) $ do
          rsQT <- tshow (toList next.bfsQ)
          debugInstStr
            "drainQ"
            fileTopValAddr
            (msprintfS "new popped item: %s, bfsQ: %s" [packFmtA item, packFmtA rsQT])
          runBFS next
        return False

  unless stop drainQ

mkCyclicBFSState :: ReducedSignal -> RM BFSState
mkCyclicBFSState item = traceSpanAdaptTM
  "mkCyclicBFSState"
  item.addr
  emptySpanValue
  (const emptySpanValue)
  $ do
    let itemCanAddr = rfbAddrToVertex item.rfbAddr
    recalcRC itemCanAddr
    g <- depGraph <$> getRMContext
    let
      elems = getElemAddrInGrp item.grpAddr g
      elemsExcludeSelf = filter (/= itemCanAddr) elems
    hasDirty <-
      foldM
        ( \acc elemCanAddr -> do
            dirty <- checkIfDirty item.rfbAddr elemCanAddr
            return $ acc || dirty
        )
        False
        elemsExcludeSelf
    -- TODO: use the hasDirty
    return $ appendAddrsToBFSQ [item.grpAddr] Seq.empty g

-- | BFSState for the breadth-first traversal of the recalculation.
data BFSState = BFSState
  { bfsQ :: Seq.Seq GrpAddr
  -- ^ The queue of GrpAddr for BFS traversal.
  , bfsQNodesSet :: Set.Set ValAddr
  -- ^ The set of ValAddr in the queue for quick lookup.
  }

-- | Run the recalculation list in breadth-first manner.
runBFS :: BFSState -> RM ()
runBFS state = case state.bfsQ of
  Seq.Empty -> return ()
  (cur Seq.:<| rest) -> do
    recalcGroup cur
    updated' <- vertexAddrToGrpAddr (fst $ getGrpAddr cur)
    -- If the updated gAddr is different from the current gAddr, it means the current gAddr is changed during the
    -- recalculation. The cause could be a new cycle discovered during the recalculation.
    -- In that case, we need to re-calculate the current gAddr.
    when (updated' /= cur) $ do
      debugInstStr
        "runBFS"
        fileTopValAddr
        ( do
            curT <- tshow cur
            updated'T <- tshow updated'
            return $ printf "current gAddr %s is updated to %s during recalculation, need to recalculate it again" curT updated'T
        )
      recalcGroup updated'
    findNeighbors updated' rest >>= runBFS

{- | Get the next BFSState by disovering the neighbors of the current GrpAddr.

Neighbors are dependents of the current GrpAddr and all of its ancestors.
-}
findNeighbors :: GrpAddr -> Seq.Seq GrpAddr -> RM BFSState
findNeighbors cur restBFSQ = traceSpanAdaptTM
  "findNeighbors"
  fileTopValAddr
  emptySpanValue
  ( \a -> do
      nextQ <- mapM tshow (toList a.bfsQ)
      let
        msg :: String
        msg = printf "next bfsQ: %s" (show nextQ)
      return $ toJSON msg
  )
  $ do
    ng <- depGraph <$> getRMContext
    parentGrpAddrs <- getAncestorGrpAddrs cur
    let deps = cur : parentGrpAddrs
    nextGAddrs <-
      concat
        <$> mapM
          ( \dep -> do
              let depAddr = trimCanonicalToRfb (getVertexAddr $ fst $ getGrpAddr dep)
                  uses = getUseGroups dep ng
              filterAffectedUses depAddr uses
          )
          deps

    debugInstStr
      "findNeighbors"
      fileTopValAddr
      ( do
          curT <- tshow cur
          depsT <- mapM tshow deps
          nextGAddrsT <- mapM tshow nextGAddrs
          return $ printf "current gAddr: %s, deps: %s, next gAddrs: %s" curT (show depsT) (show nextGAddrsT)
      )

    let next = appendAddrsToBFSQ nextGAddrs restBFSQ ng
    return next

filterAffectedUses :: ReferableAddr -> [GrpAddr] -> RM [GrpAddr]
filterAffectedUses depAddr =
  filterM
    ( \use -> do
        useCanAddrs <- getCyclicGrpNodeAddrs use
        foldM
          ( \acc useCanAddr -> do
              dirty <- checkIfDirty depAddr useCanAddr
              return $ acc || dirty
          )
          False
          useCanAddrs
    )

checkIfDirty :: ReferableAddr -> VertexAddr -> RM Bool
checkIfDirty depAddr useCanAddr = do
  extVal <- fetchValMust "checkIfDirty" (rfbAddrToAddr depAddr)
  lastDerefed <- queryLastDerefedVal useCanAddr depAddr
  debugInstStr
    "checkIfDirty"
    fileTopValAddr
    ( do
        siaddrT <- tshow useCanAddr
        depAddrT <- tshow depAddr
        extValT <- tshow extVal
        case lastDerefed of
          Nothing -> return $ printf "useAddr: %s, depAddr: %s, ext: %d, lastDerefed: Nothing" siaddrT depAddrT extVal.version
          Just ld -> do
            ldSeen <- tshow ld
            return $
              printf
                "useAddr: %s, depAddr: %s, ext version: %d, ext val: %s, lastDerefed: %s"
                siaddrT
                depAddrT
                extVal.version
                extValT
                ldSeen
    )
  return $ Just extVal.version /= lastDerefed

appendAddrsToBFSQ :: [GrpAddr] -> Seq.Seq GrpAddr -> DepGraph -> BFSState
appendAddrsToBFSQ addrs restBFSQ ng =
  let
    (newQ, _) =
      foldr
        ( \x (qAcc, vAcc) ->
            if Set.member x vAcc
              then (qAcc, vAcc)
              else (qAcc Seq.|> x, Set.insert x vAcc)
        )
        (restBFSQ, Set.fromList (toList restBFSQ))
        addrs
    newQSet =
      foldr
        ( \item acc ->
            let nodes = getNodeAddrsInGrp item ng
             in foldr Set.insert acc nodes
        )
        Set.empty
        newQ
   in
    BFSState
      { bfsQ = newQ
      , bfsQNodesSet = newQSet
      }

getCyclicGrpNodeAddrs :: GrpAddr -> RM [VertexAddr]
getCyclicGrpNodeAddrs gaddr = do
  ng <- depGraph <$> getRMContext
  let compAddrs = getElemAddrInGrp gaddr ng
  return compAddrs

recalcGroup :: GrpAddr -> RM ()
recalcGroup (IsAcyclicGrpAddr node) = recalcNode node
recalcGroup sccAddr = do
  -- TODO: what if the RC is a dynamic field or a constraint?
  ng <- depGraph <$> getRMContext
  -- If any node in the SCC is a child of another node in the SCC, then it should be removed as it is a sub-field
  -- reference cycle, which should be handled specially.
  let compAddrs = getElemAddrInGrp sccAddr ng

  traceSpanArgsTM
    "recalcCyclic"
    fileTopValAddr
    emptySpanValue
    ( do
        compAddrStrs <- mapM tshow compAddrs
        return $ printf "compAddrs: %s" (show compAddrStrs)
    )
    $ do
      store <-
        foldM
          ( \accStore siAddr -> do
              recalcRC siAddr
              -- We have to save the recalculated value to the store since it will be overwritten when we go to the
              -- next RC node.
              v <- fetchValMust "recalcGroup" (vertexToAddr siAddr)
              debugInstStr
                "recalcCyclic"
                fileTopValAddr
                (msprintfS "recalcCyclic %s done, fetch done, v: %s" [packFmtA siAddr, packFmtA v])
              return (Map.insert siAddr v accStore)
          )
          Map.empty
          compAddrs

      -- We have to put back all the recalculated values because some of them could be overwritten during the process.
      mapM_
        (\(siAddr, t) -> storeValUpToRootRecalc (vertexToAddr siAddr) t)
        (Map.toList store)

recalcRC :: VertexAddr -> RM ()
recalcRC siAddr = do
  mapRCResolver (const $ RCResolver{stack = [siAddr], doneRCAddrs = [], resolving = True})
  traceSpanTM "recalcRC" (vertexToAddr siAddr) emptySpanValue recalcRCStack
  mapRCResolver (const emptyRCResolver)

-- | Calculate the reference cycle node given by the top of the stack.
recalcRCStack :: RM ()
recalcRCStack = do
  RCResolver{stack} <- getRCResolver
  case stack of
    [] -> return ()
    node : xs -> do
      -- Reducing each RC node should make the effect visible globally, so we call recalcNode for each of them.
      recalcNode node
      RCResolver{stack = stack', doneRCAddrs} <- getRCResolver
      -- If the stack is growing, it means we discovered a new RC node during the reduction.
      if length stack' > length stack
        then recalcRCStack
        else do
          mapRCResolver $ \rs -> rs{stack = xs, doneRCAddrs = node : rs.doneRCAddrs}
          debugInstStr
            "recalcRCStack"
            (vertexToAddr node)
            (msprintfS "stack: %s, done: %s" [packFmtA (show xs), packFmtA (show $ node : doneRCAddrs)])
          recalcRCStack

-- | Re-calculate a single node.
recalcNode :: VertexAddr -> RM ()
recalcNode nodeVAddr = do
  let nodeAddr = topReducerToAddr $ trimVertexToTopReducerAddr nodeVAddr
  vM <- fetchValFromStore "recalcNode" nodeAddr
  case vM of
    Nothing -> return ()
    Just v -> void $ traceSpanTermsRepTM "recalcNode" nodeAddr v $ do
      -- We do not need to signal reduced as now everything is driven by the recalculation.
      r <- withNoSignalReduced True $ reduce nodeAddr v
      -- We have to propagate the change up to the root to make the change effect globally visible.
      storeValUpToRootRecalc nodeAddr r
      return r

{- | Store the value with the address and all its ancestors up to the root.

It can add new values to the RootRecalcQ.
-}
storeValUpToRootRecalc :: ValAddr -> VNode -> RM ()
storeValUpToRootRecalc addr v = do
  storeVal addr v
  parentM <- propValUp addr v
  case parentM of
    Nothing -> return ()
    Just (pAddr, parVN) -> do
      parVN' <- case value parVN of
        VDisj d -> normalizeDisj addr d
        _ -> handleSObjChange addr (value parVN) >>= whenStruct (validateStructPerm pAddr)
      storeValUpToRootRecalc pAddr (setVNodeValue parVN' parVN)

{- | Get the ancestor GrpAddrs of the given GrpAddr.

It handles the case that the cyclic group may contain structural cycles.
-}
getAncestorGrpAddrs :: GrpAddr -> RM [GrpAddr]
getAncestorGrpAddrs (IsAcyclicGrpAddr addr) = do
  let rM = getAncGrpFromAddr addr
  return $ maybeToList rM
getAncestorGrpAddrs sccAddr = do
  ng <- depGraph <$> getRMContext
  r <-
    foldM
      ( \acc addr -> do
          let rM = getAncGrpFromAddr addr
          return $ maybe acc (: acc) rM
      )
      []
      (getElemAddrInGrp sccAddr ng)
  return $ reverse r

{- | Get the ancestor SCC address from the given address.

Since it is a tree address, there is only one ancestor for each address, meaning that the ancestor must be acyclic.
And because it is either a struct or a list.
-}
getAncGrpFromAddr :: VertexAddr -> Maybe GrpAddr
getAncGrpFromAddr raddr
  | fileTopValAddr == vertexToAddr raddr = Nothing
  | otherwise = do
      let parentAddr =
            topReducerToVertexAddr $
              fromJust $
                initTopReducer $
                  trimVertexToTopReducerAddr raddr
      return (GrpAddr (parentAddr, False))

topReducerToVertexAddr :: TopReducerAddr -> VertexAddr
topReducerToVertexAddr (TopReducerAddr c) = VertexAddr c
