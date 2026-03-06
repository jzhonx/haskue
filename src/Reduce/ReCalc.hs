{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Recalc where

import Control.Monad (filterM, foldM, unless, void)
import Data.Foldable (toList)
import qualified Data.IntMap as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, maybeToList)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import DepGraph
import Feature
import {-# SOURCE #-} Reduce.Core (handleMutRes, reduce)
import Reduce.Monad (
  RCResolver (..),
  RM,
  RecalcItem (..),
  depGraph,
  emptyRCResolver,
  getRCResolver,
  getRMContext,
  mapRCResolver,
  modifyRMContext,
  putRMContext,
  recalcRootQ,
  withNoSignalReduced,
 )
import Reduce.Reference (select)
import Reduce.Store (fetchValFromStore, fetchValMust, propValUp, queryLastDerefedVal, storeVal, storeValUpToRoot)
import Reduce.Struct (handleSObjChange, validateStructPerm)
import Reduce.TraceSpan (
  debugInstText,
  emptySpanValue,
  traceSpanArgsTM,
  traceSpanTM,
  traceSpanValTM,
 )
import StringIndex (ShowWTIndexer (tshow))
import Text.Printf (printf)
import Util.Format (msprintf, packFmtA)
import Value

-- | Start re-calculation.
recalc :: RM ()
recalc = do
  q <- recalcRootQ <$> getRMContext
  debugInstText
    "recalc"
    rootValAddr
    ( do
        qT <- tshow (toList q)
        return $ T.pack $ printf "starting queue: %s" qT
    )

  traceSpanTM "recalc" rootValAddr emptySpanValue drainQ

sendToRootRecalcQ :: Bool -> ValAddr -> RM ()
sendToRootRecalcQ isReduced addr = createRecalcItem isReduced addr >>= flip pushToRecalcRootQ addr

createRecalcItem :: Bool -> ValAddr -> RM (Maybe RecalcItem)
createRecalcItem isReduced addr = do
  case addrIsRfbAddr addr of
    Nothing -> return Nothing
    Just rfbAddr -> do
      gAddr <- getRecalcGAddr (rfbAddrToSufIrred rfbAddr)
      return $ Just RecalcItem{addr, rfbAddr, grpAddr = gAddr, isReduced}

getRecalcGAddr :: SuffixIrredAddr -> RM GrpAddr
getRecalcGAddr siAddr = do
  ng <- depGraph <$> getRMContext
  let r = lookupGrpAddr siAddr ng
  case r of
    Just gAddr -> return gAddr
    -- If its gaddr can not be found, it means:
    -- 1) it does not depend on others
    -- 2) dependents have not been evaluated yet
    -- So it can not be an cyclic node.
    Nothing -> return $ GrpAddr (siAddr, False)

-- | Push the item to the recalculation root queue.
pushToRecalcRootQ :: Maybe RecalcItem -> ValAddr -> RM ()
pushToRecalcRootQ Nothing _ = return ()
pushToRecalcRootQ (Just item) _ = modifyRMContext $ \ctx -> ctx{recalcRootQ = recalcRootQ ctx Seq.|> item}

popRecalcRootQ :: RM (Maybe RecalcItem)
popRecalcRootQ = do
  ctx <- getRMContext
  case recalcRootQ ctx of
    Seq.Empty -> return Nothing
    (x Seq.:<| xs) -> do
      putRMContext ctx{recalcRootQ = xs}
      return (Just x)

drainQ :: RM ()
drainQ = do
  itemM <- popRecalcRootQ
  case itemM of
    Nothing -> return ()
    Just item -> do
      let gAddr = item.grpAddr
      state <-
        -- If the item is reduced and its gAddr is not acyclic, then it means we can generate the new RunState from the
        -- current item.
        if item.isReduced && not (snd $ getGrpAddr gAddr)
          then nextRunState gAddr Seq.empty
          else do
            g <- depGraph <$> getRMContext
            let qSetList = getNodeAddrsInGrp gAddr g
            return $ RunState{recalcQ = Seq.singleton gAddr, recalcQSet = Set.fromList qSetList}
      unless (Seq.null state.recalcQ) $ do
        recaclQT <- tshow (toList state.recalcQ)
        debugInstText
          "drainQ"
          rootValAddr
          (msprintf "new popped item: %s, recalcQ: %s" [packFmtA item, packFmtA recaclQT])
        run state

      drainQ

type ReCalcOrderState = (Set.Set SuffixIrredAddr, [GrpAddr])

{- | DNDiscRes stores ready strongly-connected components that are either reduced or ready to be reduced to notify
their dependents.
-}
data RunState = RunState
  { recalcQ :: Seq.Seq GrpAddr
  -- ^ The queue of GrpAddr for BFS traversal.
  , recalcQSet :: Set.Set ValAddr
  -- ^ The set of ValAddr in the queue for quick lookup.
  }

-- | Run the recalculation list in breadth-first manner.
run :: RunState -> RM ()
run state = case state.recalcQ of
  Seq.Empty -> return ()
  (cur Seq.:<| rest) -> do
    noFieldInQ <- hasNoFieldInQ cur state.recalcQSet
    if not noFieldInQ
      -- If there is a field of the current node in queue, we put it back to the end of the queue.
      -- The qSet remains the same since cur is still in the queue.
      then do
        debugInstText
          "drainQ"
          rootValAddr
          (msprintf "put back gAddr: %s to the end of the queue since there is field in the queue" [packFmtA cur])
        run state{recalcQ = rest Seq.|> cur}
      else do
        recalcGroup cur
        nextRunState cur rest >>= run

-- | Get the next RunState by disovering the neighbors of the current GrpAddr.
nextRunState :: GrpAddr -> Seq.Seq GrpAddr -> RM RunState
nextRunState cur restQ = do
  ng <- depGraph <$> getRMContext
  parentGrpAddrs <- getAncestorGrpAddrs cur
  let deps = cur : parentGrpAddrs
  nextGAddrs <-
    concat
      <$> mapM
        ( \dep -> do
            let depAddr = trimAddrToRfb (sufIrredToAddr $ fst $ getGrpAddr dep)
                uses = getUseGroups dep ng
            filterM
              ( \use -> do
                  useSIAddrs <- getCyclicGrpNodeAddrs use
                  foldM
                    ( \acc useSIAddr ->
                        -- If the use is a descendant of the dep, then it just represents a reference with selectors.
                        -- The use should be skipped.
                        if isPrefix (rfbAddrToAddr depAddr) (sufIrredToAddr useSIAddr)
                          then return False
                          else do
                            extVal <- fetchValMust "nextRunState" (rfbAddrToAddr depAddr)
                            lastDerefed <- queryLastDerefedVal useSIAddr depAddr
                            debugInstText
                              "nextRunState"
                              rootValAddr
                              ( do
                                  siaddrT <- tshow useSIAddr
                                  depAddrT <- tshow depAddr
                                  extV <- tshow extVal
                                  case lastDerefed of
                                    Nothing -> return $ T.pack $ printf "useAddr: %s, depAddr: %s, ext: %s, lastDerefed: Nothing" siaddrT depAddrT extV
                                    Just ld -> do
                                      ldSeen <- tshow ld
                                      return $ T.pack $ printf "useAddr: %s, depAddr: %s, ext: %s, lastDerefed: %s" siaddrT depAddrT extV ldSeen
                              )
                            return $ acc || Just extVal /= lastDerefed
                    )
                    False
                    useSIAddrs
              )
              uses
        )
        deps

  let
    (newQ, _) =
      foldr
        ( \x (qAcc, vAcc) ->
            if Set.member x vAcc
              then (qAcc, vAcc)
              else (qAcc Seq.|> x, Set.insert x vAcc)
        )
        (restQ, Set.fromList (toList restQ))
        nextGAddrs
    newQSet =
      foldr
        ( \item acc ->
            let nodes = getNodeAddrsInGrp item ng
             in foldr Set.insert acc nodes
        )
        Set.empty
        newQ
  return $
    RunState
      { recalcQ = newQ
      , recalcQSet = newQSet
      }

-- | Check whether there is no fields of structs specified by the GrpAddr in the given set.
hasNoFieldInQ :: GrpAddr -> Set.Set ValAddr -> RM Bool
hasNoFieldInQ gaddr qSet = case gaddr of
  IsAcyclicGrpAddr addr -> check (sufIrredToAddr addr)
  _ -> do
    epAddrs <- getCyclicGrpNodeAddrs gaddr
    foldM
      ( \acc siAddr -> do
          r <- check (sufIrredToAddr siAddr)
          return (acc && r)
      )
      True
      epAddrs
 where
  check addr = do
    let
      baseSIAddr = trimAddrToSufIrred addr
      baseAddr = sufIrredToAddr baseSIAddr
    -- First we need to go to the base irreducible address.
    -- The base address could not exist if the node is a sub RC.
    vM <- fetchValFromStore "hasNoFieldInQ" baseAddr
    case vM of
      Nothing -> return True
      Just v -> case v of
        -- If the current node is a struct, its tgen is a unify, and none of its mutable arguments is affected, then we
        -- only need to check whether the struct is ready to be used for validating its permissions.
        IsStruct struct
          | IsValMutable mut <- v
          , let
              -- If the node is an argument node, including a very deep argument in the comprehension.
              isArgChanged = addr /= baseAddr
          , Op (UOp _) <- mut
          , not isArgChanged -> do
              -- No argument affected, we can just check whether the struct is ready.
              checkSClean baseAddr qSet struct
          -- Same as above but for immutable tgen.
          | IsValImmutable <- v -> do
              checkSClean baseAddr qSet struct
        _ -> return True

getCyclicGrpNodeAddrs :: GrpAddr -> RM [SuffixIrredAddr]
getCyclicGrpNodeAddrs gaddr = do
  ng <- depGraph <$> getRMContext
  let
    compAddrs = getElemAddrInGrp gaddr ng
    epAddrs = removeChildSIAddrs compAddrs
  return epAddrs

-- | Check whether the struct is clean if all its affected leaves are clean.
checkSClean :: ValAddr -> Set.Set ValAddr -> Struct -> RM Bool
checkSClean baseAddr qSet struct = do
  let
    affectedSufIrredAddrsSet = Set.map trimAddrToSufIrred qSet
    affectedFieldSegs =
      [ mkStringFeature name
      | name <- Map.keys (stcFields struct)
      , let a = trimAddrToSufIrred $ appendSeg baseAddr (mkStringFeature name)
      , Set.member a affectedSufIrredAddrsSet
      ]
    affectedDynSegs =
      [ mkDynFieldFeature i 0
      | i <- IntMap.keys (stcDynFields struct)
      , let
          seg = mkDynFieldFeature i 0
          a = trimAddrToSufIrred $ appendSeg baseAddr seg
         in
          Set.member a affectedSufIrredAddrsSet
      ]
    affectedCnstrSegs =
      [ mkPatternFeature i 0
      | i <- IntMap.keys (stcCnstrs struct)
      , let
          seg = mkPatternFeature i 0
          a = trimAddrToSufIrred $ appendSeg baseAddr seg
         in
          Set.member a affectedSufIrredAddrsSet
      ]
    allAffected = affectedFieldSegs ++ affectedDynSegs ++ affectedCnstrSegs
  return $ null allAffected

recalcGroup :: GrpAddr -> RM ()
recalcGroup (IsAcyclicGrpAddr node) = recalcNode node
recalcGroup sccAddr = do
  -- In the intermediate steps of resolving RCs, we do not want to trigger recalculation of functions.
  -- TODO: what if the RC is a dynamic field or a constraint?
  withNoSignalReduced True $ do
    ng <- depGraph <$> getRMContext
    -- If any node in the SCC is a child of another node in the SCC, then it should be removed as it is a sub-field
    -- reference cycle, which should be handled specially.
    let
      compAddrs = getElemAddrInGrp sccAddr ng
      epAddrs = removeChildSIAddrs compAddrs

    traceSpanArgsTM
      "recalcCyclic"
      rootValAddr
      emptySpanValue
      ( const $ do
          compAddrStrs <- mapM tshow compAddrs
          epAddrStrs <- mapM tshow epAddrs
          return $ printf "compAddrs: %s, epAddrs: %s" (show compAddrStrs) (show epAddrStrs)
      )
      $ do
        store <-
          foldM
            ( \accStore siAddr -> do
                recalcRC siAddr
                -- We have to save the recalculated value to the store since it will be overwritten when we go to the
                -- next RC node.
                v <- fetchValMust "recalcGroup" (sufIrredToAddr siAddr)
                debugInstText
                  "recalcCyclic"
                  rootValAddr
                  (msprintf "recalcCyclic %s done, fetch done, v: %s" [packFmtA siAddr, packFmtA v])
                return (Map.insert siAddr v accStore)
            )
            Map.empty
            epAddrs

        -- We have to put back all the recalculated values because some of them could be overwritten during the process.
        mapM_
          (\(siAddr, t) -> storeValUpToRoot (sufIrredToAddr siAddr) t)
          (Map.toList store)

recalcRC :: SuffixIrredAddr -> RM ()
recalcRC siAddr = do
  mapRCResolver (const $ RCResolver{stack = [siAddr], doneRCAddrs = [], resolving = True})
  traceSpanTM "recalcRC" (sufIrredToAddr siAddr) emptySpanValue $ do
    recalcRCStack
  mapRCResolver (const emptyRCResolver)

-- | Calculate the reference cycle node given by the top of the stack.
recalcRCStack :: RM ()
recalcRCStack = do
  RCResolver{stack} <- getRCResolver
  case stack of
    [] -> return ()
    node : xs -> do
      recalcNode node
      RCResolver{stack = stack', doneRCAddrs} <- getRCResolver
      -- If the stack is growing, it means we discovered a new RC node during the reduction.
      if length stack' > length stack
        then recalcRCStack
        else do
          mapRCResolver $ \rs -> rs{stack = xs, doneRCAddrs = node : rs.doneRCAddrs}
          debugInstText
            "recalcRCStack"
            (sufIrredToAddr node)
            (msprintf "stack: %s, done: %s" [packFmtA (show xs), packFmtA (show $ node : doneRCAddrs)])
          recalcRCStack

{- | Re-calculate a single node given the dirty leaves and fetch function.

If a node is a struct and under certain conditions, we do not need to fully re-calculate it. We just need to check its
permissions.
-}
recalcNode :: SuffixIrredAddr -> RM ()
recalcNode nodeSIAddr = do
  let nodeAddr = sufIrredToAddr nodeSIAddr
  -- First we need to go to the base irreducible address.
  vM <- fetchValFromStore "recalcNode" nodeAddr
  case vM of
    Nothing -> return ()
    Just v -> void $ traceSpanValTM "recalcNode" nodeAddr v $ do
      g <- depGraph <$> getRMContext
      let
        nodes = getNodeAddrsByFunc nodeSIAddr g
        anyArgChanged = any (\a -> a /= nodeAddr) nodes
      nodesT <- mapM tshow nodes
      debugInstText
        "recalcNode"
        nodeAddr
        (msprintf "nodes: %s, anyArgChanged: %s" [packFmtA nodesT, packFmtA (show anyArgChanged)])
      case v of
        -- If the current node is a struct, its tgen is a unify, and none of its mutable arguments is affected, then we
        -- only need to check whether the struct is ready to be used for validating its permissions.
        IsStruct _
          | IsValMutable mut <- v
          , Op (UOp _) <- mut
          , -- No argument affected, we can just check whether the struct is ready.
            not anyArgChanged -> do
              r <- validateStructPerm nodeAddr v
              storeValUpToRoot nodeAddr r
              return r
          -- Same as above but for immutable tgen.
          | IsValImmutable <- v -> do
              r <- validateStructPerm nodeAddr v
              storeValUpToRoot nodeAddr r
              return r
        -- For mutable, list, disjunction, just re-calculate it.
        _ ->
          ( do
              r <- reduce nodeAddr v
              storeValUpToRootRecalc nodeAddr r
              return r
          )

-- | Store the value with the address and all its ancestors up to the root.
storeValUpToRootRecalc :: ValAddr -> Val -> RM ()
storeValUpToRootRecalc addr v = do
  storeVal addr v
  parentM <- propValUp addr v
  case parentM of
    Nothing -> return ()
    Just (pAddr, pVal) -> do
      newPVal <- case lastSeg addr of
        Just (FeatureType VSelectBaseLabelType)
          | IsVSelect sop vsel <- pVal -> do
              r <- select vsel pAddr pVal
              handleMutRes r False sop pAddr pVal
        _ -> handleSObjChange addr pVal >>= validateStructPerm pAddr
      storeValUpToRootRecalc pAddr newPVal

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
      (removeChildSIAddrs $ getElemAddrInGrp sccAddr ng)
  return $ reverse r

{- | Get the ancestor SCC address from the given address.

Since it is a tree address, there is only one ancestor for each address, meaning that the ancestor must be acyclic.
And because it is either a struct or a list.
-}
getAncGrpFromAddr :: SuffixIrredAddr -> Maybe GrpAddr
getAncGrpFromAddr raddr
  | rootValAddr == sufIrredToAddr raddr = Nothing
  | otherwise = do
      let parentAddr = fromJust $ initSufIrred raddr
      return (GrpAddr (parentAddr, False))
