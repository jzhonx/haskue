{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Recalc where

import Control.Monad (foldM, when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.Reader (local)
import Data.Aeson (toJSON)
import qualified Data.IntMap as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust, isNothing, maybeToList)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import NotifGraph
import Path
import Reduce.Nodes (validateStructPerm)
import Reduce.RMonad (
  Error (..),
  Fetch,
  FetchResult (..),
  HasReduceParams (..),
  ReduceMonad,
  ResolveMonad,
  ctxNotifGraph,
  debugInstantTM,
  debugSpanAdaptTM,
  debugSpanArgsAdaptTM,
  debugSpanTM,
  fetch,
  getRMContext,
  getTMAbsAddr,
  getTMTree,
  goTMAbsAddrMust,
  inRemoteTM,
  isRecalcing,
  modifyRMContext,
  popRecalcRootQ,
  pushRecalcRootQ,
  putTMTree,
  setIsReducingRC,
 )
import {-# SOURCE #-} Reduce.Root (reduce)
import Text.Printf (printf)
import Value

-- | Start re-calculation from the current focus.
recalc :: (ReduceMonad r s m) => m ()
recalc = do
  ctx <- getRMContext
  origAddr <- getTMAbsAddr
  -- We only proceed if we did not start notification yet and the current address is part of the notification graph.
  -- The address should be able to be translated to SuffixIrredAddr.
  let ng = ctxNotifGraph ctx
  startGrpAddrM <- case lookupGrpAddr (trimAddrToSufIrred origAddr) ng of
    Just gAddr | not (isRecalcing ctx) -> return $ Just gAddr
    _ -> return Nothing

  debugInstantTM "recalc" (printf "startGrpAddrM %s, ng: %s" (show startGrpAddrM) (show ng))

  when (isJust startGrpAddrM) $ debugSpanTM "recalc" $ do
    modifyRMContext $ \c -> c{isRecalcing = True}
    let startGrpAddr = fromJust startGrpAddrM
    pushRecalcRootQ startGrpAddr
    recalcRoot (origAddr, startGrpAddr)

    goTMAbsAddrMust origAddr
    -- For the starting point, there is no need to reduce it since it must have been reduced before calling
    -- recalc. Also, we should not add its ancestors since its parent is still reducing.
    -- Reset the context to not notifying.
    modifyRMContext $ \c -> c{isRecalcing = False}

recalcRoot :: (ReduceMonad r s m) => (TreeAddr, GrpAddr) -> m ()
recalcRoot start = do
  gAddrM <- popRecalcRootQ
  case gAddrM of
    Nothing -> return ()
    Just gAddr -> do
      res <-
        findDirtyNodes
          start
          (DNQueryRes (Seq.singleton gAddr) (Set.singleton gAddr) Seq.empty Map.empty)
      debugInstantTM
        "recalcRoot"
        (printf "order: %s, allAffected: %s" (show res.order) (showAllDirtyNodes res.allDirtyNodes))
      ng <- ctxNotifGraph <$> getRMContext
      runOrder
        res.allDirtyNodes
        res.order
        ( foldr
            (\x acc -> foldr Set.insert acc (getElemAddrInGrp x ng))
            Set.empty
            res.order
        )
      recalcRoot start

type ReCalcOrderState = (Set.Set SuffixIrredAddr, [GrpAddr])

runOrder ::
  (ReduceMonad r s m) =>
  Map.Map GrpAddr DirtyNodes ->
  Seq.Seq GrpAddr ->
  Set.Set SuffixIrredAddr ->
  m ()
runOrder _ Seq.Empty _ = return ()
runOrder allAffected (sccAddr Seq.:<| xs) orderSet = do
  rE <- recalcGroup sccAddr orderSet allAffected
  ng <- ctxNotifGraph <$> getRMContext
  case rE of
    Just dep -> do
      let depSCC = fromJust $ lookupGrpAddr dep ng
      debugInstantTM
        "runOrder"
        (printf "dep %s is dirty, put %s next, %s is put to the end" (show dep) (show depSCC) (show sccAddr))
      runOrder allAffected ((depSCC Seq.<| xs) Seq.|> sccAddr) orderSet
    Nothing ->
      runOrder
        allAffected
        xs
        (foldr Set.delete orderSet (getElemAddrInGrp sccAddr ng))

recalcGroup ::
  (ReduceMonad r s m) => GrpAddr -> Set.Set SuffixIrredAddr -> Map.Map GrpAddr DirtyNodes -> m (Maybe SuffixIrredAddr)
recalcGroup (ACyclicGrpAddr addr) dirtySet allAffected =
  recalcNode
    addr
    (createAffectedSet allAffected)
    (\k -> if Set.member k dirtySet then FRDirty else FRNormal)
recalcGroup sccAddr@(CyclicBaseAddr _) dirtySet allAffected = do
  setIsReducingRC True

  ng <- ctxNotifGraph <$> getRMContext
  let addrs = getElemAddrInGrp sccAddr ng
  r <- debugSpanArgsAdaptTM "recalcCyclic" (printf "addrs: %s" (show addrs)) (const $ toJSON ()) $ do
    (r, store) <-
      foldM
        ( \(acc, accStore) siAddr -> case acc of
            Just _ -> return (acc, accStore)
            Nothing ->
              do
                goTMAbsAddrMust (sufIrredToAddr siAddr)
                r <-
                  debugSpanAdaptTM (printf "recalcCyclic %s" (show siAddr)) (\r -> toJSON (show r)) $
                    recalcRC
                      (RCCalHelper allAffected addrs [siAddr] [])
                      (\k -> if Set.member k dirtySet then FRDirty else FRNormal)
                -- We have to save the recalculated value to the store since it will be overwritten when we go to the
                -- next RC node.
                v <- inRemoteTM (sufIrredToAddr siAddr) getTMTree
                debugInstantTM "recalcCyclic" (printf "recalcCyclic %s done, fetch done, v: %s" (show siAddr) (show v))
                return (r, Map.insert siAddr v accStore)
        )
        (Nothing, Map.empty)
        (removeParentSIAddrs addrs)

    -- We have to put back all the recalculated values because some of them could be overwritten during the process.
    mapM_ (\(siAddr, t) -> inRemoteTM (sufIrredToAddr siAddr) (putTMTree t)) (Map.toList store)
    return r

  setIsReducingRC False

  return r

-- | Create a sub dirty set for the given SuffixIrredAddr in the given GrpAddr.
createAffectedSet :: Map.Map GrpAddr DirtyNodes -> Set.Set TreeAddr
createAffectedSet allAffected =
  foldr
    ( \dn acc -> foldr Set.insert acc (concat $ Map.elems dn)
    )
    Set.empty
    (Map.elems allAffected)

data RCCalHelper = RCCalHelper
  { allAffected :: Map.Map GrpAddr DirtyNodes
  , rcAddrs :: [SuffixIrredAddr]
  , onStack :: [SuffixIrredAddr]
  , doneRCAddrs :: [SuffixIrredAddr]
  }

-- | Calculate the reference cycle node given by the top of the onStack.
recalcRC :: (ReduceMonad r s m) => RCCalHelper -> Fetch -> m (Maybe SuffixIrredAddr)
recalcRC RCCalHelper{onStack = []} _ = return Nothing
recalcRC h@RCCalHelper{onStack = node : xs} fetch = do
  goTMAbsAddrMust (sufIrredToAddr node)
  let nodeHasChildOnStack = filter (isSufIrredParent node) xs
  r <-
    if null nodeHasChildOnStack
      then
        recalcNode
          node
          (createAffectedSet h.allAffected)
          ( \k ->
              let kOnStack = k `elem` h.onStack
               in if
                    -- OnStack must precede fetch since at the same time all cycle nodes are dirty, which would
                    -- incorrectly raise error.
                    | kOnStack -> if kToTopHasParChildRel k h.onStack then FRSCyclic else FRCyclic
                    -- DoneRCAddrs are still marked as dirty in the dirtSet, we have to return FRNormal to let
                    -- locateRef fetch the latest value.
                    | k `elem` h.doneRCAddrs ->
                        if pathHasParChildRel (k : h.onStack) then FRSCyclic else FRNormal
                    | otherwise -> fetch k
          )
      else return Nothing
  debugInstantTM
    (printf "recalcRC %s" (show node))
    ( printf
        "stack: %s, nodeHasChildOnStack: %s, done: %s, r: %s"
        (show h.onStack)
        (show nodeHasChildOnStack)
        (show h.doneRCAddrs)
        (show r)
    )
  case r of
    Just dep
      -- If the dependency is not part of the current SCC, then we return it to the upper level to handle.
      | dep `notElem` h.rcAddrs -> return $ Just dep
      -- If the dependency is part of the current SCC, we push it to the stack and continue to recalculate it.
      | otherwise -> recalcRC h{onStack = dep : h.onStack} fetch
    Nothing ->
      recalcRC
        h{onStack = xs, doneRCAddrs = node : h.doneRCAddrs}
        fetch

pathHasParChildRel :: [SuffixIrredAddr] -> Bool
pathHasParChildRel path = any isParentOfAny path
 where
  isParentOfAny a = any (\x -> isSufIrredParent a x) path

kToTopHasParChildRel :: SuffixIrredAddr -> [SuffixIrredAddr] -> Bool
kToTopHasParChildRel k onStack =
  -- Find the path from k to the top of the stack.
  -- Reverse the stack to make bottom element first to make dropping easier.
  let path = dropWhile (/= k) (reverse onStack)
   in -- For any given node x in the path, check if any other node in the path is its parent.
      pathHasParChildRel path

recalcNode ::
  (ReduceMonad r s m) => SuffixIrredAddr -> Set.Set TreeAddr -> Fetch -> m (Maybe SuffixIrredAddr)
recalcNode addr affectedAddrsSet fetch = do
  let baseAddr = sufIrredToAddr addr
  goTMAbsAddrMust baseAddr
  debugSpanArgsAdaptTM
    "recalcNode"
    (printf "affectedAddrsSet: %s" (show affectedAddrsSet))
    ( \r -> case r of
        -- Just dep -> toJSON $ sufIrredToAddr dep
        Just dep -> toJSON ()
        Nothing -> toJSON ()
    )
    $ do
      let withDirtyCheck = local (modifyReduceParams (\p -> p{fetch}))
      t <- getTMTree
      readyM <- case t of
        -- If the current node is a struct, its tgen is a unify, and none of its mutable arguments is affected, then we
        -- can incrementally update it.
        IsStruct struct
          | IsTGenOp mut <- t
          , let
              allArgAddrs = map (\i -> appendSeg baseAddr (MutArgTASeg i)) [0 .. length (getMutArgs mut) - 1]
              anyArgAffected = any (`Set.member` affectedAddrsSet) allArgAddrs
          , MutOp (UOp _) <- mut
          , not anyArgAffected -> do
              rM <- checkSReady baseAddr affectedAddrsSet fetch struct
              when (isNothing rM) validateStructPerm
              return rM
          -- If the current node is a struct, its tgen is immutable, then we can apply the incremental update.
          | IsTGenImmutable <- t -> do
              rM <- checkSReady baseAddr affectedAddrsSet fetch struct
              when (isNothing rM) validateStructPerm
              return rM
        -- For mutable, list, disjunction, just re-calculate it.
        _ -> do
          withDirtyCheck (reduce >> return Nothing)
            `catchError` ( \case
                            DirtyDep dep -> return $ Just dep
                            e -> throwError e
                         )

      case readyM of
        Just dep -> return $ Just dep
        Nothing -> do
          return Nothing

-- | Incrementally update the struct at the given address.
checkSReady ::
  (ReduceMonad r s m) => TreeAddr -> Set.Set TreeAddr -> Fetch -> Struct -> m (Maybe SuffixIrredAddr)
checkSReady baseAddr affectedAddrsSet fetch struct = do
  let
    affectedSufIrredAddrsSet = Set.map trimAddrToSufIrred affectedAddrsSet
    affectedFieldSegs =
      [ StringTASeg name
      | name <- Map.keys (stcFields struct)
      , let a = trimAddrToSufIrred $ appendSeg baseAddr (BlockTASeg $ StringTASeg name)
      , Set.member a affectedSufIrredAddrsSet
      ]
    affectedDynSegs =
      [ DynFieldTASeg i 0
      | i <- IntMap.keys (stcDynFields struct)
      , let
          seg = BlockTASeg $ DynFieldTASeg i 0
          a = trimAddrToSufIrred $ appendSeg baseAddr seg
         in
          Set.member a affectedSufIrredAddrsSet
      ]
    affectedCnstrSegs =
      [ PatternTASeg i 0
      | i <- IntMap.keys (stcCnstrs struct)
      , let
          seg = BlockTASeg $ PatternTASeg i 0
          a = trimAddrToSufIrred $ appendSeg baseAddr seg
         in
          Set.member a affectedSufIrredAddrsSet
      ]
    allAffected = affectedFieldSegs ++ affectedDynSegs ++ affectedCnstrSegs
    deps =
      map
        (\seg -> let a = appendSeg baseAddr (BlockTASeg seg) in (trimAddrToSufIrred a, fetch (trimAddrToSufIrred a)))
        allAffected
    allClean = all (\x -> snd x == FRNormal) deps
  if allClean
    then do
      debugInstantTM "checkSReady" (printf "allAffected: %s" (show allAffected))
      return Nothing
    else do
      let dirtyAddrs = map fst $ filter (\(_, v) -> v /= FRNormal) deps
      return $ Just $ head dirtyAddrs

type DirtyNodes = Map.Map SuffixIrredAddr [TreeAddr]

addrsToDirtyNodes :: [TreeAddr] -> DirtyNodes
addrsToDirtyNodes =
  foldr
    ( \addr acc ->
        let iraddr = trimAddrToSufIrred addr
         in Map.insertWith (++) iraddr [addr] acc
    )
    Map.empty

{- | DNQueryRes stores ready strongly-connected components that are either reduced or ready to be reduced to notify
their dependents.
-}
data DNQueryRes = DNQueryRes
  { q :: Seq.Seq GrpAddr
  , visited :: Set.Set GrpAddr
  , order :: Seq.Seq GrpAddr
  , allDirtyNodes :: Map.Map GrpAddr DirtyNodes
  }

showAllDirtyNodes :: Map.Map GrpAddr DirtyNodes -> String
showAllDirtyNodes allDirtyNodes = show $ Map.toList $ Map.map Map.toList allDirtyNodes

findDirtyNodes :: (ResolveMonad r s m) => (TreeAddr, GrpAddr) -> DNQueryRes -> m DNQueryRes
findDirtyNodes (startAddr, startGrpAddr) state = do
  ng <- ctxNotifGraph <$> getRMContext
  case state.q of
    Seq.Empty -> return state
    (nodeGrpAddr Seq.:<| xs) -> do
      parentGrpAddrs <- getAncestorGrpAddrs startAddr nodeGrpAddr
      let
        depGrpAddrs = getDependentGroups nodeGrpAddr ng
        (newQ, newVisited) =
          foldr
            ( \sccAddr (qAcc, vAcc) ->
                if Set.member sccAddr vAcc
                  then (qAcc, vAcc)
                  else (qAcc Seq.|> sccAddr, Set.insert sccAddr vAcc)
            )
            (xs, state.visited)
            (depGrpAddrs ++ parentGrpAddrs)
        allDepts = getDependentsFromGroup nodeGrpAddr ng

      findDirtyNodes
        (startAddr, startGrpAddr)
        state
          { q = newQ
          , visited = newVisited
          , -- Only add to the order if it is not the starting GrpAddr and it is acyclic.
            -- If it is cyclic, then we need to re-calculate all its members together, which was not done in regular
            -- reduce.
            order =
              case nodeGrpAddr of
                ACyclicGrpAddr _ | nodeGrpAddr == startGrpAddr -> state.order
                _ -> state.order Seq.|> nodeGrpAddr
          , allDirtyNodes =
              Map.insert
                nodeGrpAddr
                (addrsToDirtyNodes allDepts)
                state.allDirtyNodes
          }

{- | Get the ancestor Group addresses of the given GrpAddr.

It handles the case that the cyclic group may contain structural cycles.
-}
getAncestorGrpAddrs :: (ResolveMonad r s m) => TreeAddr -> GrpAddr -> m [GrpAddr]
getAncestorGrpAddrs startAddr (ACyclicGrpAddr addr) = do
  let rM = getAncSCCFromAddr startAddr addr
  return $ maybeToList rM
getAncestorGrpAddrs startAddr sccAddr@(CyclicBaseAddr _) = do
  ng <- ctxNotifGraph <$> getRMContext
  r <-
    foldM
      ( \acc addr -> do
          let rM = getAncSCCFromAddr startAddr addr
          return $ maybe acc (: acc) rM
      )
      []
      (removeChildSIAddrs $ getElemAddrInGrp sccAddr ng)
  return $ reverse r

{- | Get the ancestor SCC address from the given address.

Since it is a tree address, there is only one ancestor for each address, meaning that the ancestor must be acyclic.
And because it is either a struct or a list.
-}
getAncSCCFromAddr :: TreeAddr -> SuffixIrredAddr -> Maybe GrpAddr
getAncSCCFromAddr startAddr raddr
  | rootTreeAddr == sufIrredToAddr raddr = Nothing
  | otherwise = do
      let parentAddr = fromJust $ initSufIrred raddr
      -- We should not add the ancestors that are above the starting address of the notification.
      -- The new parent should not be a starting address either.
      if isPrefix (sufIrredToAddr parentAddr) startAddr
        then Nothing
        else Just (ACyclicGrpAddr parentAddr)
