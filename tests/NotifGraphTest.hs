module NotifGraphTest where

import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import NotifGraph
import Path
import System.Directory (listDirectory)
import System.IO (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf (printf)

ngTests :: IO TestTree
ngTests =
  return $
    testGroup
      "ngtests"
      [ testACyclic
      , testCyclic
      , testCyclic2
      , testCyclic3
      , testCyclicSelf
      , testCyclicSelf2
      , testCyclicSelf3
      , testSCyclic
      , testSCyclic2
      , testSCyclic3
      , testSCyclic4
      ]

buildAbsTA :: String -> SuffixIrredAddr
buildAbsTA path = fromJust $ addrIsSufIrred $ appendTreeAddr rootTreeAddr (addrFromString path)

absA, absAX, absAXY, absB, absC, absY :: SuffixIrredAddr
absA = buildAbsTA "a"
absAX = buildAbsTA "a.x"
absAXY = buildAbsTA "a.x.y"
absB = buildAbsTA "b"
absC = buildAbsTA "c"
absY = buildAbsTA "y"

irredToRef :: SuffixIrredAddr -> SuffixReferableAddr
irredToRef a = fromJust $ sufIrredIsSufRef a

buildG :: [(SuffixIrredAddr, SuffixIrredAddr)] -> NotifGraph
buildG =
  foldr
    ( \(dep, target) acc ->
        addNewDepToNGNoUpdate
          (sufIrredToAddr dep, fromJust $ sufIrredIsSufRef target)
          acc
    )
    emptyNotifGraph

buildGExt :: [(TreeAddr, SuffixIrredAddr)] -> NotifGraph
buildGExt =
  foldr
    ( \(dep, target) acc ->
        addNewDepToNGNoUpdate
          (dep, fromJust $ sufIrredIsSufRef target)
          acc
    )
    emptyNotifGraph

testACyclic :: TestTree
testACyclic =
  testCase "acyclic_scc" $ do
    -- {a: b, b: c, a: x: c}
    let graph = buildG [(absA, absB), (absB, absC), (absAX, absC)]
        newGraph = updateNotifGraph graph
        sccs = sccMap newGraph
    assertEqual
      "sccs"
      ( Map.fromList
          [ (ACyclicGrpAddr absA, Set.singleton absA)
          , (ACyclicGrpAddr absB, Set.singleton absB)
          , (ACyclicGrpAddr absC, Set.singleton absC)
          , (ACyclicGrpAddr absAX, Set.singleton absAX)
          ]
      )
      sccs
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, ACyclicGrpAddr absA)
          , (absB, ACyclicGrpAddr absB)
          , (absC, ACyclicGrpAddr absC)
          , (absAX, ACyclicGrpAddr absAX)
          ]
      )
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      ( Map.fromList
          [ (ACyclicGrpAddr absB, [ACyclicGrpAddr absA])
          , (ACyclicGrpAddr absC, [ACyclicGrpAddr absAX, ACyclicGrpAddr absB])
          ]
      )
      (dagEdges newGraph)

testCyclic :: TestTree
testCyclic =
  testCase "cyclic_scc" $ do
    -- {a: b, b: c, c: a}
    let graph = buildG [(absA, absB), (absB, absC), (absC, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
        sccs = sccMap newGraph
    assertEqual
      "sccs"
      ( Map.fromList
          [ (CyclicBaseAddr absA, Set.fromList [absA, absB, absC])
          ]
      )
      sccs
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, sscAAddr)
          , (absB, sscAAddr)
          , (absC, sscAAddr)
          ]
      )
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (dagEdges newGraph)

testCyclic2 :: TestTree
testCyclic2 =
  testCase "cyclic_scc2" $ do
    -- {a: b, b: a, c: a}
    let graph = buildG [(absA, absB), (absB, absA), (absC, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
        sccs = sccMap newGraph
    assertEqual
      "sccs"
      ( Map.fromList
          [ (CyclicBaseAddr absA, Set.fromList [absA, absB])
          , (ACyclicGrpAddr absC, Set.singleton absC)
          ]
      )
      sccs
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, sscAAddr)
          , (absB, sscAAddr)
          , (absC, ACyclicGrpAddr absC)
          ]
      )
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [ACyclicGrpAddr absC])])
      (dagEdges newGraph)

testCyclic3 :: TestTree
testCyclic3 =
  testCase "cyclic_scc3" $ do
    -- {a: b & {}, b: c & {}, c: a & {}}
    let graph = buildGExt [(absAL, absB), (absBL, absC), (absCL, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
    assertEqual
      "sccs"
      ( Map.fromList
          [ (sscAAddr, Set.fromList [absA, absB, absC])
          ]
      )
      (sccMap newGraph)
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, sscAAddr)
          , (absB, sscAAddr)
          , (absC, sscAAddr)
          ]
      )
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (dagEdges newGraph)
    let dg = delDepPrefixFromNG (sufIrredToAddr absB) newGraph
    assertEqual
      "delDepPrefixFromNG"
      3
      (length $ sccMap dg)
 where
  absAL = appendSeg (sufIrredToAddr absA) (MutArgTASeg 0)
  absBL = appendSeg (sufIrredToAddr absB) (MutArgTASeg 0)
  absCL = appendSeg (sufIrredToAddr absC) (MutArgTASeg 0)

testCyclicSelf :: TestTree
testCyclicSelf =
  testCase "cyclic_scc_self" $ do
    -- {a: a}
    let graph = buildG [(absA, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
    assertEqual
      "sccs"
      (Map.fromList [(sscAAddr, Set.fromList [absA])])
      (sccMap newGraph)
    assertEqual
      "addr2scc"
      (Map.fromList [(absA, sscAAddr)])
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (dagEdges newGraph)

testCyclicSelf2 :: TestTree
testCyclicSelf2 =
  testCase "cyclic_scc_self2" $ do
    -- {a: a & {}}
    let graph = buildGExt [(absAL, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
    assertEqual
      "sccs"
      (Map.fromList [(sscAAddr, Set.fromList [absA])])
      (sccMap newGraph)
    assertEqual
      "addr2scc"
      (Map.fromList [(absA, sscAAddr)])
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (dagEdges newGraph)
    assertEqual
      "lookupGrpAddr"
      (Just sscAAddr)
      (lookupGrpAddr (trimAddrToSufIrred absAL) newGraph)
 where
  absAL = appendSeg (sufIrredToAddr absA) (MutArgTASeg 0)

testCyclicSelf3 :: TestTree
testCyclicSelf3 =
  testCase "cyclic_scc_self3" $ do
    -- {a: a & a}
    let graph = buildGExt [(absAL, absA), (absAR, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
    assertEqual
      "sccs"
      (Map.fromList [(sscAAddr, Set.fromList [absA])])
      (sccMap newGraph)
    assertEqual
      "addr2scc"
      (Map.fromList [(absA, sscAAddr)])
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (dagEdges newGraph)
    assertEqual
      "lookupGrpAddr"
      (Just sscAAddr)
      (lookupGrpAddr (trimAddrToSufIrred absAL) newGraph)
 where
  absAL = appendSeg (sufIrredToAddr absA) (MutArgTASeg 0)
  absAR = appendSeg (sufIrredToAddr absA) (MutArgTASeg 1)

testSCyclic :: TestTree
testSCyclic =
  testCase "scyclic_scc" $ do
    -- {a: x: b, b: a}
    let graph = buildG [(absAX, absB), (absB, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
        sccs = sccMap newGraph
    assertEqual
      "sccs"
      (Map.fromList [(sscAAddr, Set.fromList [absA, absB, absAX])])
      sccs
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, sscAAddr)
          , (absB, sscAAddr)
          , (absAX, sscAAddr)
          ]
      )
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (dagEdges newGraph)

testSCyclic2 :: TestTree
testSCyclic2 =
  testCase "scyclic_scc2" $ do
    -- {a: x: b & {}, b: a}
    let graph = buildGExt [(absAXL, absB), (sufIrredToAddr absB, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
        sccs = sccMap newGraph
    assertEqual
      "sccs"
      (Map.fromList [(sscAAddr, Set.fromList [absA, absB, absAX])])
      sccs
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, sscAAddr)
          , (absB, sscAAddr)
          , (absAX, sscAAddr)
          ]
      )
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (dagEdges newGraph)
 where
  absAXL = appendSeg (sufIrredToAddr absAX) (MutArgTASeg 0)

testSCyclic3 :: TestTree
testSCyclic3 =
  testCase "scyclic_scc3" $ do
    -- {a: x: a}
    let graph = buildG [(absAX, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
        sccs = sccMap newGraph
    assertEqual
      "sccs"
      (Map.fromList [(sscAAddr, Set.fromList [absA, absAX])])
      sccs
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, sscAAddr)
          , (absAX, sscAAddr)
          ]
      )
      (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (dagEdges newGraph)

testSCyclic4 :: TestTree
testSCyclic4 =
  testCase "scyclic_scc4" $ do
    -- {a: x: y, y: a}
    let graph = buildG [(absAXY, absY), (absY, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicBaseAddr absA
        sccs = sccMap newGraph
    -- assertEqual
    --   "sccs"
    --   (Map.fromList [(sscAAddr, Set.fromList [absA, absAX])])
    --   sccs
    -- assertEqual
    --   "addr2scc"
    --   ( Map.fromList
    --       [ (absA, sscAAddr)
    --       , (absAX, sscAAddr)
    --       ]
    --   )
    --   (addrToGrpAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (dagEdges newGraph)