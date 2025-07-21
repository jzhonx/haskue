module NotifGraphTest where

import qualified Data.Map.Strict as Map
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
      , testSCyclic
      , testSCyclic2
      , testSCyclic3
      ]

buildAbsTA :: String -> TreeAddr
buildAbsTA path = appendTreeAddr rootTreeAddr (addrFromString path)

absA, absAX, absB, absC :: TreeAddr
absA = buildAbsTA "a"
absAX = buildAbsTA "a.x"
absB = buildAbsTA "b"
absC = buildAbsTA "c"

buildG :: [(TreeAddr, TreeAddr)] -> NotifGraph
buildG =
  foldr
    ( \(dep, target) acc -> addNewDepToNGNoUpdate (dep, target) acc
    )
    emptyNotifGraph

testACyclic :: TestTree
testACyclic =
  testCase "acyclic_scc" $ do
    -- {a: b, b: c, a: x: c}
    let graph = buildG [(absA, absB), (absB, absC), (absAX, absC)]
        newGraph = updateNotifGraph graph
        sccs = ngSCCs newGraph
    assertEqual
      "sccs"
      ( Map.fromList
          [ (ACyclicSCCAddr absA, Set.singleton absA)
          , (ACyclicSCCAddr absB, Set.singleton absB)
          , (ACyclicSCCAddr absC, Set.singleton absC)
          , (ACyclicSCCAddr absAX, Set.singleton absAX)
          ]
      )
      sccs
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, ACyclicSCCAddr absA)
          , (absB, ACyclicSCCAddr absB)
          , (absC, ACyclicSCCAddr absC)
          , (absAX, ACyclicSCCAddr absAX)
          ]
      )
      (ngAddrToSCCAddr newGraph)
    assertEqual
      "sccDAG"
      ( Map.fromList
          [ (ACyclicSCCAddr absB, [ACyclicSCCAddr absA])
          , (ACyclicSCCAddr absC, [ACyclicSCCAddr absAX, ACyclicSCCAddr absB])
          , (ACyclicSCCAddr absA, [])
          , (ACyclicSCCAddr absAX, [])
          ]
      )
      (ngSCCDAGEdges newGraph)

testCyclic :: TestTree
testCyclic =
  testCase "cyclic_scc" $ do
    -- {a: b, b: c, c: a}
    let graph = buildG [(absA, absB), (absB, absC), (absC, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicSCCAddr $ SCCBaseAddr absA
        sccs = ngSCCs newGraph
    assertEqual
      "sccs"
      ( Map.fromList
          [ (CyclicSCCAddr (SCCBaseAddr absA), Set.fromList [absA, absB, absC])
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
      (ngAddrToSCCAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (ngSCCDAGEdges newGraph)
    assertEqual
      "rcDependents"
      [absC, absA, absB]
      (findRCDependents absA newGraph)

testCyclic2 :: TestTree
testCyclic2 =
  testCase "cyclic_scc2" $ do
    -- {a: b, b: a, c: a}
    let graph = buildG [(absA, absB), (absB, absA), (absC, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicSCCAddr $ SCCBaseAddr absA
        sccs = ngSCCs newGraph
    assertEqual
      "sccs"
      ( Map.fromList
          [ (CyclicSCCAddr (SCCBaseAddr absA), Set.fromList [absA, absB])
          , (ACyclicSCCAddr absC, Set.singleton absC)
          ]
      )
      sccs
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, sscAAddr)
          , (absB, sscAAddr)
          , (absC, ACyclicSCCAddr absC)
          ]
      )
      (ngAddrToSCCAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [ACyclicSCCAddr absC]), (ACyclicSCCAddr absC, [])])
      (ngSCCDAGEdges newGraph)
    assertEqual
      "rcDependents"
      [absB, absA]
      (findRCDependents absA newGraph)

testCyclic3 :: TestTree
testCyclic3 =
  testCase "cyclic_scc3" $ do
    -- {a: b & {}, b: c & {}, c: a & {}}
    let graph = buildG [(absAL, absB), (absBL, absC), (absCL, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicSCCAddr $ SCCBaseAddr absA
    assertEqual
      "sccs"
      ( Map.fromList
          [ (sscAAddr, Set.fromList [absA, absB, absC])
          ]
      )
      (ngSCCs newGraph)
    assertEqual
      "addr2scc"
      ( Map.fromList
          [ (absA, sscAAddr)
          , (absB, sscAAddr)
          , (absC, sscAAddr)
          ]
      )
      (ngAddrToSCCAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (ngSCCDAGEdges newGraph)
    assertEqual
      "rcDependents"
      [absCL, absAL, absBL]
      (findRCDependents absA newGraph)
 where
  absAL = appendSeg absA (MutArgTASeg 0)
  absBL = appendSeg absB (MutArgTASeg 0)
  absCL = appendSeg absC (MutArgTASeg 0)

testCyclicSelf :: TestTree
testCyclicSelf =
  testCase "cyclic_scc_self" $ do
    -- {a: a}
    let graph = buildG [(absA, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicSCCAddr $ SCCBaseAddr absA
    assertEqual
      "sccs"
      (Map.fromList [(sscAAddr, Set.fromList [absA])])
      (ngSCCs newGraph)
    assertEqual
      "addr2scc"
      (Map.fromList [(absA, sscAAddr)])
      (ngAddrToSCCAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (ngSCCDAGEdges newGraph)

testCyclicSelf2 :: TestTree
testCyclicSelf2 =
  testCase "cyclic_scc_self2" $ do
    -- {a: a & {}}
    let graph = buildG [(absAL, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = CyclicSCCAddr $ SCCBaseAddr absA
    assertEqual
      "sccs"
      (Map.fromList [(sscAAddr, Set.fromList [absA])])
      (ngSCCs newGraph)
    assertEqual
      "addr2scc"
      (Map.fromList [(absA, sscAAddr)])
      (ngAddrToSCCAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (ngSCCDAGEdges newGraph)
 where
  absAL = appendSeg absA (MutArgTASeg 0)

testSCyclic :: TestTree
testSCyclic =
  testCase "scyclic_scc" $ do
    -- {a: x: b, b: a}
    let graph = buildG [(absAX, absB), (absB, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = SCyclicSCCAddr (SCCBaseAddr absAX) (absA, absAX)
        sccs = ngSCCs newGraph
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
      (ngAddrToSCCAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (ngSCCDAGEdges newGraph)

testSCyclic2 :: TestTree
testSCyclic2 =
  testCase "scyclic_scc2" $ do
    -- {a: x: b & {}, b: a}
    let graph = buildG [(absAXL, absB), (absB, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = SCyclicSCCAddr (SCCBaseAddr absAX) (absA, absAX)
        sccs = ngSCCs newGraph
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
      (ngAddrToSCCAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (ngSCCDAGEdges newGraph)
 where
  absAXL = appendSeg absAX (MutArgTASeg 0)

testSCyclic3 :: TestTree
testSCyclic3 =
  testCase "scyclic_scc3" $ do
    -- {a: x: a}
    let graph = buildG [(absAX, absA)]
        newGraph = updateNotifGraph graph
        sscAAddr = SCyclicSCCAddr (SCCBaseAddr absAX) (absA, absAX)
        sccs = ngSCCs newGraph
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
      (ngAddrToSCCAddr newGraph)
    assertEqual
      "sccDAG"
      (Map.fromList [(sscAAddr, [])])
      (ngSCCDAGEdges newGraph)