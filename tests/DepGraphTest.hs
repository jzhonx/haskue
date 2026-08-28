module DepGraphTest (tests) where

import DepGraph
import EvalAddr
import StringIndex (TextIndex (..))
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "DepGraph"
    [ testCase "finds existing dependency-use edges" testQueryExistingDepUseEdges
    , testCase "rejects an edge owned by another dependency" testQueryDifferentDepUseEdge
    , testCase "returns false for unknown endpoints" testQueryUnknownDepUseEdge
    ]

testQueryExistingDepUseEdges :: Assertion
testQueryExistingDepUseEdges = do
  assertBool "direct use edge is present" $ queryDepUseEdge depA (vertexAddr useA) graph
  assertBool "normalized operation use edge is present" $ queryDepUseEdge depA (vertexAddr useB) graph

testQueryDifferentDepUseEdge :: Assertion
testQueryDifferentDepUseEdge =
  assertBool "use is not an edge of depA" $ not $ queryDepUseEdge depA (vertexAddr otherUse) graph

testQueryUnknownDepUseEdge :: Assertion
testQueryUnknownDepUseEdge = do
  assertBool "unknown dependency has no edge" $ not $ queryDepUseEdge unknownDep (vertexAddr useA) graph
  assertBool "unknown use has no edge" $ not $ queryDepUseEdge depA (vertexAddr unknownUse) graph

graph :: DepGraph
graph =
  addNewDepToNG useB depA $
    addNewDepToNG useA depA $
      addNewDepToNG otherUse depB emptyDepGraph

depA :: ReferableAddr
depA = referableField 1

depB :: ReferableAddr
depB = referableField 2

unknownDep :: ReferableAddr
unknownDep = referableField 6

useA :: EvalAddr
useA = fieldAddr 3

useB :: EvalAddr
useB = appendTermStep (fieldAddr 4) (mkOpArgTermStep 0)

otherUse :: EvalAddr
otherUse = fieldAddr 5

unknownUse :: EvalAddr
unknownUse = fieldAddr 7

vertexAddr :: EvalAddr -> VertexAddr
vertexAddr = trimCanonicalToVertex . collapseToCanonical

referableField :: Int -> ReferableAddr
referableField index = case addrIsRfbAddr (fieldAddr index) of
  Just addr -> addr
  Nothing -> error "test field address is not referable"

fieldAddr :: Int -> EvalAddr
fieldAddr index = appendFeature fileTopEvalAddr (mkStringFeature (TextIndex index))
