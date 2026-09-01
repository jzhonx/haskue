module RecalcTest (tests) where

import DepGraph (VertexAddr (..), fileTopVertexAddr)
import EvalAddr
import Reduce.Recalc (owningReducerAddr, parentOwningReducerAddr)
import StringIndex (TextIndex (..))
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "Recalc"
    [ testCase "finds the vertex owning a nested reduction" testOwningReducerAddr
    , testCase "finds the parent of an owning reducer" testParentOwningReducerAddr
    ]

testOwningReducerAddr :: Assertion
testOwningReducerAddr = do
  let fieldAddr = appendFeature fileTopEvalAddr (mkStringFeature (TextIndex 0))
      nestedFieldAddr =
        appendFeature
          (appendTermStep fieldAddr (mkDisjTermStep 0))
          (mkStringFeature (TextIndex 1))
      objectFieldAddr =
        appendFeature
          (appendTermStep fieldAddr (mkObjectTermStep 0))
          (mkStringFeature (TextIndex 1))
      fieldVertex = VertexAddr (ReducedAddr fieldAddr)
  owningReducerAddr (VertexAddr (ReducedAddr nestedFieldAddr)) @?= fieldVertex
  owningReducerAddr (VertexAddr (ReducedAddr objectFieldAddr)) @?= fieldVertex
  owningReducerAddr fieldVertex @?= fieldVertex

testParentOwningReducerAddr :: Assertion
testParentOwningReducerAddr = do
  let fieldAddr = appendFeature fileTopEvalAddr (mkStringFeature (TextIndex 0))
      nestedFieldAddr =
        appendFeature
          (appendTermStep fieldAddr (mkDisjTermStep 0))
          (mkStringFeature (TextIndex 1))
      nestedFieldVertex = VertexAddr (ReducedAddr nestedFieldAddr)
  parentOwningReducerAddr nestedFieldVertex @?= Just fileTopVertexAddr
  parentOwningReducerAddr fileTopVertexAddr @?= Nothing
