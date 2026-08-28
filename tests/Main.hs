module Main where

import qualified ASTTest
import qualified DepGraphTest
import qualified EvalAddrTest
import qualified ExplainTest
import qualified ScannerTest
import SpecTest (specTests)
import Test.Tasty
import qualified TraceTest
import qualified VTermTest
import qualified ValueEqTest

main :: IO ()
main = do
  stests <- specTests
  defaultMain $
    testGroup
      "All Tests"
      [ ASTTest.tests
      , DepGraphTest.tests
      , EvalAddrTest.tests
      , ExplainTest.tests
      , ScannerTest.tests
      , TraceTest.tests
      , ValueEqTest.tests
      , VTermTest.tests
      , stests
      ]
