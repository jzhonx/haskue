module Main where

import qualified ASTTest
import qualified DepGraphTest
import E2ETest (e2eTests)
import qualified EvalAddrTest
import qualified ExplainTest
import qualified RecalcTest
import qualified ScannerTest
import Test.Tasty
import qualified TraceTest
import qualified VTermTest
import qualified ValueEqTest

main :: IO ()
main = do
  endToEndTests <- e2eTests
  defaultMain $
    testGroup
      "All Tests"
      [ ASTTest.tests
      , DepGraphTest.tests
      , EvalAddrTest.tests
      , ExplainTest.tests
      , RecalcTest.tests
      , ScannerTest.tests
      , TraceTest.tests
      , ValueEqTest.tests
      , VTermTest.tests
      , endToEndTests
      ]
