module Main where

import qualified EvalAddrTest
import qualified ScannerTest
import SpecTest (specTests)
import Test.Tasty
import qualified VTermTest
import qualified ValueEqTest

main :: IO ()
main = do
  stests <- specTests
  defaultMain $
    testGroup
      "All Tests"
      [ EvalAddrTest.tests
      , ScannerTest.tests
      , ValueEqTest.tests
      , VTermTest.tests
      , stests
      ]
