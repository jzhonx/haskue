module Main where

import qualified EvalTreeTest
import qualified ScannerTest
import SpecTest (specTests)
import Test.Tasty
import qualified VTermTest

main :: IO ()
main = do
  stests <- specTests
  defaultMain $
    testGroup
      "All Tests"
      [ EvalTreeTest.tests
      , ScannerTest.tests
      , VTermTest.tests
      , stests
      ]
