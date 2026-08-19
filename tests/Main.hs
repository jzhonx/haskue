module Main where

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
      [ ScannerTest.tests
      , VTermTest.tests
      , stests
      ]
