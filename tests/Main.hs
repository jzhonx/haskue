module Main where

import qualified ScannerTest
import SpecTest (specTests)
import Test.Tasty

main :: IO ()
main = do
  stests <- specTests
  defaultMain $
    testGroup
      "All Tests"
      [ ScannerTest.tests
      , stests
      ]
