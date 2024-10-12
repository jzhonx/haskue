module Main where

import SpecTest (specTests)
import Test.Tasty

main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ specTests
    ]
