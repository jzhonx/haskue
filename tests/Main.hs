module Main where

import SpecTest (specTests)
import Test.Tasty
import TreeTest (treeTests)

main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ specTests
    , treeTests
    ]
