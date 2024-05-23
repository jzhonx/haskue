module Main where

-- import EvalTest (evalTests)
import SpecTest (specTests)
import Test.Tasty
-- import TransformTest (transformTests)
import TreeTest (treeTests)

main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ 
      specTests,
      -- evalTests,
      -- transformTests
      treeTests
    ]
