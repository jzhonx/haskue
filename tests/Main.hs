module Main where

import           Spec          (specTests)
import           Test.Tasty
import           TransformTest (transformTests)
import           ValueTest     (valueTests)

main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ specTests,
      valueTests,
      transformTests
    ]
