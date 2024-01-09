module Main where

import           E2E        (e2eTests)
import           Test.Tasty
import           ValueTest  (valueTests)

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [e2eTests, valueTests]
