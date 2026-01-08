module Main where

import SpecTest (specTests)
import Test.Tasty

main :: IO ()
main = do
  stests <- specTests
  defaultMain $ testGroup "all_tests" [stests]
