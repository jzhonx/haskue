module Main where

import NotifGraphTest (ngTests)
import SpecTest (specTests)
import Test.Tasty

main :: IO ()
main = do
  stests <- specTests
  ntests <- ngTests
  defaultMain $ testGroup "all_tests" [stests, ntests]
