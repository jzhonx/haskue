module Main where

import NotifGraphTest (ngTests)
import SpecTest (specTests)
import Test.Tasty
import TreeTest (treeTests)

main :: IO ()
main = do
  stests <- specTests
  ntests <- ngTests
  trtests <- treeTests
  defaultMain $ testGroup "all_tests" [stests, ntests, trtests]
