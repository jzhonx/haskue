module Main where

import SpecTest (specTests)
import Test.Tasty

main :: IO ()
main = do
  tests <- specTests
  defaultMain tests

