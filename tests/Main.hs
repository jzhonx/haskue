module Main where

import Data.ByteString.Builder
import qualified Data.Map.Strict as Map
import Eval (eval)
import Parser
import System.IO (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import Value

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [e2eTests]

e2eTests :: TestTree
e2eTests =
  testGroup
    "e2e tests"
    [ testCase "basic" $
        do
          s <- readFile "tests/e2efiles/basic.cue"
          let val = (eval . parseCUE) s
          case val of
            Left err -> assertFailure err
            Right val' ->
              val'
                @?= Struct
                  ["x1", "x2", "y1", "y2", "z1"]
                  ( Map.fromList
                      [ ("x1", Bool True),
                        ("x2", Bool False),
                        ("y1", Top),
                        ("y2", Bottom ""),
                        ("z1", Null)
                      ]
                  ),
      testCase "unaryop" $
        do
          s <- readFile "tests/e2efiles/unaryop.cue"
          let val = (eval . parseCUE) s
          case val of
            Left err -> assertFailure err
            Right val' ->
              val'
                @?= Struct
                  ["x", "y", "z"]
                  ( Map.fromList
                      [ ("x", Int 1),
                        ("y", Int (-1)),
                        ("z", Bool False)
                      ]
                  ),
      testCase "binop" $
        do
          s <- readFile "tests/e2efiles/binop.cue"
          let val = (eval . parseCUE) s
          case val of
            Left err -> assertFailure err
            Right val' ->
              val'
                @?= Struct
                  ["x", "y", "z", "a", "b", "c", "d"]
                  ( Map.fromList
                      [ ("x", Int 3),
                        ("y", Int 8),
                        ("z", Int 2),
                        ("a", Int 5),
                        ("b", Struct [] Map.empty),
                        ("c", Bottom ""),
                        ("d", Int (-3))
                      ]
                  ),
      testCase
        "disjunction"
        $ do
          s <- readFile "tests/e2efiles/disjunct.cue"
          let val = (eval . parseCUE) s
          case val of
            Left err -> assertFailure err
            Right val' ->
              val'
                @?= Struct
                  (map (\i -> "x" ++ show i) [1 .. 7])
                  ( Map.fromList
                      [ ("x1", Disjunction Nothing [Int 1, Int 2, Int 3]),
                        ("x2", Disjunction Nothing [Int 1, Int 2]),
                        ("x3", Int 1),
                        ("x4", String "a"),
                        ("x5", Int 1),
                        ("x6", Disjunction Nothing [Int 1, Int 2]),
                        ("x7", Int 1)
                      ]
                  ),
      testCase
        "disjunction-2"
        $ do
          s <- readFile "tests/e2efiles/disjunct2.cue"
          let val = (eval . parseCUE) s
          case val of
            Left err -> assertFailure err
            Right val' ->
              val'
                @?= Struct
                  ["x"]
                  ( Map.fromList
                      [ ("x", Struct ["y", "z"] (Map.fromList [("y", Int 1), ("z", Int 3)]))
                      ]
                  ),
      testCase
        "unify-structs"
        $ do
          s <- readFile "tests/e2efiles/unify_structs.cue"
          let val = (eval . parseCUE) s
          case val of
            Left err -> assertFailure err
            Right val' ->
              val'
                @?= Struct
                  ["a", "b", "d", "z"]
                  ( Map.fromList
                      [ ("a", Int 123),
                        ("b", Int 456),
                        ("d", String "hello"),
                        ("z", Int 4321)
                      ]
                  )
    ]
