module Spec where

import           Data.ByteString.Builder
import qualified Data.Map.Strict         as Map
import qualified Data.Set                as Set
import           Debug.Trace
import           Eval                    (eval, run)
import           Parser
import           Path
import           System.IO               (readFile)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Value

newStruct :: [String] -> Map.Map String Value -> Set.Set String -> Value
newStruct lbls fds ids = Struct (StructValue lbls fds ids Set.empty)

newSimpleStruct :: [String] -> [(String, Value)] -> Value
newSimpleStruct lbls fds = newStruct lbls (Map.fromList fds) Set.empty

startEval :: String -> Either String Value
startEval = run

testBottom :: IO ()
testBottom = do
  s <- readFile "tests/spec/bottom.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y @?= Bottom ""

testBinOp2 :: IO ()
testBinOp2 = do
  s <- readFile "tests/spec/binop2.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newStruct
          ["x1", "x2"]
          ( Map.fromList
              [ ("x1", Int 7),
                ("x2", Int 7)
              ]
          )
          Set.empty

testSelector :: IO ()
testSelector = do
  s <- readFile "tests/spec/selector.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["T", "a", "b", "c", "d", "e", "f"]
          ( Map.fromList
              [ ("T", structT),
                ("a", Int 1),
                ("b", Int 3),
                ("c", Bottom "z is not found"),
                ("d", Int 4),
                ("e", structE),
                ("f", Disjunction [Int 4] [Int 3, Int 4])
              ]
          )
          Set.empty
  where
    structT =
      newStruct
        ["x", "y", "x-y"]
        ( Map.fromList
            [ ("x", Int 1),
              ("y", Int 3),
              ("x-y", Int 4)
            ]
        )
        Set.empty
    fieldEDefault = newSimpleStruct ["a"] [("a", Disjunction [Int 4] [Int 3, Int 4])]
    structE =
      Disjunction
        [fieldEDefault]
        [newSimpleStruct ["a"] [("a", Disjunction [Int 2] [Int 1, Int 2])], fieldEDefault]

testVars1 :: IO ()
testVars1 = do
  s <- readFile "tests/spec/vars1.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["z", "x", "y"]
          ( Map.fromList
              [ ("z", Int 1),
                ("x", Int 1),
                ("y", Int 1)
              ]
          )
          Set.empty

testVars2 :: IO ()
testVars2 = do
  s <- readFile "tests/spec/vars2.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= structTop
  where
    structX =
      newStruct
        ["a", "b", "c"]
        ( Map.fromList
            [ ("a", Int 1),
              ("b", Int 2),
              ("c", Int 9)
            ]
        )
        Set.empty
    structY =
      newStruct
        ["e", "f", "g"]
        ( Map.fromList
            [ ("e", Int 3),
              ("f", Int 4),
              ("g", Int 9)
            ]
        )
        Set.empty
    structTop =
      newStruct
        ["x", "y", "z"]
        ( Map.fromList
            [ ("x", structX),
              ("y", structY),
              ("z", Int 12)
            ]
        )
        Set.empty

testVars3 :: IO ()
testVars3 = do
  s <- readFile "tests/spec/vars3.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= structTop
  return ()
  where
    structX =
      newStruct
        ["a", "b"]
        ( Map.fromList [("a", Int 2), ("b", Int 2)]
        )
        Set.empty
    structTop =
      newStruct
        ["x"]
        ( Map.fromList [("x", structX)]
        )
        Set.empty

testCycles1 :: IO ()
testCycles1 = do
  s <- readFile "tests/spec/cycles1.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= structTop
  return ()
  where
    structTop =
      newStruct
        ["x", "b", "c", "d"]
        ( Map.fromList [("x", Top), ("b", Top), ("c", Top), ("d", Top)]
        )
        Set.empty

testBasic :: IO ()
testBasic = do
  s <- readFile "tests/spec/basic.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["a", "b", "c", "d"]
          ( Map.fromList
              [ ("a", Bool True),
                ("b", Bool False),
                ("c", Top),
                ("d", Null)
              ]
          )
          Set.empty

testUnaryOp :: IO ()
testUnaryOp = do
  s <- readFile "tests/spec/unaryop.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["x", "y", "z"]
          ( Map.fromList
              [ ("x", Int 1),
                ("y", Int (-1)),
                ("z", Bool False)
              ]
          )
          Set.empty

testBinop :: IO ()
testBinop = do
  s <- readFile "tests/spec/binop.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          (map (\i -> "x" ++ show i) [1 .. 9])
          ( Map.fromList
              [ ("x1", Int 3),
                ("x2", Int 8),
                ("x3", Int 2),
                ("x4", Int 5),
                ("x5", Int (-3)),
                ("x6", Int 7),
                ("x7", Int 5),
                ("x8", Int 9),
                ("x9", Int 9)
              ]
          )
          Set.empty

testDisjunction1 :: IO ()
testDisjunction1 = do
  s <- readFile "tests/spec/disjunct.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          (map (\i -> "x" ++ show i) [1 .. 6] ++ ["y0", "y1", "y2"])
          ( Map.fromList
              [ ("x1", Disjunction [String "tcp"] [String "tcp", String "udp"]),
                ("x2", Disjunction [Int 1] [Int 1, Int 2, Int 3]),
                ("x3", Disjunction [Int 1, Int 2] [Int 1, Int 2, Int 3]),
                ("x4", Disjunction [Int 2] [Int 1, Int 2, Int 3]),
                ("x5", Disjunction [Int 1, Int 2] [Int 1, Int 2, Int 3]),
                ("x6", Disjunction [] [Int 1, Int 2]),
                ("y0", Disjunction [] [Int 1, Int 2, Int 3]),
                ("y1", Disjunction [Int 2] [Int 1, Int 2, Int 3]),
                ("y2", Disjunction [Int 3] [Int 1, Int 2, Int 3])
              ]
          )
          Set.empty

testDisjunction2 :: IO ()
testDisjunction2 = do
  s <- readFile "tests/spec/disjunct2.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["x"]
          ( Map.fromList
              [ ( "x",
                  Disjunction
                    []
                    [ newStruct ["y", "z"] (Map.fromList [("y", Int 1), ("z", Int 3)]) Set.empty,
                      newStruct ["y"] (Map.fromList [("y", Int 2)]) Set.empty
                    ]
                )
              ]
          )
          Set.empty

testUnifyStructs :: IO ()
testUnifyStructs = do
  s <- readFile "tests/spec/unify_structs.cue"
  let val = startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["a", "b", "d", "z"]
          ( Map.fromList
              [ ("a", Int 123),
                ("b", Int 456),
                ("d", String "hello"),
                ("z", Int 4321)
              ]
          )
          Set.empty

specTests :: TestTree
specTests =
  testGroup
    "specTests"
    [ testCase "basic" testBasic,
      testCase "bottom" testBottom,
      testCase "unaryop" testUnaryOp,
      testCase "binop" testBinop,
      testCase "binop2" testBinOp2,
      testCase "disjunction1" testDisjunction1,
      testCase "disjunction2" testDisjunction2,
      testCase "unifyStructs" testUnifyStructs,
      testCase "vars1" testVars1,
      testCase "vars2" testVars2,
      testCase "vars3" testVars3,
      testCase "selector" testSelector,
      testCase "cycles1" testCycles1
    ]