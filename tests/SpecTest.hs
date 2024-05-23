module SpecTest where

import qualified AST
import Control.Monad.Except (runExceptT)
import Data.ByteString.Builder
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Debug.Trace
import Eval (eval, runIO)
import Parser
import Path
import System.IO (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import Tree

newStruct :: [String] -> Map.Map String TreeNode -> TreeNode
newStruct lbls subs =
  TNScope $
    emptyTNScope
      { trsSubs = subs,
        trsOrdLabels = lbls
      }

newSimpleStruct :: [String] -> [(String, TreeNode)] -> TreeNode
newSimpleStruct lbls fds = newStruct lbls (Map.fromList fds)

startEval :: String -> IO (Either String TreeNode)
startEval s = runExceptT $ do
  tc <- runIO s
  case goDownTCSel StartSelector tc of
    Just u -> return $ fst u
    Nothing -> return $ TNRoot $ mkTreeLeaf $ Bottom "No value"

assertStructs :: TreeNode -> TreeNode -> IO ()
assertStructs (TNScope exp) (TNScope act) = do
  assertEqual "labels" (trsOrdLabels exp) (trsOrdLabels act)
  assertEqual "fields-length" (length $ trsSubs exp) (length $ trsSubs act)
  mapM_ (\(k, v) -> assertEqual k v (trsSubs act Map.! k)) (Map.toList $ trsSubs exp)
  mapM_ (\(k, v) -> assertEqual k (trsSubs exp Map.! k) v) (Map.toList $ trsSubs act)
assertStructs _ _ = assertFailure "Not structs"

testBottom :: IO ()
testBottom = do
  s <- readFile "tests/spec/bottom.cue"
  n <- startEval s
  case n of
    Left err -> assertFailure err
    Right y ->
      y @?= (mkTreeLeaf $ Bottom "")

testBasic :: IO ()
testBasic = do
  s <- readFile "tests/spec/basic.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["a", "b", "c", "d"]
          ( Map.fromList $
              map
                (\(k, v) -> (k, mkTreeLeaf v))
                [ ("a", Bool True),
                  ("b", Bool False),
                  ("c", Top),
                  ("d", Null)
                ]
          )

testUnaryOp :: IO ()
testUnaryOp = do
  s <- readFile "tests/spec/unaryop.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["x", "y", "z"]
          ( Map.fromList $
              map
                (\(k, v) -> (k, mkTreeLeaf v))
                [ ("x", Int 1),
                  ("y", Int (-1)),
                  ("z", Bool False)
                ]
          )

testBinop :: IO ()
testBinop = do
  s <- readFile "tests/spec/binop.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          (map (\i -> "x" ++ show i) [1 .. 9])
          ( Map.fromList $
              map
                (\(k, v) -> (k, mkTreeLeaf v))
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

testBinOp2 :: IO ()
testBinOp2 = do
  s <- readFile "tests/spec/binop2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newStruct
          ["x1", "x2"]
          ( Map.fromList $
              map
                (\(k, v) -> (k, mkTreeLeaf v))
                [ ("x1", Int 7),
                  ("x2", Int 7)
                ]
          )

testVars1 :: IO ()
testVars1 = do
  s <- readFile "tests/spec/vars1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["z", "x", "y"]
          ( Map.fromList $
              map
                (\(k, v) -> (k, mkTreeLeaf v))
                [ ("z", Int 1),
                  ("x", Int 1),
                  ("y", Int 1)
                ]
          )

testVars2 :: IO ()
testVars2 = do
  s <- readFile "tests/spec/vars2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= structTop
  where
    structX =
      newStruct
        ["a", "b", "c"]
        ( Map.fromList $
            map
              (\(k, v) -> (k, mkTreeLeaf v))
              [ ("a", Int 1),
                ("b", Int 2),
                ("c", Int 9)
              ]
        )
    structY =
      newStruct
        ["e", "f", "g"]
        ( Map.fromList $
            map
              (\(k, v) -> (k, mkTreeLeaf v))
              [ ("e", Int 3),
                ("f", Int 4),
                ("g", Int 9)
              ]
        )

    structTop =
      newStruct
        ["x", "y", "z"]
        ( Map.fromList
            [ ("x", structX),
              ("y", structY),
              ("z", mkTreeLeaf $ Int 12)
            ]
        )

testVars3 :: IO ()
testVars3 = do
  s <- readFile "tests/spec/vars3.cue"
  val <- startEval s
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
        ( Map.fromList $
            map
              (\(k, v) -> (k, mkTreeLeaf v))
              [("a", Int 2), ("b", Int 2)]
        )
    structTop =
      newStruct
        ["x"]
        ( Map.fromList [("x", structX)]
        )

testDisj1 :: IO ()
testDisj1 = do
  s <- readFile "tests/spec/disj1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          (map (\i -> "x" ++ show i) [1 .. 6] ++ ["y0", "y1", "y2"])
          ( Map.fromList
              [ ("x1", newSimpleDisj [String "tcp"] [String "tcp", String "udp"]),
                ("x2", newSimpleDisj [Int 1] [Int 1, Int 2, Int 3]),
                ("x3", newSimpleDisj [Int 1, Int 2] [Int 1, Int 2, Int 3]),
                ("x4", newSimpleDisj [Int 2] [Int 1, Int 2, Int 3]),
                ("x5", newSimpleDisj [Int 1, Int 2] [Int 1, Int 2, Int 3]),
                ("x6", newSimpleDisj [] [Int 1, Int 2]),
                ("y0", newSimpleDisj [] [Int 1, Int 2, Int 3]),
                ("y1", newSimpleDisj [Int 2] [Int 1, Int 2, Int 3]),
                ("y2", newSimpleDisj [Int 3] [Int 1, Int 2, Int 3])
              ]
          )

newSimpleDisj :: [Value] -> [Value] -> TreeNode
newSimpleDisj d1 d2 = TNDisj $ TreeDisj (map mkTreeLeaf d1) (map mkTreeLeaf d2)

testDisj2 :: IO ()
testDisj2 = do
  s <- readFile "tests/spec/disj2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["x"]
          ( Map.fromList
              [ ( "x",
                  TNDisj $
                    TreeDisj
                      []
                      [ newStruct
                          ["y", "z"]
                          ( Map.fromList
                              [("y", mkTreeLeaf $ Int 1), ("z", mkTreeLeaf $ Int 3)]
                          ),
                        newStruct ["y"] (Map.fromList [("y", mkTreeLeaf $ Int 2)])
                      ]
                )
              ]
          )

testSelector1 :: IO ()
testSelector1 = do
  s <- readFile "tests/spec/selector1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right v -> assertStructs expStruct v
  where
    structT =
      newStruct
        ["x", "y", "x-y"]
        ( Map.fromList $
            map
              (\(k, v) -> (k, mkTreeLeaf v))
              [ ("x", Int 1),
                ("y", Int 3),
                ("x-y", Int 4)
              ]
        )
    fieldEDefault = newSimpleStruct ["a"] [("a", newSimpleDisj [Int 4] [Int 3, Int 4])]
    structE =
      TNDisj $
        TreeDisj
          [fieldEDefault]
          [newSimpleStruct ["a"] [("a", newSimpleDisj [Int 2] [Int 1, Int 2])], fieldEDefault]
    pathC = Path [StringSelector "c"]
    pendValC =
      TNUnaryOp $
        TreeUnaryOp
          { truRep = "\"dot z\"",
            truArg = structT
          }
    pathF = Path [StringSelector "f"]
    disjF = newSimpleDisj [Int 4] [Int 3, Int 4]
    expStruct =
      newStruct
        ["T", "a", "b", "c", "d", "e", "f"]
        ( Map.fromList
            [ ("T", structT),
              ("a", mkTreeLeaf $ Int 1),
              ("b", mkTreeLeaf $ Int 3),
              ("c", pendValC),
              ("d", mkTreeLeaf $ Int 4),
              ("e", structE),
              ("f", disjF)
            ]
        )

testUnify1 :: IO ()
testUnify1 = do
  s <- readFile "tests/spec/unify1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["a", "d", "b", "z"]
          ( Map.fromList $
              map
                (\(k, v) -> (k, mkTreeLeaf v))
                [ ("a", Int 123),
                  ("b", Int 456),
                  ("d", String "hello"),
                  ("z", Int 4321)
                ]
          )

-- testCycles1 :: IO ()
-- testCycles1 = do
--   s <- readFile "tests/spec/cycles1.cue"
--   val <- startEval s
--   case val of
--     Left err -> assertFailure err
--     Right val' ->
--       val'
--         @?= structTop
--   return ()
--   where
--     pendValGen path =
--       Pending $
--         PendingValue
--           path
--           []
--           []
--           undefined
--           Top
--           (AST.litCons AST.BottomLit)
--     structTop =
--       newStruct
--         ["x", "b", "c", "d"]
--         ( Map.fromList
--             [ ("x", Top),
--               ("b", pendValGen (Path [StringSelector "b"])),
--               ("c", pendValGen (Path [StringSelector "c"])),
--               ("d", pendValGen (Path [StringSelector "d"]))
--             ]
--         )
--         Set.empty
--
--
--

specTests :: TestTree
specTests =
  testGroup
    "specTest"
    [ testCase "basic" testBasic,
      testCase "bottom" testBottom,
      testCase "unaryop" testUnaryOp,
      testCase "binop" testBinop,
      testCase "binop2" testBinOp2,
      testCase "disj1" testDisj1,
      testCase "disj2" testDisj2,
      testCase "vars1" testVars1,
      testCase "vars2" testVars2,
      testCase "vars3" testVars3,
      testCase "selector1" testSelector1,
      testCase "unify1" testUnify1
      -- testCase "cycles1" testCycles1
    ]
