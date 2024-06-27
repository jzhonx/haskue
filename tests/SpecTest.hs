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

newStruct :: [String] -> Map.Map String Tree -> Tree
newStruct lbls subs =
  mkSimpleTree . TNScope $
    emptyTNScope
      { trsSubs = subs
      , trsOrdLabels = lbls
      }

newSimpleStruct :: [String] -> [(String, Tree)] -> Tree
newSimpleStruct lbls fds = newStruct lbls (Map.fromList fds)

mkSimpleTreeLeaf :: Value -> Tree
mkSimpleTreeLeaf v = mkTreeLeaf v Nothing

mkSimpleTree :: TreeNode -> Tree
mkSimpleTree n = mkTree n Nothing

mkSimpleLink :: Path -> Tree
mkSimpleLink p = mkSimpleTree $ TNLink $ TreeLink{trlTarget = p, trlExpr = undefined}

startEval :: String -> IO (Either String Tree)
startEval s = runExceptT $ do
  tc <- runIO s
  case goDownTCSel StartSelector tc of
    Just u -> return $ fst u
    Nothing -> return $ mkSimpleTree . TNRoot $ TreeRoot (mkSimpleTreeLeaf $ Bottom "No value")

assertStructs :: Tree -> Tree -> IO ()
assertStructs (Tree{treeNode = TNScope exp}) (Tree{treeNode = TNScope act}) = do
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
      y @?= (mkSimpleTreeLeaf $ Bottom "")

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
                (\(k, v) -> (k, mkSimpleTreeLeaf v))
                [ ("a", Bool True)
                , ("b", Bool False)
                , ("c", Top)
                , ("d", Null)
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
                (\(k, v) -> (k, mkSimpleTreeLeaf v))
                [ ("x", Int 1)
                , ("y", Int (-1))
                , ("z", Bool False)
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
                (\(k, v) -> (k, mkSimpleTreeLeaf v))
                [ ("x1", Int 3)
                , ("x2", Int 8)
                , ("x3", Int 2)
                , ("x4", Int 5)
                , ("x5", Int (-3))
                , ("x6", Int 7)
                , ("x7", Int 5)
                , ("x8", Int 9)
                , ("x9", Int 9)
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
                (\(k, v) -> (k, mkSimpleTreeLeaf v))
                [ ("x1", Int 7)
                , ("x2", Int 7)
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
                (\(k, v) -> (k, mkSimpleTreeLeaf v))
                [ ("z", Int 1)
                , ("x", Int 1)
                , ("y", Int 1)
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
            (\(k, v) -> (k, mkSimpleTreeLeaf v))
            [ ("a", Int 1)
            , ("b", Int 2)
            , ("c", Int 9)
            ]
      )
  structY =
    newStruct
      ["e", "f", "g"]
      ( Map.fromList $
          map
            (\(k, v) -> (k, mkSimpleTreeLeaf v))
            [ ("e", Int 3)
            , ("f", Int 4)
            , ("g", Int 9)
            ]
      )

  structTop =
    newStruct
      ["x", "y", "z"]
      ( Map.fromList
          [ ("x", structX)
          , ("y", structY)
          , ("z", mkSimpleTreeLeaf $ Int 12)
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
            (\(k, v) -> (k, mkSimpleTreeLeaf v))
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
              [ ("x1", newSimpleDisj [String "tcp"] [String "tcp", String "udp"])
              , ("x2", newSimpleDisj [Int 1] [Int 1, Int 2, Int 3])
              , ("x3", newSimpleDisj [Int 1, Int 2] [Int 1, Int 2, Int 3])
              , ("x4", newSimpleDisj [Int 2] [Int 1, Int 2, Int 3])
              , ("x5", newSimpleDisj [Int 1, Int 2] [Int 1, Int 2, Int 3])
              , ("x6", newSimpleDisj [] [Int 1, Int 2])
              , ("y0", newSimpleDisj [] [Int 1, Int 2, Int 3])
              , ("y1", newSimpleDisj [Int 2] [Int 1, Int 2, Int 3])
              , ("y2", newSimpleDisj [Int 3] [Int 1, Int 2, Int 3])
              ]
          )

newSimpleDisj :: [Value] -> [Value] -> Tree
newSimpleDisj d1 d2 = mkSimpleTree . TNDisj $ TreeDisj (mkDefault d1) (map mkSimpleTreeLeaf d2)
 where
  mkDefault :: [Value] -> Maybe Tree
  mkDefault ts = case ts of
    [] -> Nothing
    x : [] -> Just $ mkSimpleTreeLeaf x
    xs -> Just $ newSimpleDisj [] xs

newSimpleTreeDisj :: [Tree] -> [Tree] -> Tree
newSimpleTreeDisj d1 d2 = mkSimpleTree . TNDisj $ TreeDisj (mkDefault d1) d2
 where
  mkDefault :: [Tree] -> Maybe Tree
  mkDefault ts = case ts of
    [] -> Nothing
    x : [] -> Just x
    xs -> Just $ newSimpleTreeDisj [] xs

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
              [
                ( "x"
                , mkSimpleTree . TNDisj $
                    TreeDisj
                      Nothing
                      [ newStruct
                          ["y", "z"]
                          ( Map.fromList
                              [("y", mkSimpleTreeLeaf $ Int 1), ("z", mkSimpleTreeLeaf $ Int 3)]
                          )
                      , newStruct ["y"] (Map.fromList [("y", mkSimpleTreeLeaf $ Int 2)])
                      ]
                )
              ]
          )

testDisj3 :: IO ()
testDisj3 = do
  s <- readFile "tests/spec/disj3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ( ["a" ++ (show i) | i <- [0 .. 2]]
              ++ ["b" ++ (show i) | i <- [0 .. 1]]
              ++ ["c" ++ (show i) | i <- [0 .. 3]]
              ++ ["d" ++ (show i) | i <- [0 .. 0]]
              ++ ["e" ++ (show i) | i <- [0 .. 4]]
          )
          ( [ ("a0", newSimpleDisj [] [String "tcp", String "udp"])
            , ("a1", newSimpleDisj [String "tcp"] [String "tcp", String "udp"])
            , ("a2", mkSimpleTreeLeaf $ Int 4)
            , ("b0", newSimpleDisj [Int 1, Int 2] [Int 1, Int 2, Int 3])
            , ("b1", newSimpleDisj [] [Int 1, Int 2, Int 3])
            , ("c0", newSimpleDisj [String "tcp"] [String "tcp", String "udp"])
            , ("c1", newSimpleDisj [String "tcp"] [String "tcp", String "udp"])
            , ("c2", newSimpleDisj [String "tcp"] [String "tcp"])
            , ("c3", newSimpleDisj [] [String "tcp", String "udp"])
            , ("d0", newSimpleDisj [Bool True] [Bool True, Bool False])
            , ("e0", newSimpleTreeDisj [] [sa, sb])
            , ("e1", newSimpleTreeDisj [sb] [sa, sb])
            , ("e2", newSimpleTreeDisj [] [sa, sb])
            , ("e3", newSimpleTreeDisj [] [sa, sba])
            , ("e4", newSimpleTreeDisj [sb] [sa, sba, sab, sb])
            ]
          )
 where
  sa = newSimpleStruct ["a"] [("a", mkSimpleTreeLeaf $ Int 1)]
  sb = newSimpleStruct ["b"] [("b", mkSimpleTreeLeaf $ Int 1)]
  sba = newSimpleStruct ["b", "a"] [("a", mkSimpleTreeLeaf $ Int 1), ("b", mkSimpleTreeLeaf $ Int 1)]
  sab = newSimpleStruct ["a", "b"] [("a", mkSimpleTreeLeaf $ Int 1), ("b", mkSimpleTreeLeaf $ Int 1)]

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
            (\(k, v) -> (k, mkSimpleTreeLeaf v))
            [ ("x", Int 1)
            , ("y", Int 3)
            , ("x-y", Int 4)
            ]
      )
  fieldEDefault = newSimpleStruct ["a"] [("a", newSimpleDisj [Int 4] [Int 3, Int 4])]
  structE =
    mkSimpleTree . TNDisj $
      TreeDisj
        (Just fieldEDefault)
        [newSimpleStruct ["a"] [("a", newSimpleDisj [Int 2] [Int 1, Int 2])], fieldEDefault]
  pathC = Path [StringSelector "c"]
  pendValC =
    mkSimpleTree . TNLink $
      TreeLink
        { trlTarget = pathFromList [StringSelector "T", StringSelector "z"]
        , trlExpr = undefined
        }
  pathF = Path [StringSelector "f"]
  disjF = newSimpleDisj [Int 4] [Int 3, Int 4]
  expStruct =
    newStruct
      ["T", "a", "b", "c", "d", "e", "f"]
      ( Map.fromList
          [ ("T", structT)
          , ("a", mkSimpleTreeLeaf $ Int 1)
          , ("b", mkSimpleTreeLeaf $ Int 3)
          , ("c", pendValC)
          , ("d", mkSimpleTreeLeaf $ Int 4)
          , ("e", structE)
          , ("f", disjF)
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
          ["a", "b", "d", "z"]
          ( Map.fromList $
              map
                (\(k, v) -> (k, mkSimpleTreeLeaf v))
                [ ("a", Int 123)
                , ("b", Int 456)
                , ("d", String "hello")
                , ("z", Int 4321)
                ]
          )

testCycles1 :: IO ()
testCycles1 = do
  s <- readFile "tests/spec/cycles1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["x", "b", "c", "d"]
          ( Map.fromList $
              [ ("x", mkSimpleTree TNRefCycleVar)
              , ("b", mkSimpleTree TNRefCycleVar)
              , ("c", mkSimpleTree TNRefCycleVar)
              , ("d", mkSimpleTree TNRefCycleVar)
              ]
          )

testCycles2 :: IO ()
testCycles2 = do
  s <- readFile "tests/spec/cycles2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["a", "b"]
          ( Map.fromList $
              [
                ( "a"
                , mkSimpleTree $
                    TNBinaryOp $
                      TreeBinaryOp
                        { trbRep = AST.Add
                        , trbOp = undefined
                        , trbArgL = mkSimpleLink $ pathFromList [StringSelector "b"]
                        , trbArgR = mkSimpleTreeLeaf $ Int 100
                        }
                )
              ,
                ( "b"
                , mkSimpleTree $
                    TNBinaryOp $
                      TreeBinaryOp
                        { trbRep = AST.Sub
                        , trbOp = undefined
                        , trbArgL = mkSimpleLink $ pathFromList [StringSelector "a"]
                        , trbArgR = mkSimpleTreeLeaf $ Int 100
                        }
                )
              ]
          )

testCycles3 :: IO ()
testCycles3 = do
  s <- readFile "tests/spec/cycles3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["b", "a"]
          ( Map.fromList $
              [ ("a", mkSimpleTreeLeaf $ Int 200)
              , ("b", mkSimpleTreeLeaf $ Int 100)
              ]
          )

testCycles4 :: IO ()
testCycles4 = do
  s <- readFile "tests/spec/cycles4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["x", "y"]
          [
            ( "x"
            , newSimpleStruct
                ["a", "b"]
                [
                  ( "a"
                  , mkSimpleTree $
                      TNBinaryOp $
                        TreeBinaryOp
                          { trbRep = AST.Add
                          , trbOp = undefined
                          , trbArgL = mkSimpleLink $ pathFromList [StringSelector "b"]
                          , trbArgR = mkSimpleTreeLeaf $ Int 100
                          }
                  )
                ,
                  ( "b"
                  , mkSimpleTree $
                      TNBinaryOp $
                        TreeBinaryOp
                          { trbRep = AST.Sub
                          , trbOp = undefined
                          , trbArgL = mkSimpleLink $ pathFromList [StringSelector "a"]
                          , trbArgR = mkSimpleTreeLeaf $ Int 100
                          }
                  )
                ]
            )
          ,
            ( "y"
            , newSimpleStruct
                ["a", "b"]
                [("a", mkSimpleTreeLeaf $ Int 200), ("b", mkSimpleTreeLeaf $ Int 100)]
            )
          ]

testCycles5 :: IO ()
testCycles5 = do
  s <- readFile "tests/spec/cycles5.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["a", "b", "c"]
          [ ("a", innerStructGen ["y", "z", "x"])
          , ("b", innerStructGen ["x", "z", "y"])
          , ("c", innerStructGen ["x", "y", "z"])
          ]
 where
  innerStructGen labels =
    newSimpleStruct
      labels
      [ ("x", mkSimpleTreeLeaf $ Int 1)
      , ("y", mkSimpleTreeLeaf $ Int 2)
      , ("z", mkSimpleTreeLeaf $ Int 3)
      ]

testCycles6 :: IO ()
testCycles6 = do
  s <- readFile "tests/spec/cycles6.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["a", "b", "c"]
          [ ("a", newSimpleTreeDisj [] [yzx, sy1])
          , ("b", newSimpleTreeDisj [] [sx2, xyz])
          , ("c", newSimpleTreeDisj [] [xzy, sz3])
          ]
 where
  innerStructGen labels =
    newSimpleStruct
      labels
      [ ("x", mkSimpleTreeLeaf $ Int 1)
      , ("y", mkSimpleTreeLeaf $ Int 3)
      , ("z", mkSimpleTreeLeaf $ Int 2)
      ]

  sy1 = newSimpleStruct ["y"] [("y", mkSimpleTreeLeaf $ Int 1)]
  sx2 = newSimpleStruct ["x"] [("x", mkSimpleTreeLeaf $ Int 2)]
  sz3 = newSimpleStruct ["z"] [("z", mkSimpleTreeLeaf $ Int 3)]

  yzx = innerStructGen ["y", "z", "x"]
  xzy = innerStructGen ["x", "z", "y"]
  xyz = innerStructGen ["x", "y", "z"]

testIncomplete :: IO ()
testIncomplete = do
  s <- readFile "tests/spec/incomplete.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          ["a", "b"]
          ( Map.fromList $
              [ ("a", mkSimpleTreeLeaf Top)
              ,
                ( "b"
                , mkSimpleTree . TNBinaryOp $
                    TreeBinaryOp
                      { trbRep = AST.Sub
                      , trbOp = undefined
                      , trbArgL = mkSimpleLink $ pathFromList [StringSelector "a"]
                      , trbArgR = mkSimpleTreeLeaf $ Int 1
                      }
                )
              ]
          )

testDup1 :: IO ()
testDup1 = do
  s <- readFile "tests/spec/dup1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["z"]
          [
            ( "z"
            , newSimpleStruct
                ["y", "x"]
                [ ("x", newSimpleStruct ["b"] [("b", mkSimpleTreeLeaf $ Int 4)])
                , ("y", newSimpleStruct ["b"] [("b", mkSimpleTreeLeaf $ Int 4)])
                ]
            )
          ]

testDup2 :: IO ()
testDup2 = do
  s <- readFile "tests/spec/dup2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["x"]
          [
            ( "x"
            , newSimpleStruct
                ["a", "c"]
                [ ("a", mkSimpleTreeLeaf $ Int 1)
                , ("c", mkSimpleTreeLeaf $ Int 2)
                ]
            )
          ]

testDup3 :: IO ()
testDup3 = do
  s <- readFile "tests/spec/dup3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["x"]
          [
            ( "x"
            , newSimpleStruct
                ["a", "b", "c"]
                [ ("a", mkSimpleTreeLeaf $ Int 1)
                , ("b", mkSimpleTreeLeaf $ Int 2)
                , ("c", mkSimpleTreeLeaf $ Int 2)
                ]
            )
          ]

testRef1 :: IO ()
testRef1 = do
  s <- readFile "tests/spec/ref1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["a", "b"]
          [ ("a", mkSimpleTreeLeaf $ Int 4)
          , ("b", mkSimpleTreeLeaf $ Int 4)
          ]

testRef2 :: IO ()
testRef2 = do
  s <- readFile "tests/spec/ref2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["a", "x"]
          [ ("a", mkSimpleTreeLeaf $ Int 1)
          ,
            ( "x"
            , newSimpleStruct
                ["c", "d"]
                [ ("c", mkSimpleTreeLeaf $ Int 1)
                , ("d", mkSimpleTreeLeaf $ Top)
                ]
            )
          ]

testRef3 :: IO ()
testRef3 = do
  s <- readFile "tests/spec/ref3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["x", "d"]
          [
            ( "x"
            , newSimpleStruct
                ["a", "c"]
                [ ("a", mkSimpleTreeLeaf $ Int 1)
                , ("c", mkSimpleTreeLeaf $ Int 2)
                ]
            )
          ,
            ( "d"
            , newSimpleStruct
                ["y"]
                [
                  ( "y"
                  , newSimpleStruct
                      ["a", "c"]
                      [ ("a", mkSimpleTreeLeaf $ Int 1)
                      , ("c", mkSimpleTreeLeaf $ Int 2)
                      ]
                  )
                ]
            )
          ]

specTests :: TestTree
specTests =
  testGroup
    "specTest"
    [ testCase "basic" testBasic
    , testCase "bottom" testBottom
    , testCase "unaryop" testUnaryOp
    , testCase "binop" testBinop
    , testCase "binop2" testBinOp2
    , testCase "disj1" testDisj1
    , testCase "disj2" testDisj2
    , testCase "disj3" testDisj3
    , testCase "vars1" testVars1
    , testCase "vars2" testVars2
    , testCase "vars3" testVars3
    , testCase "selector1" testSelector1
    , testCase "unify1" testUnify1
    , testCase "cycles1" testCycles1
    , testCase "cycles2" testCycles2
    , testCase "cycles3" testCycles3
    , testCase "cycles4" testCycles4
    , testCase "cycles5" testCycles5
    , testCase "cycles6" testCycles6
    , testCase "incomplete" testIncomplete
    , testCase "dup1" testDup1
    , testCase "dup2" testDup2
    , testCase "dup3" testDup3
    , testCase "ref1" testRef1
    , testCase "ref2" testRef2
    , testCase "ref3" testRef3
    ]
