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
import Text.Printf (printf)
import Tree

newStruct :: [String] -> [(String, LabelAttr)] -> [(String, Tree)] -> Tree
newStruct lbls ow subs =
  mkNewTree . TNScope $
    TreeScope
      { trsSubs = Map.fromList subs
      , trsOrdLabels = lbls
      , trsAttrs = Map.fromList $ map attrWrite lbls
      }
 where
  attrWrite :: String -> (String, LabelAttr)
  attrWrite s = case lookup s ow of
    Just v -> (s, v)
    Nothing -> (s, defaultLabelAttr)

newSimpleStruct :: [String] -> [(String, Tree)] -> Tree
newSimpleStruct lbls subs = newStruct lbls [] subs

mkSimpleLink :: Path -> Tree
mkSimpleLink p = mkNewTree $ TNLink $ TreeLink{trlTarget = p, trlExpr = undefined}

startEval :: String -> IO (Either String Tree)
startEval s = runExceptT $ do
  tc <- runIO s
  case goDownTCSel StartSelector tc of
    Just u -> return $ fst u
    Nothing -> return $ mkNewTree . TNRoot $ TreeRoot (mkBottom "No value")

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
      y @?= (mkBottom "")

testBasic :: IO ()
testBasic = do
  s <- readFile "tests/spec/basic.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["a", "b", "c", "d"]
          ( map
              (\(k, v) -> (k, mkTreeAtom v))
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
        @?= newSimpleStruct
          ["x", "y", "z"]
          ( map
              (\(k, v) -> (k, mkTreeAtom v))
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
    Right v ->
      cmpStructs
        v
        $ newSimpleStruct
          (map (\i -> "x" ++ show i) [1 .. 10])
          ( map
              (\(k, v) -> (k, mkTreeAtom v))
              [ ("x1", Int 3)
              , ("x2", Int 8)
              , ("x3", Float 2.0)
              , ("x4", Int 5)
              , ("x5", Int (-3))
              , ("x6", Int 7)
              , ("x7", Float 5.0)
              , ("x8", Int 9)
              , ("x9", Int 9)
              , ("x10", Float 0.5)
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
        @?= newSimpleStruct
          ["x1", "x2"]
          ( map
              (\(k, v) -> (k, mkTreeAtom v))
              [ ("x1", Int 7)
              , ("x2", Int 7)
              ]
          )

testBinOpCmpEq :: IO ()
testBinOpCmpEq = do
  s <- readFile "tests/spec/binop_cmp_eq.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newSimpleStruct
          ( ["i" ++ (show i) | i <- [0 .. 2]]
              ++ ["f" ++ (show i) | i <- [0 .. 5]]
              ++ ["b" ++ (show i) | i <- [0 .. 2]]
              ++ ["s" ++ (show i) | i <- [0 .. 2]]
              ++ ["n" ++ (show i) | i <- [0 .. 6]]
          )
          ( map
              (\(k, v) -> (k, mkTreeAtom (Bool v)))
              [ ("i0", False)
              , ("i1", True)
              , ("i2", False)
              , ("f0", False)
              , ("f1", True)
              , ("f2", False)
              , ("f3", True)
              , ("f4", True)
              , ("f5", False)
              , ("b0", False)
              , ("b1", True)
              , ("b2", False)
              , ("s0", False)
              , ("s1", True)
              , ("s2", False)
              , ("n0", True)
              , ("n1", False)
              , ("n2", False)
              , ("n3", False)
              , ("n4", False)
              , ("n5", False)
              , ("n6", False)
              ]
          )

testBinOpCmpNE :: IO ()
testBinOpCmpNE = do
  s <- readFile "tests/spec/binop_cmp_ne.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newSimpleStruct
          ( ["i" ++ (show i) | i <- [0 .. 2]]
              ++ ["b" ++ (show i) | i <- [0 .. 2]]
              ++ ["s" ++ (show i) | i <- [0 .. 2]]
              ++ ["n" ++ (show i) | i <- [0 .. 6]]
          )
          ( map
              (\(k, v) -> (k, mkTreeAtom (Bool v)))
              [ ("i0", True)
              , ("i1", False)
              , ("i2", True)
              , ("b0", True)
              , ("b1", False)
              , ("b2", True)
              , ("s0", True)
              , ("s1", False)
              , ("s2", True)
              , ("n0", False)
              , ("n1", True)
              , ("n2", True)
              , ("n3", True)
              , ("n4", True)
              , ("n5", True)
              , ("n6", True)
              ]
          )

testBounds1 :: IO ()
testBounds1 = do
  s <- readFile "tests/spec/bounds1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newSimpleStruct
          ( ["x" ++ (show i) | i <- [0 .. 5]]
          )
          ( map
              (\(k, v) -> (k, mkTreeAtom v))
              [ ("x0", Int 2)
              , ("x1", Int 2)
              , ("x2", String "a")
              , ("x3", String "a")
              , ("x4", Bool True)
              , ("x5", Bool False)
              ]
          )

testBounds2 :: IO ()
testBounds2 = do
  s <- readFile "tests/spec/bounds2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newSimpleStruct
          ( ["x" ++ (show i) | i <- [0 .. 6]]
          )
          ( map
              (\(k, v) -> (k, mkTreeAtom v))
              [ ("x0", Int 2)
              , ("x1", Float 2.5)
              , ("x2", Int 2)
              , ("x3", Int 2)
              , ("x4", Float 2.5)
              , ("x5", Int 1)
              , ("x6", Int 5)
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
        @?= newSimpleStruct
          ["z", "x", "y"]
          ( map
              (\(k, v) -> (k, mkTreeAtom v))
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
    newSimpleStruct
      ["a", "b", "c"]
      ( map
          (\(k, v) -> (k, mkTreeAtom v))
          [ ("a", Int 1)
          , ("b", Int 2)
          , ("c", Int 9)
          ]
      )
  structY =
    newSimpleStruct
      ["e", "f", "g"]
      ( map
          (\(k, v) -> (k, mkTreeAtom v))
          [ ("e", Int 3)
          , ("f", Int 4)
          , ("g", Int 9)
          ]
      )

  structTop =
    newSimpleStruct
      ["x", "y", "z"]
      ( [ ("x", structX)
        , ("y", structY)
        , ("z", mkTreeAtom $ Int 12)
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
    newSimpleStruct
      ["a", "b"]
      ( map
          (\(k, v) -> (k, mkTreeAtom v))
          [("a", Int 2), ("b", Int 2)]
      )
  structTop =
    newSimpleStruct
      ["x"]
      [("x", structX)]

testDisj1 :: IO ()
testDisj1 = do
  s <- readFile "tests/spec/disj1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right v ->
      cmpStructs v $
        newSimpleStruct
          (map (\i -> "x" ++ show i) [1 .. 6] ++ ["y0", "y1", "y2"])
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

newSimpleDisj :: [Atom] -> [Atom] -> Tree
newSimpleDisj d1 d2 = mkNewTree . TNDisj $ TreeDisj (mkDefault d1) (map mkTreeAtom d2)
 where
  mkDefault :: [Atom] -> Maybe Tree
  mkDefault ts = case ts of
    [] -> Nothing
    x : [] -> Just $ mkTreeAtom x
    xs -> Just $ newSimpleDisj [] xs

newSimpleTreeDisj :: [Tree] -> [Tree] -> Tree
newSimpleTreeDisj d1 d2 = mkNewTree . TNDisj $ TreeDisj (mkDefault d1) d2
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
        @?= newSimpleStruct
          ["x"]
          [
            ( "x"
            , mkNewTree . TNDisj $
                TreeDisj
                  Nothing
                  [ newSimpleStruct
                      ["y", "z"]
                      [("y", mkTreeAtom $ Int 1), ("z", mkTreeAtom $ Int 3)]
                  , newSimpleStruct ["y"] ([("y", mkTreeAtom $ Int 2)])
                  ]
            )
          ]

testDisj3 :: IO ()
testDisj3 = do
  s <- readFile "tests/spec/disj3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right v ->
      cmpStructs v $
        newSimpleStruct
          ( ["a" ++ (show i) | i <- [0 .. 2]]
              ++ ["b" ++ (show i) | i <- [0 .. 1]]
              ++ ["c" ++ (show i) | i <- [0 .. 3]]
              ++ ["d" ++ (show i) | i <- [0 .. 0]]
              ++ ["e" ++ (show i) | i <- [0 .. 4]]
          )
          ( [ ("a0", newSimpleDisj [] [String "tcp", String "udp"])
            , ("a1", newSimpleDisj [String "tcp"] [String "tcp", String "udp"])
            , ("a2", mkTreeAtom $ Int 4)
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
  sa = newSimpleStruct ["a"] [("a", mkTreeAtom $ Int 1)]
  sb = newSimpleStruct ["b"] [("b", mkTreeAtom $ Int 1)]
  sba = newSimpleStruct ["b", "a"] [("a", mkTreeAtom $ Int 1), ("b", mkTreeAtom $ Int 1)]
  sab = newSimpleStruct ["a", "b"] [("a", mkTreeAtom $ Int 1), ("b", mkTreeAtom $ Int 1)]

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
      [("x-y", LabelAttr SLRegular False)]
      ( map
          (\(k, v) -> (k, mkTreeAtom v))
          [ ("x", Int 1)
          , ("y", Int 3)
          , ("x-y", Int 4)
          ]
      )
  fieldEDefault = newSimpleStruct ["a"] [("a", newSimpleDisj [Int 4] [Int 3, Int 4])]
  structE =
    mkNewTree . TNDisj $
      TreeDisj
        (Just fieldEDefault)
        [newSimpleStruct ["a"] [("a", newSimpleDisj [Int 2] [Int 1, Int 2])], fieldEDefault]
  pathC = Path [StringSelector "c"]
  pendValC =
    mkNewTree . TNLink $
      TreeLink
        { trlTarget = pathFromList [StringSelector "T", StringSelector "z"]
        , trlExpr = undefined
        }
  pathF = Path [StringSelector "f"]
  disjF = newSimpleDisj [Int 4] [Int 3, Int 4]
  expStruct =
    newSimpleStruct
      ["T", "a", "b", "c", "d", "e", "f"]
      [ ("T", structT)
      , ("a", mkTreeAtom $ Int 1)
      , ("b", mkTreeAtom $ Int 3)
      , ("c", pendValC)
      , ("d", mkTreeAtom $ Int 4)
      , ("e", structE)
      , ("f", disjF)
      ]

testUnify1 :: IO ()
testUnify1 = do
  s <- readFile "tests/spec/unify1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["a", "b", "d", "z"]
          ( map
              (\(k, v) -> (k, mkTreeAtom v))
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
        @?= newSimpleStruct
          ["x", "b", "c", "d"]
          [ ("x", mkNewTree TNRefCycleVar)
          , ("b", mkNewTree TNRefCycleVar)
          , ("c", mkNewTree TNRefCycleVar)
          , ("d", mkNewTree TNRefCycleVar)
          ]

testCycles2 :: IO ()
testCycles2 = do
  s <- readFile "tests/spec/cycles2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["a", "b"]
          [
            ( "a"
            , mkNewTree $
                TNFunc $
                  mkBinaryOp
                    AST.Add
                    undefined
                    (mkSimpleLink $ pathFromList [StringSelector "b"])
                    (mkTreeAtom $ Int 100)
            )
          ,
            ( "b"
            , mkNewTree $
                TNFunc $
                  mkBinaryOp
                    AST.Sub
                    undefined
                    (mkSimpleLink $ pathFromList [StringSelector "a"])
                    (mkTreeAtom $ Int 100)
            )
          ]

testCycles3 :: IO ()
testCycles3 = do
  s <- readFile "tests/spec/cycles3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newSimpleStruct
          ["b", "a"]
          [ ("a", mkTreeAtom $ Int 200)
          , ("b", mkTreeAtom $ Int 100)
          ]

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
                  , mkNewTree $
                      TNFunc $
                        mkBinaryOp
                          AST.Add
                          undefined
                          (mkSimpleLink $ pathFromList [StringSelector "b"])
                          (mkTreeAtom $ Int 100)
                  )
                ,
                  ( "b"
                  , mkNewTree $
                      TNFunc $
                        mkBinaryOp
                          AST.Sub
                          undefined
                          (mkSimpleLink $ pathFromList [StringSelector "a"])
                          (mkTreeAtom $ Int 100)
                  )
                ]
            )
          ,
            ( "y"
            , newSimpleStruct
                ["a", "b"]
                [("a", mkTreeAtom $ Int 200), ("b", mkTreeAtom $ Int 100)]
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
      [ ("x", mkTreeAtom $ Int 1)
      , ("y", mkTreeAtom $ Int 2)
      , ("z", mkTreeAtom $ Int 3)
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
      [ ("x", mkTreeAtom $ Int 1)
      , ("y", mkTreeAtom $ Int 3)
      , ("z", mkTreeAtom $ Int 2)
      ]

  sy1 = newSimpleStruct ["y"] [("y", mkTreeAtom $ Int 1)]
  sx2 = newSimpleStruct ["x"] [("x", mkTreeAtom $ Int 2)]
  sz3 = newSimpleStruct ["z"] [("z", mkTreeAtom $ Int 3)]

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
        @?= newSimpleStruct
          ["a", "b"]
          [ ("a", mkTreeAtom Top)
          ,
            ( "b"
            , mkNewTree . TNFunc $
                mkBinaryOp
                  AST.Sub
                  undefined
                  (mkSimpleLink $ pathFromList [StringSelector "a"])
                  (mkTreeAtom $ Int 1)
            )
          ]

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
                [ ("x", newSimpleStruct ["b"] [("b", mkTreeAtom $ Int 4)])
                , ("y", newSimpleStruct ["b"] [("b", mkTreeAtom $ Int 4)])
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
                [ ("a", mkTreeAtom $ Int 1)
                , ("c", mkTreeAtom $ Int 2)
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
                [ ("a", mkTreeAtom $ Int 1)
                , ("b", mkTreeAtom $ Int 2)
                , ("c", mkTreeAtom $ Int 2)
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
          [ ("a", mkTreeAtom $ Int 4)
          , ("b", mkTreeAtom $ Int 4)
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
          [ ("a", mkTreeAtom $ Int 1)
          ,
            ( "x"
            , newSimpleStruct
                ["c", "d"]
                [ ("c", mkTreeAtom $ Int 1)
                , ("d", mkTreeAtom $ Top)
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
                [ ("a", mkTreeAtom $ Int 1)
                , ("c", mkTreeAtom $ Int 2)
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
                      [ ("a", mkTreeAtom $ Int 1)
                      , ("c", mkTreeAtom $ Int 2)
                      ]
                  )
                ]
            )
          ]

testStruct1 :: IO ()
testStruct1 = do
  s <- readFile "tests/spec/struct1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newSimpleStruct
          ["s1"]
          [ ("s1", s1)
          ]
 where
  s1 =
    newSimpleStruct
      ["a", "b", "c"]
      ( map
          (\(k, v) -> (k, mkTreeAtom v))
          [ ("a", Int 1)
          , ("b", Int 2)
          , ("c", Int 3)
          ]
      )

testStruct2 :: IO ()
testStruct2 = do
  s <- readFile "tests/spec/struct2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newSimpleStruct
          ["a"]
          [("a", a)]
 where
  a =
    newSimpleStruct
      ["b", "c"]
      [ ("b", ab)
      , ("c", mkTreeAtom $ Int 42)
      ]
  ab =
    newSimpleStruct
      ["c", "d"]
      [ ("c", abc)
      , ("d", mkTreeAtom $ Int 12)
      ]
  abc =
    newSimpleStruct
      ["d"]
      [("d", mkTreeAtom $ Int 123)]

testStruct3 :: IO ()
testStruct3 = do
  s <- readFile "tests/spec/struct3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  sGen :: Tree -> Tree
  sGen t = newSimpleStruct ["f"] [("f", t)]

  sGen2 :: Tree -> LabelAttr -> Tree
  sGen2 t la = newStruct ["f"] [("f", la)] [("f", t)]

  exp =
    newSimpleStruct
      (map (\i -> "x" ++ show i) [0 .. 7])
      [ ("x0", sGen $ mkTreeAtom $ Int 3)
      , ("x1", sGen $ mkTreeAtom $ Int 3)
      , ("x2", sGen $ mkTNBounds [BdType BdInt])
      , ("x3", sGen2 (mkTNBounds [BdNumCmp $ BdNumCmpCons BdLT (NumInt 1)]) (LabelAttr SLRequired True))
      , ("x4", sGen $ mkTNBounds [BdNumCmp $ BdNumCmpCons BdLE (NumInt 3)])
      , ("x5", sGen $ mkTreeAtom $ Int 3)
      , ("x6", sGen $ mkTreeAtom $ Int 3)
      , ("x7", sGen $ mkTreeAtom $ Int 3)
      ]

testList1 :: IO ()
testList1 = do
  s <- readFile "tests/spec/list1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newSimpleStruct
      ["x0", "x1"]
      ( [ ("x0", mkNewTree . TNList $ TreeList (map mkTreeAtom [Int 1, Int 4, Int 9]))
        , ("x1", mkNewTree . TNList $ TreeList (map mkTreeAtom [Float 1.0, Bool True, String "hello"]))
        ]
      )

testIndex1 :: IO ()
testIndex1 = do
  s <- readFile "tests/spec/index1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpExpStructs y exp
 where
  exp =
    newSimpleStruct
      ["x1", "x2", "x3", "x4", "x5", "z"]
      ( map
          (\(k, v) -> (k, mkTreeAtom v))
          [ ("x1", Int 14)
          , ("x2", Int 4)
          , ("x3", Int 9)
          , ("x4", Int 3)
          , ("x5", Int 1)
          , ("z", Int 4)
          ]
      )

specTests :: TestTree
specTests =
  testGroup
    "specTest"
    [ testCase "basic" testBasic
    , testCase "bottom" testBottom
    , testCase "unaryop" testUnaryOp
    , testCase "binop" testBinop
    , testCase "binop2" testBinOp2
    , testCase "binop_cmp_eq" testBinOpCmpEq
    , testCase "binop_cmp_ne" testBinOpCmpNE
    , testCase "bounds1" testBounds1
    , testCase "bounds2" testBounds2
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
    , testCase "struct1" testStruct1
    , testCase "struct2" testStruct2
    , testCase "struct3" testStruct3
    , testCase "list1" testList1
    , testCase "index1" testIndex1
    ]

cmpStructs :: Tree -> Tree -> IO ()
cmpStructs (Tree{treeNode = TNScope act}) (Tree{treeNode = TNScope exp}) = do
  assertEqual "labels" (trsOrdLabels exp) (trsOrdLabels act)
  assertEqual "fields-length" (length $ trsSubs exp) (length $ trsSubs act)
  mapM_ (\(k, v) -> assertEqual k v (trsSubs act Map.! k)) (Map.toList $ trsSubs exp)
  mapM_ (\(k, v) -> assertEqual k (trsSubs exp Map.! k) v) (Map.toList $ trsSubs act)
cmpStructs v1 v2 = assertFailure $ printf "Not structs: %s, %s" (show v1) (show v2)

cmpExpStructs :: Tree -> Tree -> IO ()
cmpExpStructs (Tree{treeNode = TNScope act}) (Tree{treeNode = TNScope exp}) = do
  mapM_ cmp (Map.toList $ trsSubs exp)
 where
  cmp (k, v) =
    if k `Map.member` trsSubs act
      then assertEqual k v (trsSubs act Map.! k)
      else assertFailure $ printf "Field %s not found" k
cmpExpStructs v1 v2 = assertFailure $ printf "Not structs: %s, %s" (show v1) (show v2)
