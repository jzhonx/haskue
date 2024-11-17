module SpecTest where

import qualified AST
import Class
import Config
import Control.Monad.Except (runExcept, runExceptT, throwError)
import Data.ByteString.Builder
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Debug.Trace
import Eval (runTreeIO)
import Parser
import Path
import Reduction (mkRefFunc)
import System.IO (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf (printf)
import Value.Tree

newStruct :: [String] -> [(String, LabelAttr)] -> [(String, Tree)] -> Tree
newStruct lbls ow subs =
  mkNewTree . TNStruct $
    Struct
      { stcSubs =
          Map.fromList
            ( map
                ( \(k, v) ->
                    ( Path.StringSelector k
                    , StaticStructField
                        { ssfField = v
                        , ssfAttr = snd $ attrWrite k
                        }
                    )
                )
                subs
            )
      , stcOrdLabels = map Path.StringSelector lbls
      , stcPendSubs = []
      , stcPatterns = []
      , stcClosed = False
      }
 where
  attrWrite :: String -> (StructSelector, LabelAttr)
  attrWrite s = case lookup s ow of
    Just v -> (StringSelector s, v)
    Nothing -> (StringSelector s, defaultLabelAttr)

newSimpleStruct :: [String] -> [(String, Tree)] -> Tree
newSimpleStruct lbls = newStruct lbls []

newFieldsStruct :: [(String, Tree)] -> Tree
newFieldsStruct subs = newSimpleStruct (map fst subs) subs

mkSimpleLink :: Path -> Tree
mkSimpleLink p = case runExcept (mkRefFunc p undefined) of
  Left err -> error err
  Right v -> mkFuncTree v

startEval :: String -> IO (Either String Tree)
startEval s = runExceptT $ runTreeIO s

assertStructs :: Tree -> Tree -> IO ()
assertStructs (Tree{treeNode = TNStruct exp}) (Tree{treeNode = TNStruct act}) = do
  assertEqual "labels" (stcOrdLabels exp) (stcOrdLabels act)
  assertEqual "fields-length" (length $ stcSubs exp) (length $ stcSubs act)
  mapM_ (\(k, v) -> assertEqual (show k) v (stcSubs act Map.! k)) (Map.toList $ stcSubs exp)
  mapM_ (\(k, v) -> assertEqual (show k) (stcSubs exp Map.! k) v) (Map.toList $ stcSubs act)
assertStructs _ _ = assertFailure "Not structs"

strSel :: String -> Selector
strSel = StructSelector . StringSelector

testBottom :: IO ()
testBottom = do
  s <- readFile "tests/spec/bottom.cue"
  n <- startEval s
  case n of
    Left err -> assertFailure err
    Right y -> y @?= mkBottomTree ""

testBasic :: IO ()
testBasic = do
  s <- readFile "tests/spec/basic.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpStructs y $
        newSimpleStruct
          ["a", "b", "c", "d"]
          [ ("a", mkAtomTree $ Bool True)
          , ("b", mkAtomTree $ Bool False)
          , ("c", mkNewTree TNTop)
          , ("d", mkAtomTree Null)
          ]

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
              (\(k, v) -> (k, mkAtomTree v))
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
              (\(k, v) -> (k, mkAtomTree v))
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
              (\(k, v) -> (k, mkAtomTree v))
              [ ("x1", Int 7)
              , ("x2", Int 7)
              ]
          )

testBinOp3 :: IO ()
testBinOp3 = do
  s <- readFile "tests/spec/binop3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newSimpleStruct
          ["x1"]
          ( map
              (\(k, v) -> (k, mkAtomTree v))
              [ ("x1", String "foobar")
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
          ( ["i" ++ show i | i <- [0 .. 2]]
              ++ ["f" ++ show i | i <- [0 .. 5]]
              ++ ["b" ++ show i | i <- [0 .. 2]]
              ++ ["s" ++ show i | i <- [0 .. 2]]
              ++ ["n" ++ show i | i <- [0 .. 6]]
          )
          ( map
              (\(k, v) -> (k, mkAtomTree (Bool v)))
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
          ( ["i" ++ show i | i <- [0 .. 2]]
              ++ ["b" ++ show i | i <- [0 .. 2]]
              ++ ["s" ++ show i | i <- [0 .. 2]]
              ++ ["n" ++ show i | i <- [0 .. 6]]
          )
          ( map
              (\(k, v) -> (k, mkAtomTree (Bool v)))
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
              (\(k, v) -> (k, mkAtomTree v))
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
          ( ["x" ++ show i | i <- [0 .. 6]]
          )
          ( map
              (\(k, v) -> (k, mkAtomTree v))
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
              (\(k, v) -> (k, mkAtomTree v))
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
          (\(k, v) -> (k, mkAtomTree v))
          [ ("a", Int 1)
          , ("b", Int 2)
          , ("c", Int 9)
          ]
      )
  structY =
    newSimpleStruct
      ["e", "f", "g"]
      ( map
          (\(k, v) -> (k, mkAtomTree v))
          [ ("e", Int 3)
          , ("f", Int 4)
          , ("g", Int 9)
          ]
      )

  structTop =
    newSimpleStruct
      ["x", "y", "z"]
      [ ("x", structX)
      , ("y", structY)
      , ("z", mkAtomTree $ Int 12)
      ]

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
          (\(k, v) -> (k, mkAtomTree v))
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
          (map (\i -> "x" ++ show i) [1 .. 6] ++ ["y0", "y1", "y2"] ++ ["z1"])
          [ ("x1", newSimpleAtomDisj [String "tcp"] [String "tcp", String "udp"])
          , ("x2", newSimpleAtomDisj [Int 1] [Int 1, Int 2, Int 3])
          , ("x3", newSimpleAtomDisj [Int 1, Int 2] [Int 1, Int 2, Int 3])
          , ("x4", newSimpleAtomDisj [Int 2] [Int 1, Int 2, Int 3])
          , ("x5", newSimpleAtomDisj [Int 1, Int 2] [Int 1, Int 2, Int 3])
          , ("x6", newSimpleAtomDisj [] [Int 1, Int 2])
          , ("y0", newSimpleAtomDisj [] [Int 1, Int 2, Int 3])
          , ("y1", newSimpleAtomDisj [Int 2] [Int 1, Int 2, Int 3])
          , ("y2", newSimpleAtomDisj [Int 3] [Int 1, Int 2, Int 3])
          , ("z1", mkAtomTree $ Int 3)
          ]

newSimpleAtomDisj :: [Atom] -> [Atom] -> Tree
newSimpleAtomDisj d1 d2 = mkNewTree . TNDisj $ Disj (mkDefault d1) (map mkAtomTree d2)
 where
  mkDefault :: [Atom] -> Maybe Tree
  mkDefault ts = case ts of
    [] -> Nothing
    [x] -> Just $ mkAtomTree x
    xs -> Just $ newSimpleAtomDisj [] xs

newSimpleDisj :: [Tree] -> [Tree] -> Tree
newSimpleDisj d1 d2 = mkNewTree . TNDisj $ Disj (mkDefault d1) d2
 where
  mkDefault :: [Tree] -> Maybe Tree
  mkDefault ts = case ts of
    [] -> Nothing
    [x] -> Just x
    xs -> Just $ newSimpleDisj [] xs

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
                Disj
                  Nothing
                  [ newSimpleStruct
                      ["y", "z"]
                      [("y", mkAtomTree $ Int 1), ("z", mkAtomTree $ Int 3)]
                  , newSimpleStruct ["y"] [("y", mkAtomTree $ Int 2)]
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
          ( ["a" ++ show i | i <- [0 .. 2]]
              ++ ["b" ++ show i | i <- [0 .. 1]]
              ++ ["c" ++ show i | i <- [0 .. 3]]
              ++ ["d" ++ show i | i <- [0 .. 0]]
              ++ ["e" ++ show i | i <- [0 .. 4]]
          )
          [ ("a0", newSimpleAtomDisj [] [String "tcp", String "udp"])
          , ("a1", newSimpleAtomDisj [String "tcp"] [String "tcp", String "udp"])
          , ("a2", mkAtomTree $ Int 4)
          , ("b0", newSimpleAtomDisj [Int 1, Int 2] [Int 1, Int 2, Int 3])
          , ("b1", newSimpleAtomDisj [] [Int 1, Int 2, Int 3])
          , ("c0", newSimpleAtomDisj [String "tcp"] [String "tcp", String "udp"])
          , ("c1", newSimpleAtomDisj [String "tcp"] [String "tcp", String "udp"])
          , ("c2", newSimpleAtomDisj [String "tcp"] [String "tcp"])
          , ("c3", newSimpleAtomDisj [] [String "tcp", String "udp"])
          , ("d0", newSimpleAtomDisj [Bool True] [Bool True, Bool False])
          , ("e0", newSimpleDisj [] [sa, sb])
          , ("e1", newSimpleDisj [sb] [sa, sb])
          , ("e2", newSimpleDisj [] [sa, sb])
          , ("e3", newSimpleDisj [] [sa, sba])
          , ("e4", newSimpleDisj [sb] [sa, sba, sab, sb])
          ]
 where
  sa = newSimpleStruct ["a"] [("a", mkAtomTree $ Int 1)]
  sb = newSimpleStruct ["b"] [("b", mkAtomTree $ Int 1)]
  sba = newSimpleStruct ["b", "a"] [("a", mkAtomTree $ Int 1), ("b", mkAtomTree $ Int 1)]
  sab = newSimpleStruct ["a", "b"] [("a", mkAtomTree $ Int 1), ("b", mkAtomTree $ Int 1)]

testDisj4 :: IO ()
testDisj4 = do
  s <- readFile "tests/spec/disj4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpExpStructs y $
        newFieldsStruct
          [
            ( "x"
            , mkNewTree . TNDisj $
                Disj
                  (Just $ mkAtomTree $ String "h")
                  [ mkAtomTree $ String "h"
                  , mkBoundsTree [BdType BdString]
                  ]
            )
          ,
            ( "y"
            , mkNewTree . TNDisj $
                Disj
                  (Just $ mkAtomTree $ String "h")
                  [ mkAtomTree $ String "h"
                  , mkBoundsTree [BdType BdString]
                  ]
            )
          ,
            ( "z"
            , mkNewTree . TNDisj $
                Disj
                  (Just $ mkAtomTree $ String "h")
                  [ mkAtomTree $ String "h"
                  , mkBoundsTree [BdType BdString]
                  ]
            )
          ]

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
          (\(k, v) -> (k, mkAtomTree v))
          [ ("x", Int 1)
          , ("y", Int 3)
          , ("x-y", Int 4)
          ]
      )
  fieldEDefault = newSimpleStruct ["a"] [("a", newSimpleAtomDisj [Int 4] [Int 3, Int 4])]
  structE =
    mkNewTree . TNDisj $
      Disj
        (Just fieldEDefault)
        [newSimpleStruct ["a"] [("a", newSimpleAtomDisj [Int 2] [Int 1, Int 2])], fieldEDefault]
  pathC = Path [strSel "c"]
  pendValC = mkSimpleLink $ pathFromList [strSel "T", strSel "z"]
  pathF = Path [strSel "f"]
  disjF = newSimpleAtomDisj [Int 4] [Int 3, Int 4]
  expStruct =
    newSimpleStruct
      ["T", "a", "b", "c", "d", "e", "f"]
      [ ("T", structT)
      , ("a", mkAtomTree $ Int 1)
      , ("b", mkAtomTree $ Int 3)
      , ("c", pendValC)
      , ("d", mkAtomTree $ Int 4)
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
          ["a", "d", "b", "z"]
          ( map
              (\(k, v) -> (k, mkAtomTree v))
              [ ("a", Int 123)
              , ("b", Int 456)
              , ("d", String "hello")
              , ("z", Int 4321)
              ]
          )

testUnify2 :: IO ()
testUnify2 = do
  s <- readFile "tests/spec/unify2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpStructs y $
        newSimpleStruct
          ["x", "y"]
          [ ("x", newFieldsStruct [("a", mkNewTree TNTop), ("b", mkNewTree TNTop)])
          , ("y", newFieldsStruct [("a", mkAtomTree $ Int 200), ("b", mkAtomTree $ Int 200)])
          ]

testUnify3 :: IO ()
testUnify3 = do
  s <- readFile "tests/spec/unify3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpStructs y $
        newSimpleStruct
          ["x", "y"]
          [ ("x", newFieldsStruct [("a", mkNewTree TNTop), ("b", mkNewTree TNTop)])
          , ("y", newFieldsStruct [("a", mkAtomTree $ Int 200), ("b", mkNewTree TNTop)])
          ]

testUnify4 :: IO ()
testUnify4 = do
  s <- readFile "tests/spec/unify4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpStructs y $
        newSimpleStruct
          ["x", "y", "df"]
          [ ("x", newFieldsStruct [("a", mkNewTree TNTop), ("b", mkAtomTree $ Int 1)])
          , ("y", newFieldsStruct [("a", mkAtomTree $ Int 2), ("b", mkAtomTree $ Int 1)])
          , ("df", mkAtomTree $ String "x")
          ]

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
          [ ("x", selfCycle)
          , ("b", selfCycle)
          , ("c", selfCycle)
          , ("d", selfCycle)
          ]
 where
  selfCycle = mkNewTree (TNRefCycle (RefCycle True))

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
            , mkNewTree (TNRefCycle (RefCycle False))
            )
          ,
            ( "b"
            , mkNewTree (TNRefCycle (RefCycle False))
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
          ["a", "b"]
          [ ("a", mkAtomTree $ Int 200)
          , ("b", mkAtomTree $ Int 100)
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
                  , mkNewTree (TNRefCycle (RefCycle False))
                  )
                ,
                  ( "b"
                  , mkNewTree (TNRefCycle (RefCycle False))
                  )
                ]
            )
          ,
            ( "y"
            , newSimpleStruct
                ["a", "b"]
                [("a", mkAtomTree $ Int 200), ("b", mkAtomTree $ Int 100)]
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
          [ ("a", innerStructGen ["z", "y", "x"])
          , ("b", innerStructGen ["x", "z", "y"])
          , ("c", innerStructGen ["y", "x", "z"])
          ]
 where
  innerStructGen labels =
    newSimpleStruct
      labels
      [ ("x", mkAtomTree $ Int 1)
      , ("y", mkAtomTree $ Int 2)
      , ("z", mkAtomTree $ Int 3)
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
          [ ("a", newSimpleDisj [] [yzx, sy1])
          , ("b", newSimpleDisj [] [sx2, xyz])
          , ("c", newSimpleDisj [] [zxy, sz3])
          ]
 where
  innerStructGen labels =
    newSimpleStruct
      labels
      [ ("x", mkAtomTree $ Int 1)
      , ("y", mkAtomTree $ Int 3)
      , ("z", mkAtomTree $ Int 2)
      ]

  sy1 = newSimpleStruct ["y"] [("y", mkAtomTree $ Int 1)]
  sx2 = newSimpleStruct ["x"] [("x", mkAtomTree $ Int 2)]
  sz3 = newSimpleStruct ["z"] [("z", mkAtomTree $ Int 3)]

  yzx = innerStructGen ["y", "z", "x"]
  xyz = innerStructGen ["x", "y", "z"]
  zxy = innerStructGen ["z", "x", "y"]

testCycles7 :: IO ()
testCycles7 = do
  s <- readFile "tests/spec/cycles7.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpExpStructs x $
        newSimpleStruct
          ["x", "y", "z", "dfa", "z2"]
          [ ("x", newSimpleStruct ["a", "b"] [("a", selfCycle), ("b", selfCycle)])
          , ("y", newSimpleStruct ["a", "b"] [("a", selfCycle), ("b", mkAtomTree $ Int 2)])
          , ("z", newSimpleStruct ["a", "b"] [("a", mkAtomTree $ Int 2), ("b", mkAtomTree $ Int 2)])
          , ("dfa", mkAtomTree $ String "a")
          , ("z2", newSimpleStruct ["a", "b"] [("a", mkAtomTree $ Int 2), ("b", mkAtomTree $ Int 2)])
          ]
 where
  selfCycle = mkNewTree (TNRefCycle (RefCycle True))

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
          [ ("a", mkNewTree TNTop)
          ,
            ( "b"
            , mkFuncTree $
                mkBinaryOp
                  AST.Sub
                  (\_ _ -> throwError "not implemented")
                  (mkNewTree TNTop)
                  (mkAtomTree $ Int 1)
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
                [ ("x", newSimpleStruct ["b"] [("b", mkAtomTree $ Int 4)])
                , ("y", newSimpleStruct ["b"] [("b", mkAtomTree $ Int 4)])
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
                [ ("a", mkAtomTree $ Int 1)
                , ("c", mkAtomTree $ Int 2)
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
                [ ("a", mkAtomTree $ Int 1)
                , ("b", mkAtomTree $ Int 2)
                , ("c", mkAtomTree $ Int 2)
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
          [ ("a", mkAtomTree $ Int 4)
          , ("b", mkAtomTree $ Int 4)
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
          [ ("a", mkAtomTree $ Int 1)
          ,
            ( "x"
            , newSimpleStruct
                ["c", "d"]
                [ ("c", mkAtomTree $ Int 1)
                , ("d", mkNewTree TNTop)
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
                [ ("a", mkAtomTree $ Int 1)
                , ("c", mkAtomTree $ Int 2)
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
                      [ ("a", mkAtomTree $ Int 1)
                      , ("c", mkAtomTree $ Int 2)
                      ]
                  )
                ]
            )
          ]

testRef5 :: IO ()
testRef5 = do
  s <- readFile "tests/spec/ref5.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpExpStructs x $
        newSimpleStruct
          ["b", "c", "df"]
          [ ("b", mkAtomTree $ String "z")
          , ("df", mkAtomTree $ String "c")
          ,
            ( "c"
            , newSimpleStruct
                ["z"]
                [ ("z", mkAtomTree $ String "z")
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
          (\(k, v) -> (k, mkAtomTree v))
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
      , ("c", mkAtomTree $ Int 42)
      ]
  ab =
    newSimpleStruct
      ["c", "d"]
      [ ("c", abc)
      , ("d", mkAtomTree $ Int 12)
      ]
  abc =
    newSimpleStruct
      ["d"]
      [("d", mkAtomTree $ Int 123)]

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
      [ ("x0", sGen $ mkAtomTree $ Int 3)
      , ("x1", sGen $ mkAtomTree $ Int 3)
      , ("x2", sGen $ mkBoundsTree [BdType BdInt])
      , ("x3", sGen2 (mkBoundsTree [BdNumCmp $ BdNumCmpCons BdLT (NumInt 1)]) (LabelAttr SLRequired True))
      , ("x4", sGen $ mkBoundsTree [BdNumCmp $ BdNumCmpCons BdLE (NumInt 3)])
      , ("x5", sGen $ mkAtomTree $ Int 3)
      , ("x6", sGen $ mkAtomTree $ Int 3)
      , ("x7", sGen $ mkAtomTree $ Int 3)
      ]

testStruct4 :: IO ()
testStruct4 = do
  s <- readFile "tests/spec/struct4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      ["a", "b", "foo", "foobar", "bar"]
      [ ("foo", LabelAttr SLRegular False)
      , ("bar", LabelAttr SLRequired False)
      , ("foobar", LabelAttr SLRegular False)
      ]
      [ ("a", mkAtomTree $ String "foo")
      , ("b", mkAtomTree $ String "bar")
      , ("foo", mkAtomTree $ String "baz")
      , ("foobar", mkAtomTree $ String "qux")
      , ("bar", mkBoundsTree [BdType BdString])
      ]

testStruct5 :: IO ()
testStruct5 = do
  s <- readFile "tests/spec/struct5.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newSimpleStruct
      ["a", "b"]
      [ ("a", newSimpleStruct ["c"] [("c", mkAtomTree $ String "b")])
      ,
        ( "b"
        , newSimpleStruct
            ["x", "y"]
            [ ("x", mkAtomTree $ String "x")
            , ("y", mkAtomTree $ String "y")
            ]
        )
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
      [ ("x0", mkNewTree . TNList $ List (map mkAtomTree [Int 1, Int 4, Int 9]))
      , ("x1", mkNewTree . TNList $ List (map mkAtomTree [Float 1.0, Bool True, String "hello"]))
      ]

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
          (\(k, v) -> (k, mkAtomTree v))
          [ ("x1", Int 14)
          , ("x2", Int 4)
          , ("x3", Int 9)
          , ("x4", Int 3)
          , ("x5", Int 1)
          , ("z", Int 4)
          ]
      )

testCnstr1 :: IO ()
testCnstr1 = do
  s <- readFile "tests/spec/cnstr1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> y @?= mkBottomTree ""

testCnstr2 :: IO ()
testCnstr2 = do
  s <- readFile "tests/spec/cnstr2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newSimpleStruct
      ["a", "b"]
      [ ("a", mkNewTree (TNRefCycle (RefCycle True)))
      ,
        ( "b"
        , mkFuncTree $
            mkBinaryOp
              AST.Unify
              (\_ _ -> throwError "not implemented")
              (mkAtomTree $ Int 200)
              ( mkNewTree . TNFunc $
                  mkBinaryOp
                    AST.Add
                    (\_ _ -> throwError "not implemented")
                    (mkSimpleLink $ pathFromList [strSel "a"])
                    (mkAtomTree $ Int 100)
              )
        )
      ]

expandWithPatterns :: [PatternStructField Tree] -> Tree -> Tree
expandWithPatterns ps t = case t of
  Tree{treeNode = TNStruct s} ->
    mkStructTree $
      s
        { stcPatterns = ps
        }
  _ -> error "Not a struct"

testPat1 :: IO ()
testPat1 = do
  s <- readFile "tests/spec/pattern1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    expandWithPatterns
      [ PatternStructField
          { psfPattern = Bounds{bdsList = [BdType BdString]}
          , psfValue = newFieldsStruct [("a", mkAtomTree $ Int 1)]
          }
      ]
      ( newFieldsStruct
          [
            ( "y"
            , newFieldsStruct
                [ ("a", mkAtomTree $ Int 1)
                , ("b", mkAtomTree $ Int 2)
                ]
            )
          ]
      )

testPat2 :: IO ()
testPat2 = do
  s <- readFile "tests/spec/pattern2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newFieldsStruct
      [
        ( "nameMap"
        , expandWithPatterns
            [ PatternStructField
                { psfPattern = Bounds{bdsList = [BdType BdString]}
                , psfValue =
                    newFieldsStruct
                      [ ("firstName", mkBoundsTree [BdType BdString])
                      ,
                        ( "nickName"
                        , mkFuncTree $
                            mkBinaryOp
                              AST.Disjunction
                              (\_ _ -> throwError "not implemented")
                              (mkSimpleLink $ pathFromList [strSel "firstName"])
                              (mkBoundsTree [BdType BdString])
                        )
                      ]
                }
            ]
            $ newFieldsStruct
              [
                ( "hank"
                , newFieldsStruct
                    [ ("firstName", mkAtomTree $ String "Hank")
                    ,
                      ( "nickName"
                      , mkNewTree . TNDisj $
                          Disj
                            (Just $ mkAtomTree $ String "Hank")
                            [ mkAtomTree $ String "Hank"
                            , mkBoundsTree [BdType BdString]
                            ]
                      )
                    ]
                )
              ]
        )
      ]

testPat3 :: IO ()
testPat3 = do
  s <- readFile "tests/spec/pattern3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> y @?= exp
 where
  exp = mkBottomTree ""

testClose1 :: IO ()
testClose1 = do
  s <- readFile "tests/spec/close1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> y @?= mkBottomTree ""

testClose2 :: IO ()
testClose2 = do
  s <- readFile "tests/spec/close2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> y @?= mkBottomTree ""

testClose3 :: IO ()
testClose3 = do
  s <- readFile "tests/spec/close3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newFieldsStruct
      [ ("c1", newFieldsStruct [("x", sxc), ("y", sycp)])
      , ("c2", newFieldsStruct [("x", sxc), ("y", sycp)])
      , ("c3", newFieldsStruct [("x", sxc), ("y", syc), ("z", sycp)])
      ]

  patterna =
    [ PatternStructField
        { psfPattern = Bounds{bdsList = [BdStrMatch $ BdReMatch "a"]}
        , psfValue = mkBoundsTree [BdType BdInt]
        }
    ]
  sxc =
    expandWithClosed True $
      expandWithPatterns patterna $
        newFieldsStruct []
  syc =
    expandWithClosed True $
      newFieldsStruct [("a", mkAtomTree $ Int 1)]
  sycp =
    expandWithClosed True $
      expandWithPatterns patterna $
        newFieldsStruct [("a", mkAtomTree $ Int 1)]

expandWithClosed :: Bool -> Tree -> Tree
expandWithClosed closesd t = case t of
  Tree{treeNode = TNStruct s} -> mkStructTree $ s{stcClosed = closesd}
  _ -> error "Not a struct"

specTests :: TestTree
specTests =
  testGroup
    "specTest"
    [ testCase "basic" testBasic
    , testCase "bottom" testBottom
    , testCase "unaryop" testUnaryOp
    , testCase "binop" testBinop
    , testCase "binop2" testBinOp2
    , testCase "binop3" testBinOp3
    , testCase "binop_cmp_eq" testBinOpCmpEq
    , testCase "binop_cmp_ne" testBinOpCmpNE
    , testCase "bounds1" testBounds1
    , testCase "bounds2" testBounds2
    , testCase "disj1" testDisj1
    , testCase "disj2" testDisj2
    , testCase "disj3" testDisj3
    , testCase "disj4" testDisj4
    , testCase "vars1" testVars1
    , testCase "vars2" testVars2
    , testCase "vars3" testVars3
    , testCase "selector1" testSelector1
    , testCase "unify1" testUnify1
    , testCase "unify2" testUnify2
    , testCase "unify3" testUnify3
    , testCase "unify4" testUnify4
    , testCase "cycles1" testCycles1
    , testCase "cycles2" testCycles2
    , testCase "cycles3" testCycles3
    , testCase "cycles4" testCycles4
    , testCase "cycles5" testCycles5
    , testCase "cycles6" testCycles6
    , testCase "cycles7" testCycles7
    , testCase "incomplete" testIncomplete
    , testCase "dup1" testDup1
    , testCase "dup2" testDup2
    , testCase "dup3" testDup3
    , testCase "ref1" testRef1
    , testCase "ref2" testRef2
    , testCase "ref3" testRef3
    , testCase "ref3" testRef5
    , testCase "struct1" testStruct1
    , testCase "struct2" testStruct2
    , testCase "struct3" testStruct3
    , testCase "struct4" testStruct4
    , testCase "struct5" testStruct5
    , testCase "list1" testList1
    , testCase "index1" testIndex1
    , testCase "cnstr1" testCnstr1
    , testCase "cnstr2" testCnstr2
    , testCase "pattern1" testPat1
    , testCase "pattern2" testPat2
    , testCase "pattern3" testPat3
    , testCase "close1" testClose1
    , testCase "close2" testClose2
    , testCase "close3" testClose3
    ]

cmpStructs :: Tree -> Tree -> IO ()
cmpStructs (Tree{treeNode = TNStruct act}) (Tree{treeNode = TNStruct exp}) = do
  assertEqual "labels" (stcOrdLabels exp) (stcOrdLabels act)
  assertEqual "fields-length" (length $ stcSubs exp) (length $ stcSubs act)
  mapM_ (\(k, v) -> assertEqual (show k) v (stcSubs act Map.! k)) (Map.toList $ stcSubs exp)
  mapM_ (\(k, v) -> assertEqual (show k) (stcSubs exp Map.! k) v) (Map.toList $ stcSubs act)
  assertEqual "patterns" (stcPatterns exp) (stcPatterns act)
  assertEqual "pendings" (stcPendSubs exp) (stcPendSubs act)
cmpStructs v1 v2 = assertFailure $ printf "Not structs: %s, %s" (show v1) (show v2)

cmpExpStructs :: Tree -> Tree -> IO ()
cmpExpStructs (Tree{treeNode = TNStruct act}) (Tree{treeNode = TNStruct exp}) = do
  mapM_ cmp (Map.toList $ stcSubs exp)
 where
  cmp (k, v) =
    if k `Map.member` stcSubs act
      then assertEqual (show k) v (stcSubs act Map.! k)
      else assertFailure $ printf "Field %s not found" (show k)
cmpExpStructs v1 v2 = assertFailure $ printf "Not structs: %s, %s" (show v1) (show v2)
