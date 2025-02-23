module SpecTest where

import qualified AST
import Class
import Config
import Control.Monad (unless)
import Control.Monad.Except (runExcept, runExceptT, throwError)
import Data.ByteString.Builder
import qualified Data.IntMap.Strict as IntMap
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Debug.Trace
import Eval (runTreeIO)
import GHC.Stack (HasCallStack)
import Parser
import Path
import System.IO (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf (printf)
import Value.Tree

newCompleteStruct :: [String] -> [(String, Tree)] -> Tree
newCompleteStruct labels subs =
  mkNewTree . TNStruct $
    emptyStruct
      { stcSubs =
          Map.fromList
            ( map
                ( \(k, v) ->
                    let (s, a) = selAttr k
                     in ( Path.StringTASeg s
                        , SField $ emptyFieldMker v a
                        )
                )
                subs
            )
      , stcOrdLabels =
          if Prelude.null labels
            then map (Path.StringTASeg . fst . selAttr . fst) subs
            else map (Path.StringTASeg . fst . selAttr) labels
      , stcPendSubs = IntMap.empty
      , stcCnstrs = IntMap.empty
      , stcClosed = False
      }
 where
  selAttr :: String -> (String, LabelAttr)
  selAttr s
    | Prelude.null s = (s, defaultLabelAttr)
    | length s >= 2 && head s == '"' && last s == '"' =
        let
          ns = drop 1 $ take (length s - 1) s
         in
          (ns, defaultLabelAttr{lbAttrIsVar = False})
    | last s == '?' =
        let
          ns = take (length s - 1) s
          np = selAttr ns
         in
          (fst np, (snd np){lbAttrCnstr = SFCOptional})
    | last s == '!' =
        let
          ns = take (length s - 1) s
          np = selAttr ns
         in
          (fst np, (snd np){lbAttrCnstr = SFCRequired})
    | otherwise = (s, defaultLabelAttr)

newStruct :: [(String, Tree)] -> Tree
newStruct = newCompleteStruct []

mkSimpleLink :: Path.Reference -> Tree
mkSimpleLink p = mkMutableTree $ mkRefMutable p

startEval :: String -> IO (Either String Tree)
startEval s = runExceptT $ runTreeIO s

assertStructs :: Tree -> Tree -> IO ()
assertStructs (Tree{treeNode = TNStruct exp}) (Tree{treeNode = TNStruct act}) = do
  assertEqual "labels" (stcOrdLabels exp) (stcOrdLabels act)
  assertEqual "fields-length" (length $ stcSubs exp) (length $ stcSubs act)
  mapM_ (\(k, v) -> assertEqual (show k) v (stcSubs act Map.! k)) (Map.toList $ stcSubs exp)
  mapM_ (\(k, v) -> assertEqual (show k) (stcSubs exp Map.! k) v) (Map.toList $ stcSubs act)
assertStructs _ _ = assertFailure "Not structs"

strSel :: String -> Path.Selector
strSel = Path.StringSel

emptyHoriCycle :: TreeNode Tree
emptyHoriCycle = TNRefCycle (RefCycleHori (emptyTreeAddr, emptyTreeAddr))

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
        newStruct
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
        @?= newStruct
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
        $ newStruct
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
        @?= newStruct
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
        @?= newStruct
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
        @?= newStruct
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
        @?= newStruct
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
        @?= newStruct
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
        @?= newStruct
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
        @?= newStruct
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
    newStruct
      ( map
          (\(k, v) -> (k, mkAtomTree v))
          [ ("a", Int 1)
          , ("b", Int 2)
          , ("c", Int 9)
          ]
      )
  structY =
    newStruct
      ( map
          (\(k, v) -> (k, mkAtomTree v))
          [ ("e", Int 3)
          , ("f", Int 4)
          , ("g", Int 9)
          ]
      )

  structTop =
    newStruct
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
    newStruct
      ( map
          (\(k, v) -> (k, mkAtomTree v))
          [("a", Int 2), ("b", Int 2)]
      )
  structTop = newStruct [("x", structX)]

testDisj1 :: IO ()
testDisj1 = do
  s <- readFile "tests/spec/disj1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right v ->
      cmpStructs v $
        newStruct
          [ ("x1", newAtomDisj [String "tcp"] [String "tcp", String "udp"])
          , ("x2", newAtomDisj [Int 1] [Int 1, Int 2, Int 3])
          , ("x3", newAtomDisj [Int 1, Int 2] [Int 1, Int 2, Int 3])
          , ("x4", newAtomDisj [Int 2] [Int 1, Int 2, Int 3])
          , ("x5", newAtomDisj [Int 1, Int 2] [Int 1, Int 2, Int 3])
          , ("x6", newAtomDisj [] [Int 1, Int 2])
          , ("y0", newAtomDisj [] [Int 1, Int 2, Int 3])
          , ("y1", newAtomDisj [Int 2] [Int 1, Int 2, Int 3])
          , ("y2", newAtomDisj [Int 3] [Int 1, Int 2, Int 3])
          , ("z1", mkAtomTree $ Int 3)
          ]

newAtomDisj :: [Atom] -> [Atom] -> Tree
newAtomDisj d1 d2 = mkNewTree . TNDisj $ Disj (mkDefault d1) (map mkAtomTree d2)
 where
  mkDefault :: [Atom] -> Maybe Tree
  mkDefault ts = case ts of
    [] -> Nothing
    [x] -> Just $ mkAtomTree x
    xs -> Just $ newAtomDisj [] xs

newDisj :: [Tree] -> [Tree] -> Tree
newDisj d1 d2 = mkNewTree . TNDisj $ Disj (mkDefault d1) d2
 where
  mkDefault :: [Tree] -> Maybe Tree
  mkDefault ts = case ts of
    [] -> Nothing
    [x] -> Just x
    xs -> Just $ newDisj [] xs

testDisj2 :: IO ()
testDisj2 = do
  s <- readFile "tests/spec/disj2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          [
            ( "x"
            , mkNewTree . TNDisj $
                Disj
                  Nothing
                  [ newStruct
                      [("y", mkAtomTree $ Int 1), ("z", mkAtomTree $ Int 3)]
                  , newStruct [("y", mkAtomTree $ Int 2)]
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
        newStruct
          [ ("a0", newAtomDisj [] [String "tcp", String "udp"])
          , ("a1", newAtomDisj [String "tcp"] [String "tcp", String "udp"])
          , ("a2", mkAtomTree $ Int 4)
          , ("b0", newAtomDisj [Int 1, Int 2] [Int 1, Int 2, Int 3])
          , ("b1", newAtomDisj [] [Int 1, Int 2, Int 3])
          , ("c0", newAtomDisj [String "tcp"] [String "tcp", String "udp"])
          , ("c1", newAtomDisj [String "tcp"] [String "tcp", String "udp"])
          , ("c2", newAtomDisj [String "tcp"] [String "tcp"])
          , ("c3", newAtomDisj [] [String "tcp", String "udp"])
          , ("d0", newAtomDisj [Bool True] [Bool True, Bool False])
          , ("e0", newDisj [] [sa, sb])
          , ("e1", newDisj [sb] [sa, sb])
          , ("e2", newDisj [] [sa, sb])
          , ("e3", newDisj [] [sa, sab])
          , ("e4", newDisj [sb] [sa, sba, sab, sb])
          ]
 where
  sa = newStruct [("a", mkAtomTree $ Int 1)]
  sb = newStruct [("b", mkAtomTree $ Int 1)]
  sba = newStruct [("b", mkAtomTree $ Int 1), ("a", mkAtomTree $ Int 1)]
  sab = newStruct [("a", mkAtomTree $ Int 1), ("b", mkAtomTree $ Int 1)]

testDisj4 :: IO ()
testDisj4 = do
  s <- readFile "tests/spec/disj4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpStructs y $
        newStruct
          [
            ( "x"
            , mkNewTree . TNDisj $
                Disj
                  (Just $ mkAtomTree $ String "a")
                  [ mkAtomTree $ String "a"
                  , mkBoundsTree [BdType BdString]
                  ]
            )
          ,
            ( "y"
            , mkNewTree . TNDisj $
                Disj
                  (Just $ mkAtomTree $ String "a")
                  [ mkAtomTree $ String "a"
                  , mkBoundsTree [BdType BdString]
                  ]
            )
          ,
            ( "z"
            , mkNewTree . TNDisj $
                Disj
                  (Just $ mkAtomTree $ String "a")
                  [ mkAtomTree $ String "a"
                  , mkBoundsTree [BdType BdString]
                  ]
            )
          ]

testDisj5 :: IO ()
testDisj5 = do
  s <- readFile "tests/spec/disj5.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpStructs y $
        newStruct
          [ ("x1", mkAtomTree $ Int 1)
          , ("x2", mkAtomTree $ Int 1)
          , ("x3", mkAtomTree $ Int 1)
          , ("x4", mkAtomTree $ Int 1)
          ]

testDisj6 :: IO ()
testDisj6 = do
  s <- readFile "tests/spec/disj6.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> y @?= mkBottomTree ""

testDisj7 :: IO ()
testDisj7 = do
  s <- readFile "tests/spec/disj7.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> y @?= mkBottomTree ""

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
      ( map
          (\(k, v) -> (k, mkAtomTree v))
          [ ("x", Int 1)
          , ("y", Int 3)
          , ("\"x-y\"", Int 4)
          ]
      )
  fieldEDefault = newStruct [("a", newAtomDisj [Int 4] [Int 3, Int 4])]
  structE =
    mkNewTree . TNDisj $
      Disj
        (Just fieldEDefault)
        [newStruct [("a", newAtomDisj [Int 2] [Int 1, Int 2])], fieldEDefault]
  -- addrC = TreeAddr [strSel "c"]
  pendValC = mkSimpleLink $ Path.Reference [strSel "T", strSel "z"]
  -- addrF = TreeAddr [strSel "f"]
  disjF = newAtomDisj [Int 4] [Int 3, Int 4]
  expStruct =
    newStruct
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
        @?= newStruct
          ( map
              (\(k, v) -> (k, mkAtomTree v))
              [ ("a", Int 123)
              , ("d", String "hello")
              , ("b", Int 456)
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
        newStruct
          [ ("x", newStruct [("a", mkNewTree TNTop), ("b", mkNewTree TNTop)])
          , ("y", newStruct [("a", mkAtomTree $ Int 200), ("b", mkAtomTree $ Int 200)])
          ]

testUnify3 :: IO ()
testUnify3 = do
  s <- readFile "tests/spec/unify3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpStructs y $
        newStruct
          [ ("x", newStruct [("a", mkNewTree TNTop), ("b", mkNewTree TNTop)])
          , ("y", newStruct [("a", mkAtomTree $ Int 200), ("b", mkNewTree TNTop)])
          ]

testUnify4 :: IO ()
testUnify4 = do
  s <- readFile "tests/spec/unify4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpStructs y $
        newStruct
          [ ("x", newStruct [("a", mkNewTree TNTop), ("b", mkAtomTree $ Int 1)])
          , ("y", newStruct [("a", mkAtomTree $ Int 2), ("b", mkAtomTree $ Int 1)])
          , ("df", mkAtomTree $ String "x")
          ]

testUnify5 :: IO ()
testUnify5 = do
  s <- readFile "tests/spec/unify5.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y $ newStruct [("x", newStruct [("a", mkAtomTree $ Int 3)])]

testUnify6 :: IO ()
testUnify6 = do
  s <- readFile "tests/spec/unify6.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [ ("a", sij)
      , ("b", sij)
      , ("c", mkAtomTree $ Int 1)
      , ("res", sij)
      ]
  sij = newStruct [("i1", newStruct [("j1", mkAtomTree $ Int 1)])]

testUnify7 :: IO ()
testUnify7 = do
  s <- readFile "tests/spec/unify7.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp = newStruct [("x", sx), ("y", sy), ("z", sz)]
  sx = newStruct [("a", mkBoundsTree [BdType BdInt]), ("b", mkBoundsTree [BdType BdInt])]
  sy = newStruct [("a", mkAtomTree $ Int 1)]
  sz = newStruct [("a", mkAtomTree $ Int 1), ("b", mkBoundsTree [BdType BdInt])]

testUnify8 :: IO ()
testUnify8 = do
  s <- readFile "tests/spec/unify8.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp = newStruct [("res", se), ("x", se), ("a", se), ("b", se)]
  se = newStruct []

testCycles_Ref1 = do
  s <- readFile "tests/spec/cycles_ref1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          [ ("x", selfCycle)
          , ("b", selfCycle)
          , ("c", selfCycle)
          , ("d", selfCycle)
          ]
 where
  selfCycle = mkNewTree emptyHoriCycle

testCycles_Ref2 = do
  s <- readFile "tests/spec/cycles_ref2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          [
            ( "a"
            , mkNewTree (TNRefCycle RefCycleVert)
            )
          ,
            ( "b"
            , mkNewTree (TNRefCycle RefCycleVert)
            )
          ]

testCycles_Ref3 = do
  s <- readFile "tests/spec/cycles_ref3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          [ ("a", mkAtomTree $ Int 200)
          , ("b", mkAtomTree $ Int 100)
          ]

testCycles_Ref4 = do
  s <- readFile "tests/spec/cycles_ref4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          [
            ( "x"
            , newStruct
                [
                  ( "a"
                  , mkNewTree (TNRefCycle RefCycleVert)
                  )
                ,
                  ( "b"
                  , mkNewTree (TNRefCycle RefCycleVert)
                  )
                ]
            )
          ,
            ( "y"
            , newStruct [("a", mkAtomTree $ Int 200), ("b", mkAtomTree $ Int 100)]
            )
          ]

testCycles_Ref4_2 = do
  s <- readFile "tests/spec/cycles_ref4_2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          [
            ( "x"
            , newStruct
                [
                  ( "a"
                  , mkNewTree (TNRefCycle RefCycleVert)
                  )
                ,
                  ( "b"
                  , mkNewTree (TNRefCycle RefCycleVert)
                  )
                ]
            )
          ]

testCycles_Ref5 = do
  s <- readFile "tests/spec/cycles_ref5.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          [ ("a", innerStructGen ["z", "y", "x"])
          , ("b", innerStructGen ["x", "z", "y"])
          , ("c", innerStructGen ["y", "x", "z"])
          ]
 where
  innerStructGen labels =
    newCompleteStruct
      labels
      [ ("x", mkAtomTree $ Int 1)
      , ("y", mkAtomTree $ Int 2)
      , ("z", mkAtomTree $ Int 3)
      ]

testCycles_Ref6 = do
  s <- readFile "tests/spec/cycles_ref6.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          [ ("a", newDisj [] [xzy, sy1])
          , ("b", newDisj [] [sx2, zyx])
          , ("c", newDisj [] [yxz, sz3])
          ]
 where
  innerStructGen labels =
    newCompleteStruct
      labels
      [ ("x", mkAtomTree $ Int 1)
      , ("y", mkAtomTree $ Int 3)
      , ("z", mkAtomTree $ Int 2)
      ]

  sy1 = newStruct [("y", mkAtomTree $ Int 1)]
  sx2 = newStruct [("x", mkAtomTree $ Int 2)]
  sz3 = newStruct [("z", mkAtomTree $ Int 3)]

  xzy = innerStructGen ["x", "z", "y"]
  zyx = innerStructGen ["z", "y", "x"]
  yxz = innerStructGen ["y", "x", "z"]

testCycles_Ref7 = do
  s <- readFile "tests/spec/cycles_ref7.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpStructs x $
        newStruct
          [ ("x", newStruct [("a", selfCycle), ("b", selfCycle)])
          , ("y", newStruct [("a", selfCycle), ("b", mkAtomTree $ Int 2)])
          , ("z", newStruct [("a", mkAtomTree $ Int 2), ("b", mkAtomTree $ Int 2)])
          , ("dfa", mkAtomTree $ String "a")
          , ("z2", newStruct [("a", mkAtomTree $ Int 2), ("b", mkAtomTree $ Int 2)])
          ]
 where
  selfCycle = mkNewTree emptyHoriCycle

testCyclesSCErr1 = do
  s <- readFile "tests/spec/cycles_sc_err1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x -> x @?= mkBottomTree ""

testCyclesSCErr2 = do
  s <- readFile "tests/spec/cycles_sc_err2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x -> x @?= mkBottomTree ""

testCyclesSCErr3 = do
  s <- readFile "tests/spec/cycles_sc_err3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x -> x @?= mkBottomTree ""

testCyclesSCErr3_2 = do
  s <- readFile "tests/spec/cycles_sc_err3_2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x -> x @?= mkBottomTree ""

testCyclesSC1 = do
  s <- readFile "tests/spec/cycles_sc1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpStructs x $
        newStruct [("#List", listS)]
 where
  listS = newStruct [("head", mkNewTree TNTop), ("tail", mkAtomTree Null)]

testCyclesSC2 = do
  s <- readFile "tests/spec/cycles_sc2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpStructs x $
        newStruct
          [ ("#List", listS)
          ,
            ( "MyList"
            , expandWithClosed True $
                newStruct [("head", mkAtomTree $ Int 1), ("tail", mkAtomTree Null)]
            )
          ]
 where
  listS = newStruct [("head", mkNewTree TNTop), ("tail", mkAtomTree Null)]

testCyclesSC3 = do
  s <- readFile "tests/spec/cycles_sc3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpStructs x $
        newStruct
          [ ("#List", listS)
          ,
            ( "MyList"
            , expandWithClosed True $
                newStruct [("head", mkAtomTree $ Int 1), ("tail", myListInnerSC)]
            )
          ]
 where
  listS = newStruct [("head", mkNewTree TNTop), ("tail", mkAtomTree Null)]
  myListInnerSC =
    expandWithClosed True $
      newStruct [("head", mkAtomTree $ Int 2), ("tail", mkAtomTree Null)]

testCyclesSC4 = do
  s <- readFile "tests/spec/cycles_sc4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpStructs x $
        newStruct
          [ ("x", newStruct [("#List", listS)])
          ,
            ( "MyList"
            , expandWithClosed True $
                newStruct [("head", mkAtomTree $ Int 1), ("tail", myListInnerSC)]
            )
          ]
 where
  listS = newStruct [("head", mkNewTree TNTop), ("tail", mkAtomTree Null)]
  myListInnerSC =
    expandWithClosed True $
      newStruct [("head", mkAtomTree $ Int 2), ("tail", mkAtomTree Null)]

testCyclesPC1 :: IO ()
testCyclesPC1 = do
  s <- readFile "tests/spec/cycles_pc1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x -> cmpStructs x exp
 where
  exp =
    newStruct
      [
        ( "p"
        , newStruct
            [ ("a", selfCycle)
            , ("b", selfCycle)
            ]
        )
      ]
  selfCycle = mkNewTree emptyHoriCycle

testCyclesPC2 :: IO ()
testCyclesPC2 = do
  s <- readFile "tests/spec/cycles_pc2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x -> cmpStructs x exp
 where
  exp =
    newStruct
      [
        ( "p"
        , newStruct
            [ ("a", selfCycle)
            , ("b", selfCycle)
            ]
        )
      ]
  selfCycle = mkNewTree emptyHoriCycle

testCyclesPC3 :: IO ()
testCyclesPC3 = do
  s <- readFile "tests/spec/cycles_pc3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x -> cmpStructs x exp
 where
  exp =
    newStruct
      [
        ( "p"
        , newStruct
            [ ("a", selfCycle)
            , ("b", selfCycle)
            , ("\"x\"", mkAtomTree $ String "a")
            ]
        )
      ]
  selfCycle = mkNewTree emptyHoriCycle

testCyclesPC4 :: IO ()
testCyclesPC4 = do
  s <- readFile "tests/spec/cycles_pc4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x -> cmpStructs x exp
 where
  exp =
    newStruct
      [
        ( "p"
        , newStruct
            [ ("a", selfCycle)
            , ("b", selfCycle)
            , ("\"c\"", selfCycle)
            ]
        )
      ]
  selfCycle = mkNewTree emptyHoriCycle

testIncomplete :: IO ()
testIncomplete = do
  s <- readFile "tests/spec/incomplete.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
          [ ("a", mkNewTree TNTop)
          ,
            ( "b"
            , mkMutableTree $
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
        @?= newStruct
          [
            ( "z"
            , newStruct
                [ ("y", newStruct [("b", mkAtomTree $ Int 4)])
                , ("x", newStruct [("b", mkAtomTree $ Int 4)])
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
        @?= newStruct
          [
            ( "x"
            , newStruct
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
    Right y ->
      y
        @?= newStruct
          [
            ( "x"
            , newStruct
                [ ("a", mkAtomTree $ Int 1)
                , ("b", mkAtomTree $ Int 2)
                , ("c", mkAtomTree $ Int 2)
                ]
            )
          ]

testDynamicField1 :: IO ()
testDynamicField1 = do
  s <- readFile "tests/spec/dynfield1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      cmpStructs y $
        newStruct
          [ ("y", newStruct [("x", mkAtomTree $ String "a")])
          , ("\"a\"", mkAtomTree $ Int 1)
          ]

testDynamicFieldErr1 :: IO ()
testDynamicFieldErr1 = do
  s <- readFile "tests/spec/dynfield_err1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> assertBottom "values mismatch" y

testRef1 :: IO ()
testRef1 = do
  s <- readFile "tests/spec/ref1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right val' ->
      val'
        @?= newStruct
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
        @?= newStruct
          [ ("a", mkAtomTree $ Int 1)
          ,
            ( "x"
            , newStruct
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
        @?= newStruct
          [
            ( "x"
            , newStruct
                [ ("a", mkAtomTree $ Int 1)
                , ("c", mkAtomTree $ Int 2)
                ]
            )
          ,
            ( "d"
            , newStruct
                [
                  ( "y"
                  , newStruct
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
      cmpStructs x $
        newStruct
          [ ("b", mkAtomTree $ Int 1)
          , ("c", newStruct [("z", mkAtomTree $ Int 1)])
          , ("df", mkAtomTree $ String "c")
          ]

testRef6 :: IO ()
testRef6 = do
  s <- readFile "tests/spec/ref6.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpStructs x $
        newStruct
          [ ("y", newStruct [("c", mkBoundsTree [BdType BdInt]), ("d", mkBoundsTree [BdType BdString])])
          , ("B", newStruct [("d", mkAtomTree $ Int 2)])
          ,
            ( "A"
            , newStruct
                [ ("d", mkAtomTree $ Int 2)
                , ("b", newStruct [("c", mkBoundsTree [BdType BdInt]), ("d", mkBoundsTree [BdType BdString])])
                ]
            )
          ]

testRef7 :: IO ()
testRef7 = do
  s <- readFile "tests/spec/ref7.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpStructs x $
        newStruct
          [ ("y", newStruct [("c", mkBoundsTree [BdType BdInt]), ("e", mkAtomTree $ Int 2)])
          , ("r1", newStruct [("d", mkAtomTree $ Int 2)])
          , ("r2", newStruct [("e", mkAtomTree $ Int 2)])
          ,
            ( "A"
            , newStruct
                [ ("d", mkAtomTree $ Int 2)
                , ("b", newStruct [("c", mkBoundsTree [BdType BdInt]), ("e", mkAtomTree $ Int 2)])
                ]
            )
          ]

testRef8 :: IO ()
testRef8 = do
  s <- readFile "tests/spec/ref8.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpStructs x $
        newStruct
          [ ("y", sa)
          , ("x", sa)
          , ("z", sb)
          ]
 where
  sb = newStruct [("b", mkAtomTree $ Int 3)]
  sa = newStruct [("a", sb)]

testRef9 :: IO ()
testRef9 = do
  s <- readFile "tests/spec/ref9.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right x ->
      cmpStructs x $
        newStruct
          [ ("a", mkAtomTree $ Int 1)
          , ("x", sa)
          ]
 where
  sa = newStruct [("d", mkAtomTree $ Int 1), ("z", mkAtomTree $ Int 1)]

testRefErr1 :: IO ()
testRefErr1 = do
  s <- readFile "tests/spec/ref_err1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> assertBottom "not found" y

testStruct1 :: IO ()
testStruct1 = do
  s <- readFile "tests/spec/struct1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y ->
      y
        @?= newStruct [("s1", s1)]
 where
  s1 =
    newStruct
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
    Right y -> y @?= newStruct [("a", a)]
 where
  a =
    newStruct
      [ ("b", ab)
      , ("c", mkAtomTree $ Int 42)
      ]
  ab =
    newStruct
      [ ("c", abc)
      , ("d", mkAtomTree $ Int 12)
      ]
  abc =
    newStruct [("d", mkAtomTree $ Int 123)]

testStruct3 :: IO ()
testStruct3 = do
  s <- readFile "tests/spec/struct3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  sGen :: Tree -> Tree
  sGen t = newStruct [("f", t)]

  sGen2 :: Tree -> Tree
  sGen2 t = newStruct [("f!", t)]

  exp =
    newStruct
      [ ("x0", sGen $ mkAtomTree $ Int 3)
      , ("x1", sGen $ mkAtomTree $ Int 3)
      , ("x2", sGen $ mkBoundsTree [BdType BdInt])
      , ("x3", sGen2 (mkBoundsTree [BdNumCmp $ BdNumCmpCons BdLT (NumInt 1)]))
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
      [ ("a", mkAtomTree $ String "foo")
      , ("b", mkAtomTree $ String "bar")
      , ("\"foo\"", mkAtomTree $ String "baz")
      , ("\"foobar\"", mkAtomTree $ String "qux")
      , ("\"bar\"!", mkBoundsTree [BdType BdString])
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
    newStruct
      [ ("a", newStruct [("c", mkAtomTree $ String "b")])
      ,
        ( "b"
        , newStruct
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
    newStruct
      [ ("x0", mkNewTree . TNList $ List (map mkAtomTree [Int 1, Int 4, Int 9]))
      , ("x1", mkNewTree . TNList $ List (map mkAtomTree [Float 1.0, Bool True, String "hello"]))
      ]

testIndex1 :: IO ()
testIndex1 = do
  s <- readFile "tests/spec/index1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  ma = mkAtomTree
  list12 = mkListTree [ma $ Int 1, ma $ Int 2]
  list34 = mkListTree [ma $ Int 3, ma $ Int 4]
  exp =
    newStruct
      [ ("x0", mkListTree [ma $ Int 1, ma $ Int 4, ma $ Int 9])
      , ("x1", ma $ Int 14)
      , ("x2", ma $ Int 4)
      , ("x3", ma $ Int 9)
      , ("x4", ma $ Int 3)
      , ("x5", ma $ Int 1)
      , ("x", newDisj [list34] [list12, list34])
      , ("y", newDisj [ma $ Int 1] [mkBoundsTree [BdType BdInt], ma $ Int 1])
      , ("z", ma $ Int 4)
      ]

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
    newStruct
      [ ("a", mkNewTree emptyHoriCycle)
      ,
        ( "b"
        , mkMutableTree $
            mkBinaryOp
              AST.Unify
              (\_ _ -> throwError "not implemented")
              (mkAtomTree $ Int 200)
              ( mkNewTree . TNMutable $
                  mkBinaryOp
                    AST.Add
                    (\_ _ -> throwError "not implemented")
                    (mkSimpleLink $ Path.Reference [strSel "a"])
                    (mkAtomTree $ Int 100)
              )
        )
      ]

expandWithPatterns :: [StructCnstr Tree] -> Tree -> Tree
expandWithPatterns ps t = case t of
  Tree{treeNode = TNStruct s} ->
    mkStructTree $
      s
        { stcCnstrs = IntMap.fromList $ map (\v -> (0, v)) ps
        }
  _ -> error "Not a struct"

testPat1 :: IO ()
testPat1 = do
  s <- readFile "tests/spec/pat1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    expandWithPatterns
      [ StructCnstr
          { scsPattern = mkBoundsTree [BdType BdString]
          , scsValue = newStruct [("a", mkAtomTree $ Int 1)]
          , scsID = 0
          }
      ]
      ( newStruct
          [
            ( "y"
            , newStruct
                [ ("b", mkAtomTree $ Int 2)
                , ("a", mkAtomTree $ Int 1)
                ]
            )
          ]
      )

testPat2 :: IO ()
testPat2 = do
  s <- readFile "tests/spec/pat2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [
        ( "nameMap"
        , expandWithPatterns
            [ StructCnstr
                { scsPattern = mkBoundsTree [BdType BdString]
                , scsValue =
                    newStruct
                      [ ("firstName", mkBoundsTree [BdType BdString])
                      ,
                        ( "nickName"
                        , mkMutableTree $
                            mkBinaryOp
                              AST.Disjunction
                              (\_ _ -> throwError "not implemented")
                              (mkSimpleLink $ Path.Reference [strSel "firstName"])
                              (mkBoundsTree [BdType BdString])
                        )
                      ]
                , scsID = 0
                }
            ]
            $ newStruct
              [
                ( "hank"
                , newStruct
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
  s <- readFile "tests/spec/pat3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> assertBottom "conflict" y

testPat4 :: IO ()
testPat4 = do
  s <- readFile "tests/spec/pat4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> assertBottom "conflict" y

testPatCons1 :: IO ()
testPatCons1 = do
  s <- readFile "tests/spec/pat_cons1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp = newStruct [("x", sx), ("y", sy)]
  sx =
    expandWithPatterns
      [ StructCnstr
          { scsPattern = mkBoundsTree [BdStrMatch (BdReMatch "a")]
          , scsValue = newStruct [("f1", mkAtomTree $ Int 1)]
          , scsID = 0
          }
      ]
      sxInner
  sxInner =
    newStruct
      [ ("a", newStruct [("f2", mkAtomTree $ Int 2), ("f1", mkAtomTree $ Int 1)])
      , ("b", newStruct [("f3", mkAtomTree $ Int 3)])
      ]
  sy =
    newStruct
      [
        ( "z"
        , mkBoundsTree [BdStrMatch (BdReMatch "a")]
        )
      ]

testPatCons1Err :: IO ()
testPatCons1Err = do
  s <- readFile "tests/spec/pat_cons1_err.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> assertBottom "values not unifiable" y

testPatCons2 :: IO ()
testPatCons2 = do
  s <- readFile "tests/spec/pat_cons2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp = newStruct [("x", sx), ("y", sy)]
  sx =
    expandWithPatterns
      [ StructCnstr
          { scsPattern = mkBoundsTree [BdStrMatch (BdReMatch "a")]
          , scsValue = newStruct [("f1", mkAtomTree $ Int 1)]
          , scsID = 0
          }
      ]
      sxInner
  sxInner =
    newStruct
      [ ("a", newStruct [("f2", mkAtomTree $ Int 2), ("f1", mkAtomTree $ Int 1)])
      , ("b", mkAtomTree $ Int 1)
      ]
  sy =
    newStruct
      [
        ( "z"
        , mkBoundsTree [BdStrMatch (BdReMatch "a")]
        )
      ]

testPatCons3 :: IO ()
testPatCons3 = do
  s <- readFile "tests/spec/pat_cons3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp = newStruct [("x", sx), ("y", sy)]
  sx =
    expandWithPatterns
      [ StructCnstr
          { scsPattern = mkBoundsTree [BdStrMatch (BdReMatch "a")]
          , scsValue = newStruct [("f1", mkAtomTree $ Int 1)]
          , scsID = 0
          }
      ]
      sxInner
  sxInner =
    newStruct
      [ ("a", newStruct [("f2", mkAtomTree $ Int 2), ("f1", mkAtomTree $ Int 1)])
      , ("\"b\"", newStruct [("f3", mkAtomTree $ Int 3)])
      ]
  sy =
    newStruct
      [
        ( "z"
        , mkBoundsTree [BdStrMatch (BdReMatch "a")]
        )
      ]

testPatDyn1 :: IO ()
testPatDyn1 = do
  s <- readFile "tests/spec/pat_dyn1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp = newStruct [("x", sx), ("y", sy)]
  sx =
    expandWithPatterns
      [ StructCnstr
          { scsPattern = mkBoundsTree [BdType BdString]
          , scsValue = newStruct [("f1", mkAtomTree $ Int 1)]
          , scsID = 0
          }
      ]
      sxInner
  sxInner =
    newStruct
      [ ("\"a\"", newStruct [("f2", mkAtomTree $ Int 2), ("f1", mkAtomTree $ Int 1)])
      ]
  sy =
    newStruct
      [
        ( "z"
        , mkAtomTree $ String "a"
        )
      ]

testPatIncmpl1 :: IO ()
testPatIncmpl1 = do
  s <- readFile "tests/spec/pat_incmpl1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp = newStruct [("x", sx), ("y", sy)]
  sx =
    expandWithPatterns
      [ StructCnstr
          { scsPattern = mkSimpleLink $ Path.Reference [strSel "y", strSel "s"]
          , scsValue = newStruct [("f1", mkAtomTree $ Int 1)]
          , scsID = 0
          }
      ]
      sxInner
  sxInner = newStruct [("a", mkAtomTree $ Int 3)]
  sy = newStruct []

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
    newStruct
      [ ("c1", newStruct [("x", sxc), ("y", sycp)])
      , ("c2", newStruct [("x", sxc), ("y", sycp)])
      , ("c3", newStruct [("x", sxc), ("y", syc), ("z", sycp)])
      ]

  patterna =
    [ StructCnstr
        { scsPattern = mkBoundsTree [BdStrMatch $ BdReMatch "a"]
        , scsValue = mkBoundsTree [BdType BdInt]
        , scsID = 0
        }
    ]
  sxc =
    expandWithClosed True $
      expandWithPatterns patterna $
        newStruct []
  syc =
    expandWithClosed True $
      newStruct [("a", mkAtomTree $ Int 1)]
  sycp =
    expandWithClosed True $
      expandWithPatterns patterna $
        newStruct [("a", mkAtomTree $ Int 1)]

expandWithClosed :: Bool -> Tree -> Tree
expandWithClosed closesd t = case t of
  Tree{treeNode = TNStruct s} -> mkStructTree $ s{stcClosed = closesd}
  _ -> error "Not a struct"

testEmbed1 :: IO ()
testEmbed1 = do
  s <- readFile "tests/spec/embed1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [ ("c1", sab)
      , ("c2", sCab)
      , ("c3", sCab)
      ]

  sab = newStruct [("a", mkAtomTree $ Int 1), ("b", mkAtomTree $ Int 2)]
  sCab = expandWithClosed True $ newStruct [("a", mkAtomTree $ Int 1), ("b", mkAtomTree $ Int 2)]

testEmbed2 :: IO ()
testEmbed2 = do
  s <- readFile "tests/spec/embed2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp = expandWithClosed True $ newStruct [("x", mkAtomTree $ Int 1)]

testEmbed3 :: IO ()
testEmbed3 = do
  s <- readFile "tests/spec/embed3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [ ("c1", mkAtomTree $ Int 1)
      , ("c2", mkAtomTree $ String "a")
      , ("c3", newAtomDisj [] [Int 1, Int 2])
      , ("c5", mkNewTree TNTop)
      ]

testEmbed4 :: IO ()
testEmbed4 = do
  s <- readFile "tests/spec/embed4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [ ("c1", mkAtomTree $ Int 1)
      , ("c2", mkAtomTree $ String "a")
      , ("c3", newAtomDisj [] [Int 1, Int 2])
      , ("c5", mkAtomTree $ Int 1)
      ]

testDef1 :: IO ()
testDef1 = do
  s <- readFile "tests/spec/def1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [ ("#S", sSBool)
      , ("m", expandWithClosed True sSC)
      ]
  sSBool = newStruct [("a", saBool)]
  saBool = newStruct [("c?", mkBoundsTree [BdType BdBool])]
  sSC = expandWithClosed True $ newStruct [("a", saC)]
  saC = expandWithClosed True $ newStruct [("c", mkAtomTree $ Bool True)]

testDef3 :: IO ()
testDef3 = do
  s <- readFile "tests/spec/def3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [ ("#D", djD)
      , ("#OneOf", oneOf)
      , ("D1", expandWithClosed True $ newStruct [("a", mkAtomTree $ Int 12), ("c", mkAtomTree $ Int 22)])
      ]

  djD =
    newDisj
      []
      [ expandWithClosed True $ newStruct [("a", mkBoundsTree [BdType BdInt]), ("c", mkBoundsTree [BdType BdInt])]
      , expandWithClosed True $ newStruct [("b", mkBoundsTree [BdType BdInt]), ("c", mkBoundsTree [BdType BdInt])]
      ]
  oneOf =
    newDisj
      []
      [ newStruct [("a", mkBoundsTree [BdType BdInt])]
      , newStruct [("b", mkBoundsTree [BdType BdInt])]
      ]

testDef5 :: IO ()
testDef5 = do
  s <- readFile "tests/spec/def5.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [ ("#A", sA)
      , ("B", sBC)
      , ("y", sY)
      ]

  sA = newStruct [("a", mkBoundsTree [BdType BdInt])]
  sBC =
    expandWithClosed True $
      newStruct
        [ ("b", newStruct [("c", mkBoundsTree [BdType BdInt])])
        , ("a", mkBoundsTree [BdType BdInt])
        ]
  sY =
    newStruct
      [ ("c", mkBoundsTree [BdType BdInt])
      , ("d", mkAtomTree $ Int 3)
      ]

testDefErr1 :: IO ()
testDefErr1 = do
  s <- readFile "tests/spec/def_err1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> y @?= mkBottomTree ""

testDefErr2 :: IO ()
testDefErr2 = do
  s <- readFile "tests/spec/def_err2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> y @?= mkBottomTree ""

testDefErr3 :: IO ()
testDefErr3 = do
  s <- readFile "tests/spec/def_err3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> y @?= mkBottomTree ""

testLet1 :: IO ()
testLet1 = do
  s <- readFile "tests/spec/let1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [ ("x1", mkAtomTree $ Int 1)
      , ("x2", mkAtomTree $ Int 1)
      , ("x3", mkAtomTree $ Int 2)
      ]

testLet2 :: IO ()
testLet2 = do
  s <- readFile "tests/spec/let2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp =
    newStruct
      [ ("a", newStruct [("y", mkSimpleLink $ Path.Reference [strSel "x", strSel "b"])])
      , ("b", newStruct [("z", mkAtomTree $ Int 1)])
      ]

testLet3 :: IO ()
testLet3 = do
  s <- readFile "tests/spec/let3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> cmpStructs y exp
 where
  exp = newStruct [("x", mkAtomTree $ Int 1)]

testLetErr1 :: IO ()
testLetErr1 = do
  s <- readFile "tests/spec/let_err1.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> assertBottom "unreferenced" y

testLetErr2 :: IO ()
testLetErr2 = do
  s <- readFile "tests/spec/let_err2.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> assertBottom "can not have both alias and field with name" y

testLetErr3 :: IO ()
testLetErr3 = do
  s <- readFile "tests/spec/let_err3.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> assertBottom "can not have both alias and field with name" y

testLetErr4 :: IO ()
testLetErr4 = do
  s <- readFile "tests/spec/let_err4.cue"
  val <- startEval s
  case val of
    Left err -> assertFailure err
    Right y -> assertBottom "redeclared in same scope" y

-- | Compare two struct fields. Other elements such as local bindings are ignored.
cmpStructs ::
  (HasCallStack) =>
  -- | act
  Tree ->
  -- | exp
  Tree ->
  IO ()
cmpStructs = cmpStructsMsg ""

cmpStructsMsg :: (HasCallStack) => String -> Tree -> Tree -> IO ()
cmpStructsMsg msg (Tree{treeNode = TNStruct act}) (Tree{treeNode = TNStruct exp}) = do
  assertEqual (withMsg msg "labels") (stcOrdLabels exp) (stcOrdLabels act)
  assertEqual (withMsg msg "fields-length") (length expFields) (length actFields)
  mapM_
    ( \(k, v) -> cmpStructVals (show k) (actFields Map.! k) v
    )
    (Map.toList expFields)
  mapM_
    ( \(k, v) -> cmpStructVals (show k) v (expFields Map.! k)
    )
    (Map.toList actFields)
  assertEqual (withMsg msg "patterns") (IntMap.elems $ stcCnstrs exp) (IntMap.elems $ stcCnstrs act)
  -- -- We only need to compare valid pendings.
  -- assertEqual
  --   (withMsg msg "pendings")
  --   (IntMap.elems $ stcPendSubs exp)
  --   (IntMap.elems $ stcPendSubs act)
  assertEqual (withMsg msg "close") (stcClosed exp) (stcClosed act)
 where
  onlyField :: Map.Map StructTASeg (StructVal Tree) -> Map.Map StructTASeg (StructVal Tree)
  onlyField =
    Map.filterWithKey
      ( \sel sv -> case sv of
          SField _ -> True
          _ -> False
      )

  expFields = onlyField $ stcSubs exp
  actFields = onlyField $ stcSubs act
cmpStructsMsg msg act exp = assertEqual msg exp act

cmpStructVals :: (HasCallStack) => String -> StructVal Tree -> StructVal Tree -> IO ()
cmpStructVals msg (SField act) (SField exp) = do
  cmpStructsMsg (withMsg msg "field") (ssfValue act) (ssfValue exp)
  assertEqual (withMsg msg "attr") (ssfAttr exp) (ssfAttr act)
cmpStructVals msg act exp = assertEqual msg exp act

withMsg :: String -> String -> String
withMsg msg s = if Prelude.null msg then s else msg ++ ": " ++ s

assertBottom :: String -> Tree -> IO ()
assertBottom msg (Tree{treeNode = TNBottom (Bottom err)}) =
  unless (msg `isInfixOf` err) $
    assertFailure (printf "in bottom msg, \"%s\" not found in \"%s\"" msg err)
assertBottom msg v = assertFailure $ printf "Not a bottom: %s" (show v)

specTests :: TestTree
specTests =
  testGroup
    "specTest"
    [ testCase "basic" testBasic
    , testCase "binop" testBinop
    , testCase "binop2" testBinOp2
    , testCase "binop3" testBinOp3
    , testCase "binop_cmp_eq" testBinOpCmpEq
    , testCase "binop_cmp_ne" testBinOpCmpNE
    , testCase "bottom" testBottom
    , testCase "bounds1" testBounds1
    , testCase "bounds2" testBounds2
    , testCase "close1" testClose1
    , testCase "close2" testClose2
    , testCase "close3" testClose3
    , testCase "cnstr1" testCnstr1
    , testCase "cnstr2" testCnstr2
    , testCase "cycles_pc1" testCyclesPC1
    , testCase "cycles_pc2" testCyclesPC2
    , testCase "cycles_pc3" testCyclesPC3
    , testCase "cycles_pc4" testCyclesPC4
    , testCase "cycles_ref1" testCycles_Ref1
    , testCase "cycles_ref2" testCycles_Ref2
    , testCase "cycles_ref3" testCycles_Ref3
    , testCase "cycles_ref4" testCycles_Ref4
    , testCase "cycles_ref4_2" testCycles_Ref4_2
    , testCase "cycles_ref5" testCycles_Ref5
    , testCase "cycles_ref6" testCycles_Ref6
    , testCase "cycles_ref7" testCycles_Ref7
    , testCase "cycles_sc1" testCyclesSC1
    , testCase "cycles_sc2" testCyclesSC2
    , testCase "cycles_sc3" testCyclesSC3
    , testCase "cycles_sc4" testCyclesSC4
    , testCase "cycles_sc_err1" testCyclesSCErr1
    , testCase "cycles_sc_err2" testCyclesSCErr2
    , testCase "cycles_sc_err3" testCyclesSCErr3
    , testCase "cycles_sc_err3_2" testCyclesSCErr3_2
    , testCase "def1" testDef1
    , testCase "def3" testDef3
    , testCase "def5" testDef5
    , testCase "def_err1" testDefErr1
    , testCase "def_err2" testDefErr2
    , testCase "def_err3" testDefErr3
    , testCase "disj1" testDisj1
    , testCase "disj2" testDisj2
    , testCase "disj3" testDisj3
    , testCase "disj4" testDisj4
    , testCase "disj5" testDisj5
    , testCase "disj6" testDisj6
    , testCase "disj7" testDisj7
    , testCase "dup1" testDup1
    , testCase "dup2" testDup2
    , testCase "dup3" testDup3
    , testCase "dynfield1" testDynamicField1
    , testCase "dynfield_err1" testDynamicFieldErr1
    , testCase "embed1" testEmbed1
    , testCase "embed2" testEmbed2
    , testCase "embed3" testEmbed3
    , testCase "embed4" testEmbed4
    , testCase "incomplete" testIncomplete
    , testCase "index1" testIndex1
    , testCase "let1" testLet1
    , testCase "let2" testLet2
    , testCase "let3" testLet3
    , testCase "let_err1" testLetErr1
    , testCase "let_err2" testLetErr2
    , testCase "let_err3" testLetErr3
    , testCase "let_err4" testLetErr4
    , testCase "list1" testList1
    , testCase "pat1" testPat1
    , testCase "pat2" testPat2
    , testCase "pat3" testPat3
    , testCase "pat4" testPat4
    , testCase "pat_cons1" testPatCons1
    , testCase "pat_cons1_err" testPatCons1Err
    , testCase "pat_cons2" testPatCons2
    , testCase "pat_cons3" testPatCons3
    , testCase "pat_dyn1" testPatDyn1
    , testCase "pat_incmpl1" testPatIncmpl1
    , testCase "ref1" testRef1
    , testCase "ref2" testRef2
    , testCase "ref3" testRef3
    , testCase "ref5" testRef5
    , testCase "ref6" testRef6
    , testCase "ref7" testRef7
    , testCase "ref8" testRef8
    , testCase "ref9" testRef9
    , testCase "ref_err1" testRefErr1
    , testCase "selector1" testSelector1
    , testCase "struct1" testStruct1
    , testCase "struct2" testStruct2
    , testCase "struct3" testStruct3
    , testCase "struct4" testStruct4
    , testCase "struct5" testStruct5
    , testCase "unaryop" testUnaryOp
    , testCase "unify1" testUnify1
    , testCase "unify2" testUnify2
    , testCase "unify3" testUnify3
    , testCase "unify4" testUnify4
    , testCase "unify5" testUnify5
    , testCase "unify6" testUnify6
    , testCase "unify7" testUnify7
    , testCase "unify8" testUnify8
    , testCase "vars1" testVars1
    , testCase "vars2" testVars2
    , testCase "vars3" testVars3
    ]
