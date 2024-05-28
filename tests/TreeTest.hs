{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module TreeTest where

import qualified AST
import Control.Monad.Except
  ( MonadError,
    runExcept,
    runExceptT,
    throwError,
  )
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Logger (MonadLogger, runNoLoggingT, runStderrLoggingT)
import Control.Monad.State (StateT (runStateT))
import Control.Monad.State.Strict (MonadState)
import Data.Either (fromRight)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Path
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
  ( assertBool,
    assertEqual,
    assertFailure,
    testCase,
  )
import Tree

edgesGen :: [(String, String)] -> [(Path, Path)]
edgesGen = map (\(x, y) -> (Path [StringSelector x], Path [StringSelector y]))

strsToPath :: [String] -> [Path]
strsToPath = map (\x -> Path [StringSelector x])

testDepsHasCycle :: IO ()
testDepsHasCycle =
  let deps1 = edgesGen [("a", "b"), ("b", "c"), ("c", "a")]
      result1 = depsHasCycle deps1
      deps2 = edgesGen [("a", "b"), ("b", "c"), ("c", "d")]
      result2 = depsHasCycle deps2
   in do
        assertEqual "depsHasCycle" True result1
        assertEqual "depsHasCycle" False result2

selY = StringSelector "y"

pathY = Path [selY]

selZ = StringSelector "z"

pathZ = Path [selZ]

selX1 = StringSelector "x1"

pathX1 = Path [selX1]

selX2 = StringSelector "x2"

pathX2 = Path [selX2]

bottomExpr = AST.litCons AST.BottomLit

treeCursorStructTest :: IO ()
treeCursorStructTest =
  (runStderrLoggingT $ runExceptT test) >>= \case
    Left err -> assertFailure err
    Right _ -> return ()
  where
    mkSimple :: (String, TreeNode) -> TreeNode
    mkSimple pair =
      TNScope $
        emptyTNScope
          { trsOrdLabels = [fst pair],
            trsSubs = Map.fromList [pair]
          }
    -- { a: { b: { c: 42 } } }
    holderC = mkSimple ("c", mkTreeLeaf $ Int 42)
    holderB = mkSimple ("b", holderC)
    holderA = mkSimple ("a", holderB)
    selA = StringSelector "a"
    selB = StringSelector "b"
    selC = StringSelector "c"

    test :: (MonadError String m, MonadIO m, MonadLogger m) => m ()
    test =
      let rootTC = (TNRoot $ TNScope emptyTNScope, [])
          topTC = fromJust $ goDownTCSel StartSelector rootTC
       in do
            tc <-
              insertTCScope selA [] Set.empty topTC
                >>= insertTCScope selB [] Set.empty
                >>= insertTCLeafValue selC (Int 42)
                >>= propTopTC

            let sva = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector]) tc
            liftIO $ assertEqual "struct a" holderA sva
            --
            let svb = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector, selA]) tc
            liftIO $ assertEqual "struct b" holderB svb
            --
            let trc = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector, selA, selB]) tc
            liftIO $ assertEqual "struct c" holderC trc

            let vl = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector, selA, selB, selC]) tc
            liftIO $ assertEqual "leaf value" (mkTreeLeaf $ Int 42) vl
            return ()

treeTests :: TestTree
treeTests =
  testGroup
    "treeTest"
    [ testCase "treeCursorStruct" treeCursorStructTest
    ]
