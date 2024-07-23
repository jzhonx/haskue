{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module TreeTest where

import qualified AST
import Control.Monad.Except (
  MonadError,
  runExcept,
  runExceptT,
  throwError,
 )
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Logger (MonadLogger, runNoLoggingT, runStderrLoggingT)
import Control.Monad.Reader (MonadReader, ReaderT (runReaderT))
import Control.Monad.State (StateT (runStateT))
import Control.Monad.State.Strict (MonadState)
import Data.Either (fromRight)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Path
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (
  assertBool,
  assertEqual,
  assertFailure,
  testCase,
 )
import Tree
import Unify (unify)

strSel :: String -> Selector
strSel = ScopeSelector . StringSelector

edgesGen :: [(String, String)] -> [(Path, Path)]
edgesGen = map (\(x, y) -> (Path [strSel x], Path [strSel y]))

strsToPath :: [String] -> [Path]
strsToPath = map (\x -> Path [strSel x])

testDepsHasCycle :: IO ()
testDepsHasCycle =
  let deps1 = edgesGen [("a", "b"), ("b", "c"), ("c", "a")]
      result1 = depsHasCycle deps1
      deps2 = edgesGen [("a", "b"), ("b", "c"), ("c", "d")]
      result2 = depsHasCycle deps2
   in do
        assertEqual "depsHasCycle" True result1
        assertEqual "depsHasCycle" False result2

selY = strSel "y"

pathY = Path [selY]

selZ = strSel "z"

pathZ = Path [selZ]

selX1 = strSel "x1"

pathX1 = Path [selX1]

selX2 = strSel "x2"

pathX2 = Path [selX2]

bottomExpr = AST.litCons AST.BottomLit

-- treeCursorStructTest :: IO ()
-- treeCursorStructTest =
--   (runReaderT (runStderrLoggingT $ runExceptT test) Config{cfUnify = unify}) >>= \case
--     Left err -> assertFailure err
--     Right _ -> return ()
--  where
--   mkSimple :: (String, Tree) -> Tree
--   mkSimple pair =
--     TNScope $
--       emptyTNScope
--         { trsOrdLabels = [fst pair]
--         , trsSubs = Map.fromList [pair]
--         }
--   -- { a: { b: { c: 42 } } }
--   holderC = mkSimple ("c", mkTreeLeaf $ Int 42)
--   holderB = mkSimple ("b", holderC)
--   holderA = mkSimple ("a", holderB)
--   selA = StringSelector "a"
--   selB = StringSelector "b"
--   selC = StringSelector "c"
--
--   test :: (MonadError String m, MonadIO m, MonadLogger m, MonadReader Config m) => m ()
--   test =
--     let rootTC = (TNRoot $ TNScope emptyTNScope, [])
--      in do
--           tc <-
--             insertTCScope StartSelector ["a"] Set.empty rootTC
--               >>= insertTCScope selA ["b"] Set.empty
--               >>= insertTCScope selB ["c"] Set.empty
--               >>= insertTCLeafValue selC (Int 42)
--               >>= propRootEvalTC
--
--           let sva = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector]) tc
--           liftIO $ assertEqual "struct a" holderA sva
--           --
--           let svb = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector, selA]) tc
--           liftIO $ assertEqual "struct b" holderB svb
--           --
--           let trc = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector, selA, selB]) tc
--           liftIO $ assertEqual "struct c" holderC trc
--
--           let vl = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector, selA, selB, selC]) tc
--           liftIO $ assertEqual "leaf value" (mkTreeLeaf $ Int 42) vl
--           return ()

treeTests :: TestTree
treeTests =
  testGroup
    "treeTest"
    []

-- [ testCase "treeCursorStruct" treeCursorStructTest
