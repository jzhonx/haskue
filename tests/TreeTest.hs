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
strSel = StructSelector . StringSelector

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

treeTests :: TestTree
treeTests =
  testGroup
    "treeTest"
    []

-- [ testCase "treeCursorStruct" treeCursorStructTest
