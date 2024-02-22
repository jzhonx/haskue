{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module ValueTest where

import qualified AST
import Control.Monad.Except (MonadError, runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (StateT (runStateT))
import Control.Monad.State.Strict (MonadState)
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
import Value

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

putValueInCtxTest :: IO ()
putValueInCtxTest = do
  let m = putValueInCtx (pathFromList [selX1, selY]) (String "world")
  let res = runStateT m (Context (outer, []) Map.empty)
  case res of
    Left err -> assertFailure err
    Right (_, Context (resVal, _) _) -> do
      assertEqual "check block" expectedVal resVal
  return ()
  where
    {-
     {
      x1: { y: "hello" }
      x2: 42
     }
    -}
    inner = StructValue ["y"] (Map.fromList [("y", String "hello")]) Set.empty Set.empty
    outer = StructValue ["x1", "x2"] (Map.fromList [("x1", Struct inner), ("x2", Int 42)]) Set.empty Set.empty
    expectedVal =
      StructValue
        ["x1", "x2"]
        ( Map.fromList
            [ ("x1", Struct $ StructValue ["y"] (Map.fromList [("y", String "world")]) Set.empty Set.empty),
              ("x2", Int 42)
            ]
        )
        Set.empty
        Set.empty

valueTests :: TestTree
valueTests =
  testGroup
    "valueTest"
    [ testCase "putValueInCtx" putValueInCtxTest,
      testCase "depsHasCycle" testDepsHasCycle
    ]
