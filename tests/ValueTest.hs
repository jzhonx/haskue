{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module ValueTest where

import Control.Monad.Except (MonadError, runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (StateT (runStateT))
import Control.Monad.State.Strict (MonadState)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
  ( assertEqual,
    assertFailure,
    testCase,
  )
import Value

edgesGen :: [(String, String)] -> [(Path, Path)]
edgesGen = map (\(x, y) -> (Path [StringSelector x], Path [StringSelector y]))

strsToPath :: [String] -> [Path]
strsToPath = map (\x -> Path [StringSelector x])

-- [ testCase "depsOrder-cycle" $
--     let deps = edgesGen [("a", "b"), ("b", "c"), ("c", "a")]
--         result = depsOrder deps
--      in do
--           assertEqual "depsOrder-cycle" Nothing result,
--   testCase "depsOrder-happy-path" $
--     let deps = edgesGen [("a", "b"), ("b", "c"), ("c", "d")]
--         result = depsOrder deps
--      in do
--           assertEqual "" (Just $ strsToPath ["c", "b", "a"]) result
-- ]
--
--
selY = StringSelector "y"

pathY = Path [selY]

selZ = StringSelector "z"

pathZ = Path [selZ]

selX1 = StringSelector "x1"

pathX1 = Path [selX1]

selX2 = StringSelector "x2"

pathX2 = Path [selX2]

modifyValueInCtxTest :: IO ()
modifyValueInCtxTest = do
  let m = modifyValueInCtx (pathFromList [selX1, selY]) (String "world")
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
    inner = StructValue ["y"] (Map.fromList [("y", String "hello")]) Set.empty
    outer = StructValue ["x1", "x2"] (Map.fromList [("x1", Struct inner), ("x2", Int 42)]) Set.empty
    expectedVal =
      StructValue
        ["x1", "x2"]
        ( Map.fromList
            [ ("x1", Struct $ StructValue ["y"] (Map.fromList [("y", String "world")]) Set.empty),
              ("x2", Int 42)
            ]
        )
        Set.empty

checkEvalPenTest :: IO ()
checkEvalPenTest = do
  let m = checkEvalPen (pathY, newVal)
  let res = runStateT m (Context (blockVal, []) revDeps)
  case res of
    Left err -> assertFailure err
    Right (_, Context (resBlock, _) resRev) -> do
      assertEqual "check block" expectedBlockVal resBlock
      assertEqual "check rev" Map.empty resRev
  where
    {-
     { x1: y; x2: x1 }
    -}
    blockVal =
      StructValue
        ["x1", "x2"]
        ( Map.fromList
            [ ("x1", newPending pathX1 pathY),
              ("x2", newPending pathX2 pathX1)
            ]
        )
        Set.empty
    newVal = Int 1
    revDeps = Map.fromList [(pathY, pathX1), (pathX1, pathX2)]
    expectedBlockVal =
      StructValue
        ["x1", "x2"]
        ( Map.fromList
            [ ("x1", Int 1),
              ("x2", Int 1)
            ]
        )
        Set.empty

runEmptyCtx :: (MonadError String m) => StateT Context m Value -> m Value
runEmptyCtx m = do
  res <- runStateT m (Context (emptyStruct, []) Map.empty)
  return $ fst res

-- | binFuncTest1 tests the case that two pending values depend on the same value.
binFuncTest1 :: IO ()
binFuncTest1 =
  runExceptT binFuncTestHelper
    >>= \case
      Left err -> assertFailure err
      Right _ -> return ()
  where
    addF :: Value -> Value -> EvalMonad Value
    addF (Int a) (Int b) = return $ Int (a + b)
    addF _ _ = throwError "addF: invalid arguments"

    pend1 = newPending pathX1 pathY
    pend2 = newPending pathX1 pathY

    binFuncTestHelper :: (MonadError String m, MonadIO m) => m ()
    binFuncTestHelper = do
      vx <- runEmptyCtx (binFunc addF pend1 pend2)
      vy <- runEmptyCtx $ applyPen (emptyPath, vx) (pathY, Int 2)
      liftIO $ assertEqual "check value" (Int 4) vy

-- | binFuncTest2 tests the case that two pending values order.
binFuncTest2 :: IO ()
binFuncTest2 =
  runExceptT binFuncTestHelper
    >>= \case
      Left err -> assertFailure err
      Right _ -> return ()
  where
    divF :: Value -> Value -> EvalMonad Value
    divF (Int a) (Int b) = return $ Int (a `div` b)
    divF _ _ = throwError "addF: invalid arguments"

    pend1 = newPending pathX1 pathY
    pend2 = newPending pathX1 pathZ

    binFuncTestHelper :: (MonadError String m, MonadIO m) => m ()
    binFuncTestHelper = do
      vx <- runEmptyCtx (binFunc divF pend1 pend2)
      vy <- runEmptyCtx $ applyPen (emptyPath, vx) (pathY, Int 12)
      res <- runEmptyCtx $ applyPen (emptyPath, vy) (pathZ, Int 4)
      liftIO $ assertEqual "check value" (Int 3) res

valueTests :: TestTree
valueTests =
  testGroup
    "valueTest"
    [ testCase "checkEvalPen" checkEvalPenTest,
      testCase "modifyValueInCtx" modifyValueInCtxTest,
      testCase "binFunc1" binFuncTest1,
      testCase "binFunc2" binFuncTest2
    ]
