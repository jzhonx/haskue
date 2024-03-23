{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module EvalTest where

import qualified AST
import Control.Monad.Except
  ( Except,
    MonadError,
    runExcept,
    runExceptT,
    throwError,
  )
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Logger
  ( LoggingT,
    MonadLogger,
    runStderrLoggingT,
  )
import Control.Monad.State
  ( State,
    StateT (runStateT),
    evalState,
    evalStateT,
    runState,
  )
import Control.Monad.State.Strict (MonadState, get, put)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Eval
import Path
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
  ( assertBool,
    assertEqual,
    assertFailure,
    testCase,
  )
import Value

selY = StringSelector "y"

pathY = Path [selY]

selZ = StringSelector "z"

pathZ = Path [selZ]

selX1 = StringSelector "x1"

pathX1 = Path [selX1]

selX2 = StringSelector "x2"

pathX2 = Path [selX2]

bottomExpr = AST.litCons AST.BottomLit

simpleExpr = AST.idCons "simple"

runEmptyCtx :: (MonadError String m, MonadIO m) => LoggingT (StateT Context m) a -> m a
runEmptyCtx = runCtx (Context (emptyStruct, []) Map.empty)

runCtx :: (MonadError String m, MonadIO m) => Context -> LoggingT (StateT Context m) a -> m a
runCtx ctx m = evalStateT (runStderrLoggingT m) ctx

runKeep :: (MonadError String m, MonadIO m) => Context -> LoggingT (StateT Context m) a -> m (a, Context)
runKeep ctx m = runStateT (runStderrLoggingT m) ctx

mkPending :: AST.Expression -> Path -> Path -> Value
mkPending expr src dst = mkReference expr src dst (Unevaluated src)

propagateTest :: IO ()
propagateTest =
  runExceptT compareContext >>= \case
    Left err -> assertFailure err
    Right _ -> return ()
  where
    ctx = Context (blockVal, []) revDeps
    {-
     { x1: y; x2: x1 }
    -}
    blockVal =
      StructValue
        ["x1", "x2"]
        ( Map.fromList
            [ ("x1", mkPending bottomExpr pathX1 pathY),
              ("x2", mkPending bottomExpr pathX2 pathX1)
            ]
        )
        Set.empty
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
        Set.empty

    compareContext :: (MonadError String m, MonadIO m) => m ()
    compareContext = do
      (_, Context (resBlock, _) resRev) <- runKeep ctx $ propagate (pathY, newVal)
      liftIO $ assertEqual "check block" expectedBlockVal resBlock
      -- resRev should be empty because all values are evaluated to atoms.
      liftIO $ assertBool "check rev" $ resRev == Map.empty

-- -- | binFuncTest1 tests the case that two pending values depend on the same value.
-- binFuncTest1 :: IO ()
-- binFuncTest1 =
--   runExceptT binFuncTestHelper
--     >>= \case
--       Left err -> assertFailure err
--       Right _ -> return ()
--   where
--     addF :: Value -> Value -> EvalMonad Value
--     addF (Int a) (Int b) = return $ Int (a + b)
--     addF _ _ = throwError "addF: invalid arguments"
--
--     pend1 = mkPending bottomExpr pathX1 pathY
--     pend2 = mkPending bottomExpr pathX1 pathY
--
--     binFuncTestHelper :: (MonadError String m, MonadIO m) => m ()
--     binFuncTestHelper = do
--       vx <- runEmptyCtx (bindBinary simpleExpr addF pend1 pend2)
--       vy <- runEmptyCtx $ resolve (emptyPath, vx) (pathY, Int 2)
--       liftIO $ assertEqual "check value" (Int 4) vy
--
-- -- | binFuncTest2 tests the case that two pending values order.
-- binFuncTest2 :: IO ()
-- binFuncTest2 =
--   runExceptT binFuncTestHelper
--     >>= \case
--       Left err -> assertFailure err
--       Right _ -> return ()
--   where
--     divF :: Value -> Value -> EvalMonad Value
--     divF (Int a) (Int b) = return $ Int (a `div` b)
--     divF _ _ = throwError "addF: invalid arguments"
--
--     pend1 = mkPending bottomExpr pathX1 pathY
--     pend2 = mkPending bottomExpr pathX1 pathZ
--
--     binFuncTestHelper :: (MonadError String m, MonadIO m) => m ()
--     binFuncTestHelper = do
--       vx <- runEmptyCtx (bindBinary simpleExpr divF pend1 pend2)
--       vy <- runEmptyCtx $ applyPen (emptyPath, vx) (pathY, Int 12)
--       res <- runEmptyCtx $ applyPen (emptyPath, vy) (pathZ, Int 4)
--       liftIO $ assertEqual "check value" (Int 3) res

evalTests :: TestTree
evalTests =
  testGroup
    "evalTest"
    [ testCase "propagate" propagateTest
    -- testCase "binFunc1" binFuncTest1,
    -- testCase "binFunc2" binFuncTest2
    -- testCase "putValueInCtx" putValueInCtxTest,
    -- testCase "depsHasCycle" testDepsHasCycle
    ]
