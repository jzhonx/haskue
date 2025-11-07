{-# LANGUAGE FlexibleContexts #-}

module TreeTest where

import AST (exprToOneLinerStr)
import Common (CommonState, Config, emptyCommonState, emptyConfig)
import Control.Monad.Except (ExceptT, MonadError (throwError), modifyError, runExcept, runExceptT)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (StateT, evalStateT, execStateT, runStateT)
import Cursor (TrCur (..), goDownTCSegMust)
import Data.Aeson (ToJSON, Value, encode, toJSON)
import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import EvalExpr (evalExpr)
import Parser (parseExpr)
import Feature
import Reduce (reduce)
import Reduce.RMonad (
  Context,
  Error (..),
  RTCState (..),
  ReduceConfig,
  ResolveMonad,
  emptyContext,
  emptyReduceConfig,
  getTMTree,
 )
import System.Directory (listDirectory)
import System.IO (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf (printf)
import Value
import Value.Util.TreeRep (
  TreeRepBuildOption (..),
  buildRepTree,
  defaultTreeRepBuildOption,
  repToString,
  treeToFullRepString,
  treeToRepString,
 )

treeTests :: IO TestTree
treeTests =
  return $
    testGroup
      "treetests"
      []

-- [testRep]

-- testRep :: TestTree
-- testRep = testCase "rep" $ do
--   let work = do
--         e <- parseExpr "{a: x: a}"
--         t <- runEvalEnv (evalExpr e)
--         evalReduceMonad
--           (TrCur t [(RootTASeg, mkNewTree TNTop)])
--           (reduce >> getTMTree)
--   rE <- runExceptT work
--   case rE of
--     Left err -> assertFailure err
--     Right r -> do
--       putStrLn $ treeToRepString r
--       putStrLn $ treeToFullRepString r
--       putStrLn $ oneLinerStringOfTree r

--   return ()

-- evalResolveMonad :: (MonadIO m, MonadError String m) => StateT Context (ReaderT Config m) a -> m a
-- evalResolveMonad action = runReaderT (evalStateT action emptyContext) emptyConfig

-- evalReduceMonad ::
--   (MonadIO m, MonadError String m) => TrCur -> StateT RTCState (ReaderT ReduceConfig (ExceptT Error m)) a -> m a
-- evalReduceMonad tc action = do
--   r <- runExceptT $ runReaderT (evalStateT action (RTCState tc emptyContext)) emptyReduceConfig
--   case r of
--     Left err -> throwError (show err)
--     Right v -> return v

-- runEvalEnv :: (MonadIO m, MonadError String m) => StateT CommonState (ReaderT Config m) a -> m a
-- runEvalEnv action = runReaderT (evalStateT action emptyCommonState) emptyConfig

-- --   rE <- runExceptT work
-- --   case rE of
-- --     Left err -> assertFailure err
-- --     Right r -> do
-- --       putStrLn $ treeToFullRepString r
-- --       putStrLn $ oneLinerStringOfTree r

-- --  testSnapshotTree
-- -- , testSnapshotTree2
-- -- testeliminateRCAndOtherRefs

-- -- testSnapshotTree :: TestTree
-- -- testSnapshotTree =
-- --   testCase "snapshot_tree" $ do
-- --     let
-- --       refAWithRC = mkNewTreeWithTGen TNRefCycle (TGenOp $ withEmptyMutFrame $ Ref $ emptyIdentRef $ T.pack "x")

-- --       -- a1 = mkAtomTree (Int 1)
-- --       -- a2 = mkAtomTree (Int 2)
-- --       -- a3 = mkAtomTree (Int 3)
-- --       -- a4 = mkAtomTree (Int 4)
-- --       -- unify1 = mkUnifyOp [refAWithRC, a2]
-- --       -- disj1 = mkDisjoinOpFromList [DisjTerm False a1, DisjTerm False (mkMutableTree unify1)]
-- --       -- refB = withEmptyMutFrame $ Ref $ emptyIdentRef $ T.pack "b"
-- --       -- refBV = setMutVal (Just (mkMutableTree disj1)) refB
-- --       -- disj2 = mkDisjoinOpFromList [DisjTerm False (mkMutableTree refBV), DisjTerm False a4]
-- --       -- t = mkNewTree (TNMutable disj2)
-- --       t = refAWithRC

-- --     t <- case runExcept (snapshotTree t) of
-- --       Left err -> assertFailure err
-- --       Right t -> return t

-- --     putStrLn "-----"
-- --     let rep = buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = True})
-- --     putStrLn (repToString 0 rep)

-- --     putStrLn "-----"
-- --     let rep = buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = False})
-- --     putStrLn (repToString 0 rep)

-- --     putStrLn "-----"
-- --     BL.putStr (encode rep)

-- --     putStrLn "-----"
-- --     let astE = buildASTExprDebug t
-- --     case runExcept astE of
-- --       Left err -> assertFailure err
-- --       Right expr -> putStrLn $ exprToOneLinerStr expr

-- -- testSnapshotTree2 :: TestTree
-- -- testSnapshotTree2 =
-- --   testCase "snapshot_tree2" $ do
-- --     let
-- --       refAWithRC = setMutVal (Just (mkNewTree TNRefCycle)) (withEmptyMutFrame $ Ref $ emptyIdentRef $ T.pack "a")

-- --       b1 = mkBlockTree $ mkBlockFromAdder 1 (StaticSAdder (T.pack "x") (mkdefaultField (mkAtomTree (Int 2))))
-- --       b2 = mkBlockTree $ mkBlockFromAdder 1 (StaticSAdder (T.pack "y") (mkdefaultField (mkAtomTree (Int 2))))
-- --       unify1 = mkUnifyOp [mkNewTree (TNMutable refAWithRC), b2]
-- --       disj1 = mkDisjoinOpFromList [DisjTerm False b1, DisjTerm False (mkNewTree (TNMutable unify1))]
-- --       tester = mkNewTree (TNMutable disj1)

-- --     putStrLn "-----"
-- --     putStrLn (oneLinerStringOfTree tester)

-- --     putStrLn "-----"
-- --     let rep = buildRepTree tester (defaultTreeRepBuildOption{trboRepSubFields = True})
-- --     putStrLn (repToString 0 rep)

-- --     x <- case runExcept (snapshotTree tester) of
-- --       Left err -> assertFailure err
-- --       Right x -> return x

-- --     putStrLn "-----"
-- --     let rep = buildRepTree x (defaultTreeRepBuildOption{trboRepSubFields = False})
-- --     putStrLn (repToString 0 rep)

-- --     putStrLn "-----"
-- --     BL.putStr (encode rep)

-- --     putStrLn "-----"
-- --     let astE = buildASTExprDebug x
-- --     case runExcept astE of
-- --       Left err -> assertFailure err
-- --       Right expr -> putStrLn $ exprToOneLinerStr expr

-- buildAbsTA :: String -> TreeAddr
-- buildAbsTA path = appendTreeAddr rootTreeAddr (addrFromString path)

-- absA, absAX, absB, absC :: TreeAddr
-- absA = buildAbsTA "a"
-- absAX = buildAbsTA "a.x"
-- absB = buildAbsTA "b"
-- absC = buildAbsTA "c"

-- -- testeliminateRCAndOtherRefs :: TestTree
-- -- testeliminateRCAndOtherRefs = testCase "eliminateRCAndOtherRefs" $ do
-- --   let work = do
-- --         e <- parseExpr "{a: 2 & (b + 1), b: a - 1}"
-- --         t <- runEvalEnv (evalExpr e)
-- --         r <-
-- --           evalResolveMonad
-- --             ( do
-- --                 let rootTC = TrCur t [(RootTASeg, mkNewTree TNTop)]
-- --                 aTC <- goDownTCSegMust (strToStringFeature "a") rootTC
-- --                 eliminateRCAndOtherRefs [absA, absB] [absA] aTC
-- --             )
-- --         return $ tcFocus r
-- --   rE <- runExceptT work
-- --   case rE of
-- --     Left err -> assertFailure err
-- --     Right r -> do
-- --       putStrLn $ treeToFullRepString r
-- --       putStrLn $ oneLinerStringOfTree r
-- --  where
-- --   b1 = mkBlockTree $ mkBlockFromAdder 1 (StaticSAdder (T.pack "x") (mkdefaultField (mkAtomTree (Int 2))))
