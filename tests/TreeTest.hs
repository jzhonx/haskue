{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module TreeTest where

import qualified AST
import Control.Monad.Except
  ( MonadError,
    runExcept,
    runExceptT,
    throwError,
  )
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Logger (runNoLoggingT)
import Control.Monad.State (StateT (runStateT))
import Control.Monad.Logger (MonadLogger, runStderrLoggingT)
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

-- putValueInCtxTest :: IO ()
-- putValueInCtxTest = do
--   let m = putValueInCtx (pathFromList [selX1, selY]) (String "world")
--   let res = runStateT (runNoLoggingT m) (Context (outer, []) Map.empty)
--   case res of
--     Left err -> assertFailure err
--     Right (_, Context (resVal, _) _) -> do
--       assertEqual "check block" expectedVal resVal
--   return ()
--   where
--     {-
--      {
--       x1: { y: "hello" }
--       x2: 42
--      }
--     -}
--     inner = StructValue ["y"] (Map.fromList [("y", String "hello")]) Set.empty Set.empty
--     outer = StructValue ["x1", "x2"] (Map.fromList [("x1", Struct inner), ("x2", Int 42)]) Set.empty Set.empty
--     expectedVal =
--       StructValue
--         ["x1", "x2"]
--         ( Map.fromList
--             [ ("x1", Struct $ StructValue ["y"] (Map.fromList [("y", String "world")]) Set.empty Set.empty),
--               ("x2", Int 42)
--             ]
--         )
--         Set.empty
--         Set.empty

treeCursorStructTest :: IO ()
treeCursorStructTest = (runStderrLoggingT $ runExceptT test) >>= \case
  Left err -> assertFailure err
  Right _ -> return ()
  where
    mkSimple :: (String, TreeNode) -> TreeNode
    mkSimple pair = TNScope $ emptyTNScope { 
      trsOrdLabels = [fst pair],
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
      let 
        rootTC = (TNRoot $ TNScope emptyTNScope, [])
        topTC = fromJust $ goDownTCSel StartSelector rootTC 
      in do
      tc <- 
        insertTCScope selA [] Set.empty topTC >>=
        insertTCScope selB [] Set.empty >>=
        insertTCLeafValue selC (Int 42) >>=
        propTopTC

      let sva = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector]) tc 
      liftIO $ assertEqual "struct a" holderA sva
      --
      let svb = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector,selA]) tc 
      liftIO $ assertEqual "struct b" holderB svb
      --
      let trc = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector,selA, selB]) tc 
      liftIO $ assertEqual "struct c" holderC trc

      let vl = fst $ fromJust $ goDownTCPath (pathFromList [StartSelector, selA, selB, selC]) tc 
      liftIO $ assertEqual "leaf value" (mkTreeLeaf $ Int 42) vl
      return ()

-- treeCursorOpTest :: IO ()
-- treeCursorOpTest = (runStderrLoggingT $ runExceptT test) >>= \case
--   Left err -> assertFailure err
--   Right _ -> return ()
--   where
--     mkSimple :: (String, TreeNode) -> TreeNode
--     mkSimple pair = TNScope $ emptyTNScope { 
--       trsOrdLabels = [fst pair],
--       trsSubs = Map.fromList [pair]
--     }
--     -- { 
--     --  a: { 
--     --    c: UnaryOp{arg: 42} 
--     --  } 
--     --  b: {
--     --    c: BinaryOp{l: 1, r: 2}
--     --  }
--     -- }
--     selA = StringSelector "a"
--     selB = StringSelector "b"
--     selC = StringSelector "c"
--
--     test :: (MonadError String m, MonadIO m, MonadLogger m) => m ()
--     test = 
--       let 
--         rootTC = (TNRoot $ TNScope emptyTNScope, [])
--         topTC = fromJust $ goDownTCSel StartSelector rootTC 
--       in do
--       tc <-
--         insertTCScope selA [] Set.empty topTC >>=
--         insertTCUnaryOp selC "nop" undefined (\x -> return x) >>=
--         insertTCLeafValue UnaryOpSelector (Int 42) >>= 
--         propTopTC >>=
--         insertTCScope selB [] Set.empty >>=
--         insertTCBinaryOp selC "nop" undefined (\x y -> return $ x + y) >>=
--         insertTCLeafValue (BinOpSelector L) (Int 1) >>=
--         (\tc -> return $ fromJust (goUpTC tc)) >>=
--         insertTCLeafValue (BinOpSelector R) (Int 2) >>= 
--         propTopTC
--
--       let v = fst $ fromJust $ goDownTCPath tc (pathFromList [selA, selC, UnaryOpSelector])
--       liftIO $ assertEqual "v1" (mkTreeLeaf $ Int 42) v
--
--       let v = fst $ fromJust $ goDownTCPath tc (pathFromList [selB, selC, BinOpSelector L])
--       liftIO $ assertEqual "v1" (mkTreeLeaf $ Int 1) v
--
--       let v = fst $ fromJust $ goDownTCPath tc (pathFromList [selB, selC, BinOpSelector R])
--       liftIO $ assertEqual "v1" (mkTreeLeaf $ Int 2) v
--       return ()

treeTests :: TestTree
treeTests =
  testGroup
    "treeTest"
    [ 
      -- testCase "putValueInCtx" putValueInCtxTest
      -- ,testCase "depsHasCycle" testDepsHasCycle
      testCase "treeCursorStruct" treeCursorStructTest
      -- testCase "treeCursorOp" treeCursorOpTest
    ]
