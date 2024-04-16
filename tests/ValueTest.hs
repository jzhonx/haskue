{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module ValueTest where

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
treeCursorStructTest = runExceptT test >>= \case
  Left err -> assertFailure err
  Right _ -> return ()
  where
    mkSimple :: (String, Value) -> StructValue
    mkSimple pair = StructValue [fst pair] (Map.fromList [pair]) Set.empty Set.empty
    -- { a: { b: { c: 42 } } }
    holderC = mkSimple ("c", Int 42)
    holderB = mkSimple ("b", Struct holderC)
    holderA = mkSimple ("a", Struct holderB)
    selA = StringSelector "a"
    selB = StringSelector "b"
    selC = StringSelector "c"

    test :: (MonadError String m, MonadIO m) => m ()
    test = do
      let rootTC = tcFromSV emptyStruct
      tc <- 
        insertTCSV selA emptyStruct rootTC >>= 
        insertTCSV selB emptyStruct >>=
        insertTCLeafValue selC (Int 42)

      let (Struct sva) = fromJust $ getValueTCPath tc (pathFromList [])
      liftIO $ assertEqual "sva" holderA sva
      --
      let (Struct svb) = fromJust $ getValueTCPath tc (pathFromList [selA])
      liftIO $ assertEqual "svb" holderB svb
      --
      let (Struct svc) = fromJust $ getValueTCPath tc (pathFromList [selA, selB])
      liftIO $ assertEqual "svc" holderC svc

      let vl = fromJust $ getValueTCPath tc (pathFromList [selA, selB, selC])
      liftIO $ assertEqual "leaf value" (Int 42) vl
      return ()

treeCursorOpTest :: IO ()
treeCursorOpTest = runExceptT test >>= \case
  Left err -> assertFailure err
  Right _ -> return ()
  where
    mkSimple :: (String, Value) -> StructValue
    mkSimple pair = StructValue [fst pair] (Map.fromList [pair]) Set.empty Set.empty
    -- { 
    --  a: { 
    --    c: UnaryOp{arg: 42} 
    --  } 
    --  b: {
    --    c: BinaryOp{l: 1, r: 2}
    --  }
    -- }
    -- una = mkSimple ("c", TNUnaryOp $ TreeUnaryOp {truArg=undefined, truOp=undefined})
    -- holderB = mkSimple ("b", Struct holderC)
    -- holderA = mkSimple ("a", Struct holderB)
    selA = StringSelector "a"
    selB = StringSelector "b"
    selC = StringSelector "c"

    test :: (MonadError String m, MonadIO m) => m ()
    test = do
      let rootTC = tcFromSV emptyStruct
      tc <-
        insertTCSV selA emptyStruct rootTC >>=
        insertTCUnaryOp selC undefined >>=
        insertTCLeafValue UnaryOpSelector (Int 42) >>= 
        propRootTC >>=
        insertTCSV selB emptyStruct >>=
        insertTCBinaryOp selC undefined >>=
        insertTCLeafValue (BinOpSelector L) (Int 1) >>=
        (\tc -> return $ fromJust (goUpTC tc)) >>=
        insertTCLeafValue (BinOpSelector R) (Int 2) >>= 
        propRootTC

      let v = fromJust $ getValueTCPath tc (pathFromList [selA, selC, UnaryOpSelector])
      liftIO $ assertEqual "v1" (Int 42) v

      let v = fromJust $ getValueTCPath tc (pathFromList [selB, selC, BinOpSelector L])
      liftIO $ assertEqual "v1" (Int 1) v

      let v = fromJust $ getValueTCPath tc (pathFromList [selB, selC, BinOpSelector R])
      liftIO $ assertEqual "v1" (Int 2) v
      return ()

valueTests :: TestTree
valueTests =
  testGroup
    "valueTest"
    [ 
      -- testCase "putValueInCtx" putValueInCtxTest
      -- ,testCase "depsHasCycle" testDepsHasCycle
      testCase "treeCursorStruct" treeCursorStructTest,
      testCase "treeCursorOp" treeCursorOpTest
    ]
