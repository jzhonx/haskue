module ValueTest where

import           Control.Monad.State (StateT (runStateT))
import qualified Data.Map.Strict     as Map
import           Data.Maybe          (fromJust)
import qualified Data.Set            as Set
import           Test.Tasty          (TestTree, testGroup)
import           Test.Tasty.HUnit    (assertEqual, assertFailure, testCase)
import           Value

edgesGen :: [(String, String)] -> [(Path, Path)]
edgesGen = map (\(x, y) -> ([StringSelector x], [StringSelector y]))

strsToPath :: [String] -> [Path]
strsToPath = map (\x -> [StringSelector x])

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
pathY = [StringSelector "y"]

pathX1 = [StringSelector "x1"]

pathX2 = [StringSelector "x2"]

modifyValueInCtxTest :: IO ()
modifyValueInCtxTest = do
  let m = modifyValueInCtx [head pathX1, head pathY] (String "world")
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
  return ()
  where
    {-
     { x1: y; x2: x1 }
    -}
    blockVal =
      StructValue
        ["x1", "x2"]
        ( Map.fromList
            [ ("x1", Pending [(pathY, pathX1)] (\xs -> return $ fromJust $ lookup pathY xs)),
              ("x2", Pending [(pathX1, pathX2)] (\xs -> return $ fromJust $ lookup pathX1 xs))
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

valueTests :: TestTree
valueTests =
  testGroup
    "value test"
    [ testCase "checkEvalPen" checkEvalPenTest,
      testCase "modifyValueInCtx" modifyValueInCtxTest
    ]
