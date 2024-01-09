module ValueTest where

import           Control.Monad.State (StateT (runStateT))
import qualified Data.Map.Strict     as Map
import           Data.Maybe          (fromJust)
import qualified Data.Set            as Set
import           Test.Tasty          (TestTree, testGroup)
import           Test.Tasty.HUnit    (assertEqual, assertFailure, testCase)
import           Value

newStruct :: [String] -> Map.Map String Value -> Set.Set String -> Value
newStruct lbls fds ids = Struct (StructValue lbls fds ids)

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

checkEvalPenCase :: IO ()
checkEvalPenCase = do
  let m = checkEvalPen (pathY, newVal)
  let res = runStateT m (Context [] (blockVal, []) revDeps)
  case res of
    Left err -> assertFailure err
    Right (_, Context resPath (resVal, _) resRev) -> do
      assertEqual "check path" [] resPath
      assertEqual "check block" expectedBlockVal resVal
      assertEqual "check rev" Map.empty resRev
  return ()
  where
    pathY = [StringSelector "y"]
    pathX1 = [StringSelector "x1"]
    pathX2 = [StringSelector "x2"]
    {-
     { x1: y; x2: x1 }
    -}
    blockVal =
      newStruct
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
      newStruct
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
    [ testCase "checkEvalPen" checkEvalPenCase
    ]
