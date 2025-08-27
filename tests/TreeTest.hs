module TreeTest where

import AST (exprToOneLinerStr)
import Control.Monad.Except (runExcept)
import Data.Aeson (ToJSON, Value, encode, toJSON)
import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import Path
import System.Directory (listDirectory)
import System.IO (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf (printf)
import Value
import Value.Util.TreeRep (TreeRepBuildOption (..), buildRepTree, defaultTreeRepBuildOption, repToString)

treeTests :: IO TestTree
treeTests =
  return $
    testGroup
      "treetests"
      [ testSnapshotTree
      ]

testSnapshotTree :: TestTree
testSnapshotTree =
  testCase "snapshot_tree" $ do
    let
      refAWithRC = setMutVal (Just (mkNewTree TNRefCycle)) (withEmptyMutFrame $ Ref $ emptyIdentRef $ T.pack "x")

      a1 = mkAtomTree (Int 1)
      a2 = mkAtomTree (Int 2)
      a3 = mkAtomTree (Int 3)
      a4 = mkAtomTree (Int 4)
      unify1 = mkUnifyOp [mkNewTree (TNMutable refAWithRC), a2]
      disj1 = mkDisjoinOpFromList [DisjTerm False a1, DisjTerm False (mkNewTree (TNMutable unify1))]
      refB = withEmptyMutFrame $ Ref $ emptyIdentRef $ T.pack "b"
      refBV = setMutVal (Just (mkMutableTree disj1)) refB
      disj2 = mkDisjoinOpFromList [DisjTerm False (mkMutableTree refBV), DisjTerm False a4]
      t = mkNewTree (TNMutable disj2)

    t <- case runExcept (snapshotTree t) of
      Left err -> assertFailure err
      Right t -> return t

    let rep = buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = True})
    putStrLn (repToString 0 rep)

    putStrLn "-----"
    BL.putStr (encode rep)

    putStrLn "-----"
    let astE = buildASTExprDebug t
    case runExcept astE of
      Left err -> assertFailure err
      Right expr -> putStrLn $ exprToOneLinerStr expr
