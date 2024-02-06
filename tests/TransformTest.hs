module TransformTest where

import           AST
import           Parser           (parseCUE)
import           System.IO        (readFile)
import           Test.Tasty       (TestTree, testGroup)
import           Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import           Transform        (transform)

testTransform :: IO ()
testTransform = do
  s <- readFile "tests/transform/transform.cue"
  let res = parseCUE s
  case res of
    Left err  -> assertFailure err
    Right val -> assertEqual "transformed" exp (transform val)
  where
    aField =
      ExprBinaryOp
        Unify
        (litCons $ BoolLit True)
        (ExprBinaryOp Unify (litCons $ (StringLit . SimpleStringLit) "hello") (litCons $ IntLit 1))
    exp =
      ExprUnaryExpr $
        UnaryExprPrimaryExpr $
          PrimExprOperand $
            OpLiteral $
              StructLit
                [ ((Label . LabelName . LabelID) "a", aField),
                  ((Label . LabelName . LabelID) "b", litCons $ IntLit 4),
                  ((Label . LabelName . LabelID) "c", litCons $ IntLit 3)
                ]

transformTests :: TestTree
transformTests = testGroup "Transform Tests" [testCase "transform" testTransform]
