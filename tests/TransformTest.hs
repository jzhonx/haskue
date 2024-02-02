module TransformTest where

import AST
import Parser (parseCUE)
import System.IO (readFile)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Transform (transform)

testTransform :: IO ()
testTransform = do
  s <- readFile "tests/e2efiles/binop2.cue"
  let res = parseCUE s
  case res of
    Left err -> assertFailure err
    Right val -> assertEqual "transform" val (transform val)
  where
    aField =
      ExprBinaryOp Unify (litCons $ IntLit 1) (litCons $ StringLit $ SimpleStringLit "hello")
    exp =
      ExprUnaryExpr $
        UnaryExprPrimaryExpr $
          PrimExprOperand $
            OpLiteral $
              StructLit [((Label . LabelName . LabelString) "a", aField)]

transformTests :: TestTree
transformTests = testGroup "Transform Tests" [testCase "simplify-struct" testTransform]
