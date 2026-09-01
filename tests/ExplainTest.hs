module ExplainTest (tests) where

import Control.Monad.Except (runExceptT)
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Char8 as BC
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Eval (emptyConfig, explainExpr)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "explain"
    [ testCase "explains unified struct constraints" testUnifiedStruct
    , testCase "explains conflicting constraints" testConflict
    , testCase "rejects a non-reference query" testInvalidQuery
    ]

testUnifiedStruct :: Assertion
testUnifiedStruct = do
  actual <- runExplain "{x: {a: {p: 1}} & {a: {q: 2}}}" "x.a"
  actual
    @?= T.unlines
      [ "x.a = {p: 1,q: 2}"
      , ""
      , "Conjuncts:"
      , "├─ {p: 1}    -:1:9"
      , "└─ {q: 2}    -:1:23"
      ]

testConflict :: Assertion
testConflict = do
  actual <- runExplain "{x: {a: int} & {a: \"one\"}}" "x.a"
  actual
    @?= T.unlines
      [ "x.a = _|_"
      , ""
      , "Conjuncts:"
      , "├─ int      -:1:9"
      , "└─ \"one\"    -:1:20"
      ]

testInvalidQuery :: Assertion
testInvalidQuery = do
  result <- runExceptT $ explainExpr "{x: 1}" "1 + 2" emptyConfig
  case result of
    Left err -> err @?= "query must be a reference rooted at a file-level identifier"
    Right _ -> assertFailure "expected the query to be rejected"

runExplain :: BC.ByteString -> BC.ByteString -> IO T.Text
runExplain source query = do
  result <- runExceptT $ explainExpr source query emptyConfig
  case result of
    Left err -> assertFailure err
    Right builder -> return $ TE.decodeUtf8 $ BC.toStrict $ toLazyByteString builder
