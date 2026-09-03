module ExplainTest (tests) where

import Control.Monad.Except (runExceptT)
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Char8 as BC
import Data.List (isInfixOf)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Eval (Config (..), emptyConfig, evalSelectedStr, evalStr, explainExpr)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "explain"
    [ testCase "explains unified struct constraints" testUnifiedStruct
    , testCase "evaluates a selected reference" testSelectedReference
    , testCase "explains conflicting constraints" testConflict
    , testCase "rejects a non-reference query" testInvalidQuery
    , testCase "reports a missing query root" testMissingQueryRoot
    , testCase "reports query token errors" testQueryTokenError
    , testCase "reports query semantic errors" testQuerySemanticError
    , testCase "reports query selector bottoms" testQuerySelectorBottom
    , testCase "reports source parse errors as user errors" testSourceParseError
    , testCase "reports incomplete JSON without a call stack" testIncompleteJSON
    ]

testSelectedReference :: Assertion
testSelectedReference = do
  result <- runExceptT $ evalSelectedStr "x: 1 + 2" "x" emptyConfig
  case result of
    Left err -> assertFailure err
    Right builder ->
      TE.decodeUtf8 (BC.toStrict $ toLazyByteString builder) @?= "3"

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
    Left err -> err @?= "query must be a reference that starts with a file-level identifier"
    Right _ -> assertFailure "expected the query to be rejected"

testMissingQueryRoot :: Assertion
testMissingQueryRoot = do
  result <- runExceptT $ explainExpr "{a: 1}" "b" emptyConfig
  case result of
    Left err -> err @?= "query path not found"
    Right _ -> assertFailure "expected the query to be rejected"

testQueryTokenError :: Assertion
testQueryTokenError = do
  result <- runExceptT $ explainExpr "{a: 1}" "@" emptyConfig
  case result of
    Left err -> err @?= "-:1:1: illegal character: @"
    Right _ -> assertFailure "expected the query to be rejected"

testQuerySemanticError :: Assertion
testQuerySemanticError = do
  result <- runExceptT $ explainExpr "{a: {x: 1}}" "a[b]" emptyConfig
  case result of
    Left err -> assertBool err $ "reference \"b\" not found" `isInfixOf` err
    Right _ -> assertFailure "expected the query to be rejected"

testQuerySelectorBottom :: Assertion
testQuerySelectorBottom = do
  result <- runExceptT $ explainExpr "{a: [1]}" "a[1 & 2]" emptyConfig
  case result of
    Left err -> err @?= "conflicting values: 1 and 2"
    Right _ -> assertFailure "expected the query to be rejected"

testSourceParseError :: Assertion
testSourceParseError = do
  result <- runExceptT $ evalStr "{a:" emptyConfig
  case result of
    Left err -> assertFailure $ "parse error was reported as internal: " ++ err
    Right builder -> do
      let output = BC.unpack $ BC.toStrict $ toLazyByteString builder
      assertBool output $ "error:" `isInfixOf` output
      assertBool output $ not $ "CallStack" `isInfixOf` output

testIncompleteJSON :: Assertion
testIncompleteJSON = do
  result <- runExceptT $ evalStr "a: int" emptyConfig{outputFormat = "json"}
  case result of
    Left err -> assertFailure $ "export error was reported as internal: " ++ err
    Right builder -> do
      let output = BC.unpack $ BC.toStrict $ toLazyByteString builder
      assertBool output $ "cannot export incomplete value to JSON: int" `isInfixOf` output
      assertBool output $ not $ "CallStack" `isInfixOf` output

runExplain :: BC.ByteString -> BC.ByteString -> IO T.Text
runExplain source query = do
  result <- runExceptT $ explainExpr source query emptyConfig
  case result of
    Left err -> assertFailure err
    Right builder -> return $ TE.decodeUtf8 $ BC.toStrict $ toLazyByteString builder
