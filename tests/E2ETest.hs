{-# LANGUAGE FlexibleContexts #-}

module E2ETest (e2eTests) where

import Control.Monad (foldM, when)
import Control.Monad.Except (MonadError, runExceptT)
import Control.Monad.IO.Class (liftIO)
import Data.ByteString.Builder (Builder, toLazyByteString)
import qualified Data.ByteString.Char8 as BC (ByteString, lines, pack, readFile, toStrict, unpack)
import Data.Char (isSpace)
import Data.List (dropWhileEnd, sort)
import qualified Data.Text as T
import Eval (ecMaxTreeDepth, emptyConfig, evalStr, explainStr)
import Exception (throwErrSt)
import System.Directory (listDirectory)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf (printf)

data TestCase = TestCase
  { name :: String
  , input :: BC.ByteString
  , output :: Builder
  , expectedOutput :: BC.ByteString
  }

emptyTestCase :: TestCase
emptyTestCase =
  TestCase
    { name = ""
    , input = ""
    , output = mempty
    , expectedOutput = ""
    }

data TxtarParseState
  = TPSInitial
  | TPSFoundCaseHeader
  | TPSReadingInput
  | TPSFoundExpHeader
  | TPSReadingExpectedOutput
  deriving (Eq)

parseTxtar :: (MonadError String m) => BC.ByteString -> m [TestCase]
parseTxtar file = do
  ((acc, cases), final) <-
    foldM
      ( \((cur, out), state) line ->
          let lineStr = BC.unpack line
           in if length lineStr >= 6 && take 3 lineStr == "-- " && drop (length lineStr - 3) lineStr == " --"
                then
                  let header = take (length lineStr - 6) (drop 3 lineStr)
                   in case state of
                        TPSInitial -> return ((cur{name = header}, out), TPSFoundCaseHeader)
                        TPSFoundCaseHeader -> throwErrSt $ "Unexpected case header: " ++ header
                        TPSReadingInput -> return ((cur, out), TPSFoundExpHeader)
                        TPSFoundExpHeader -> throwErrSt $ "Unexpected expected output header: " ++ header
                        TPSReadingExpectedOutput -> return ((emptyTestCase{name = header}, cur : out), TPSFoundCaseHeader)
                else case state of
                  TPSInitial -> throwErrSt $ "Expected case header, got: " ++ lineStr
                  TPSFoundCaseHeader -> return ((cur{input = cur.input <> line <> "\n"}, out), TPSReadingInput)
                  TPSReadingInput -> return ((cur{input = cur.input <> line <> "\n"}, out), TPSReadingInput)
                  TPSFoundExpHeader ->
                    return ((cur{expectedOutput = cur.expectedOutput <> line <> "\n"}, out), TPSReadingExpectedOutput)
                  TPSReadingExpectedOutput ->
                    return ((cur{expectedOutput = cur.expectedOutput <> line <> "\n"}, out), TPSReadingExpectedOutput)
      )
      ((emptyTestCase, []), TPSInitial)
      (BC.lines file)
  when (final /= TPSReadingExpectedOutput) $
    throwErrSt "Incomplete test case at end of file"

  return $ reverse $ acc : cases

cmpStrings :: BC.ByteString -> BC.ByteString -> IO ()
cmpStrings want act = do
  let _exp = BC.lines want
      _act = BC.lines act
  if length _exp /= length _act
    then assertFailure $ printf "Expected %d lines, got %d. got:\n%s" (length _exp) (length _act) (show _act)
    else mapM_ (\(i, e, a) -> assertEqual ("line " ++ show i) e a) (zip3 [0 :: Int ..] _exp _act)

runEvalCase :: TestCase -> IO ()
runEvalCase c = do
  rE <- runExceptT $ evalStr c.input emptyConfig{ecMaxTreeDepth = 20}
  checkResult c rE

runExplainCase :: BC.ByteString -> TestCase -> IO ()
runExplainCase query c = do
  rE <-
    runExceptT $
      explainStr
        c.input
        query
        emptyConfig{ecMaxTreeDepth = 20}
  checkResult c rE

checkResult :: TestCase -> Either String Builder -> IO ()
checkResult c rE =
  case rE of
    Left err -> assertFailure (show err)
    Right b -> do
      let act = BC.toStrict $ toLazyByteString b
          -- We strip the trailing whitespace from the expected output.
          strippedExpOut = BC.pack $ dropWhileEnd isSpace (BC.unpack c.expectedOutput)
      liftIO $ cmpStrings strippedExpOut act

parseExplainTitle :: String -> Either String (String, BC.ByteString)
parseExplainTitle title = do
  withoutClosingDelimiter <-
    maybe
      (Left $ "Explain case title must end with __query__: " ++ title)
      Right
      (T.stripSuffix "__" $ T.pack title)
  let (nameWithDelimiter, query) = T.breakOnEnd "__" withoutClosingDelimiter
      testName = T.strip $ T.dropEnd 2 nameWithDelimiter
  if T.null nameWithDelimiter || T.null testName || T.null query
    then Left $ "Explain case title must have the form name __query__: " ++ title
    else Right (T.unpack testName, BC.pack $ T.unpack query)

evalTestCase :: TestCase -> TestTree
evalTestCase c = testCase c.name (runEvalCase c)

explainTestCase :: TestCase -> TestTree
explainTestCase c =
  case parseExplainTitle c.name of
    Left err -> testCase c.name (assertFailure err)
    Right (testName, query) -> testCase testName (runExplainCase query c)

createTestsInTxtar :: (TestCase -> TestTree) -> String -> String -> IO TestTree
createTestsInTxtar makeTest path name = do
  file <- BC.readFile path
  casesE <- runExceptT $ parseTxtar file
  case casesE of
    Left err -> assertFailure ("Failed to parse txtar file: " ++ err)
    Right cases -> do
      let ts = map makeTest cases
      return $ testGroup name ts

createTestsInDir :: (TestCase -> TestTree) -> String -> IO [TestTree]
createTestsInDir makeTest dir = do
  -- sort the files so that the tests are run in order
  files <- sort <$> listDirectory dir
  -- only run the .txtar files
  reverse
    <$> foldM
      ( \acc file ->
          if reverse (take 6 (reverse file)) == ".txtar"
            then do
              group <- createTestsInTxtar makeTest (dir ++ "/" ++ file) file
              return $ group : acc
            else return acc
      )
      []
      files

e2eTests :: IO TestTree
e2eTests = do
  evalTests <- createTestsInDir evalTestCase "tests/e2e/eval"
  explainTests <- createTestsInDir explainTestCase "tests/e2e/explain"
  return $
    testGroup
      "e2e"
      [ testGroup "eval" evalTests
      , testGroup "explain" explainTests
      ]
