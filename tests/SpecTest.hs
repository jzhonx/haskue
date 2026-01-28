{-# LANGUAGE FlexibleContexts #-}

module SpecTest where

import Control.Monad (foldM, when)
import Control.Monad.Except (ExceptT, MonadError, runExceptT)
import Control.Monad.IO.Class (liftIO)
import Data.ByteString.Builder (Builder, toLazyByteString)
import qualified Data.ByteString.Char8 as BS (ByteString, lines, pack, toStrict)
import Data.List (sort)
import Eval (ecMaxTreeDepth, emptyConfig, evalStr)
import Exception (throwErrSt)
import System.Directory (listDirectory)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf (printf)

data TestCase = TestCase
  { name :: String
  , input :: String
  , output :: Builder
  , expectedOutput :: String
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

parseTxtar :: (MonadError String m) => String -> m [TestCase]
parseTxtar file = do
  ((acc, cases), final) <-
    foldM
      ( \((cur, out), state) line ->
          if length line >= 6 && take 3 line == "-- " && drop (length line - 3) line == " --"
            then
              let header = take (length line - 6) (drop 3 line)
               in case state of
                    TPSInitial -> return ((cur{name = header}, out), TPSFoundCaseHeader)
                    TPSFoundCaseHeader -> throwErrSt $ "Unexpected case header: " ++ header
                    TPSReadingInput -> return ((cur, out), TPSFoundExpHeader)
                    TPSFoundExpHeader -> throwErrSt $ "Unexpected expected output header: " ++ header
                    TPSReadingExpectedOutput -> return ((emptyTestCase{name = header}, cur : out), TPSFoundCaseHeader)
            else case state of
              TPSInitial -> throwErrSt $ "Expected case header, got: " ++ line
              TPSFoundCaseHeader -> return ((cur{input = cur.input ++ line ++ "\n"}, out), TPSReadingInput)
              TPSReadingInput -> return ((cur{input = cur.input ++ line ++ "\n"}, out), TPSReadingInput)
              TPSFoundExpHeader ->
                return ((cur{expectedOutput = cur.expectedOutput ++ line ++ "\n"}, out), TPSReadingExpectedOutput)
              TPSReadingExpectedOutput ->
                -- allow empty lines in expected output
                if line == "\n" || line == ""
                  then return ((cur, out), TPSReadingExpectedOutput)
                  else
                    return ((cur{expectedOutput = cur.expectedOutput ++ line ++ "\n"}, out), TPSReadingExpectedOutput)
      )
      ((emptyTestCase, []), TPSInitial)
      (lines file)
  when (final /= TPSReadingExpectedOutput) $
    throwErrSt "Incomplete test case at end of file"

  return $ reverse $ acc : cases

cmpStrings :: BS.ByteString -> BS.ByteString -> IO ()
cmpStrings want act = do
  let _exp = BS.lines want
      _act = BS.lines act
  if length _exp /= length _act
    then assertFailure $ printf "Expected %d lines, got %d. got:\n%s" (length _exp) (length _act) (show _act)
    else mapM_ (\(i, e, a) -> assertEqual ("line " ++ show i) e a) (zip3 [0 ..] _exp _act)

runCase :: TestCase -> IO ()
runCase c = do
  rE <- runExceptT $ evalStr (BS.pack c.input) emptyConfig{ecMaxTreeDepth = 20}
  case rE of
    Left err -> assertFailure (show err)
    Right b -> do
      let act = BS.toStrict $ toLazyByteString b
          expOut = BS.pack c.expectedOutput
      liftIO $ cmpStrings expOut act

createTestsInTxtar :: String -> String -> IO TestTree
createTestsInTxtar path name = do
  file <- readFile path
  casesE <- runExceptT $ parseTxtar file
  case casesE of
    Left err -> assertFailure ("Failed to parse txtar file: " ++ err)
    Right cases -> do
      let ts = map (\c -> testCase c.name (runCase c)) cases
      return $ testGroup name ts

specTests :: IO TestTree
specTests = do
  let dir = "tests/spec"
  -- sort the files so that the tests are run in order
  files <- sort <$> listDirectory dir
  -- only run the .txtar files
  cases <-
    foldM
      ( \acc file ->
          if reverse (take 6 (reverse file)) == ".txtar"
            then do
              g <- createTestsInTxtar (dir ++ "/" ++ file) file
              return $ g : acc
            else return acc
      )
      []
      files
  return $ testGroup "spec_tests" (reverse cases)
