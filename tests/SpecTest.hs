{-# LANGUAGE FlexibleContexts #-}

module SpecTest where

import AST (declsBld)
import Control.Monad (when)
import Control.Monad.Except (MonadError, runExcept, runExceptT, throwError)
import Data.ByteString.Builder (
  toLazyByteString,
 )
import qualified Data.ByteString.Lazy.Char8 as BS (ByteString, lines, pack)
import Data.List (sort)
import Eval (emptyEvalConfig, runIO)
import System.Directory (listDirectory)
import System.IO (readFile)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Printf (printf)

parseTxtar :: (MonadError String m) => String -> m (String, String)
parseTxtar file = do
  let ((input, exp), state) =
        foldr
          ( \line ((input, exp), state) ->
              if length line >= 6 && take 3 line == "-- " && drop (length line - 3) line == " --"
                then case state of
                  0 -> ((input, exp), 1)
                  1 -> ((input, exp), 2)
                else case state of
                  0 -> ((input, line ++ "\n" ++ exp), 0)
                  1 -> ((line ++ "\n" ++ input, exp), 1)
                  2 -> ((input, exp), 2)
          )
          (("", ""), 0)
          (lines file)
  when (state /= 2) $ throwError "No expected output"
  return (input, exp)

cmpStrings :: BS.ByteString -> BS.ByteString -> IO ()
cmpStrings exp act = do
  let _exp = BS.lines exp
      _act = BS.lines act
  if length _exp /= length _act
    then assertFailure $ printf "Expected %d lines, got %d" (length _exp) (length _act)
    else mapM_ (\(i, e, a) -> assertEqual ("line " ++ show i) e a) (zip3 [0 ..] _exp _act)

createTest :: String -> String -> TestTree
createTest path name = testCase name $ do
  file <- readFile path
  x <- runExceptT $ do
    (input, exp) <- parseTxtar file
    r <- runIO input emptyEvalConfig
    return (exp, r)
  case x of
    Left err -> assertFailure err
    Right (_exp, b) -> do
      let act = toLazyByteString b
          exp = BS.pack _exp
      cmpStrings exp act

specTests :: IO TestTree
specTests = do
  let dir = "tests/spec"
  -- sort the files so that the tests are run in order
  files <- sort <$> listDirectory dir
  -- only run the .txtar files
  let cases =
        foldr
          ( \file acc ->
              if reverse (take 6 (reverse file)) == ".txtar"
                then createTest (dir ++ "/" ++ file) file : acc
                else acc
          )
          []
          files
  return $ testGroup "Spec tests" cases
