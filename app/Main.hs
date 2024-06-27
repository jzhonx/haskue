module Main where

import AST (exprBld)
import Control.Monad.Except (MonadError, runExceptT, throwError)
import Data.ByteString.Builder (hPutBuilder)
import Eval (runIO)
import Parser (parseCUE)
import System.Environment (getArgs)
import System.IO (readFile, stdout)
import Tree

main :: IO ()
main = do
  args <- getArgs
  f <- readFile (head args)
  x <- runExceptT $ runIO f >>= \tc -> return $ buildASTExpr (fst tc)
  case x of
    Left err -> putStrLn err
    Right expr -> hPutBuilder stdout (exprBld expr)
