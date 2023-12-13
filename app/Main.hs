module Main where

import Control.Monad.Except (MonadError, runExceptT, throwError)
import Data.ByteString.Builder (hPutBuilder)
import Eval (eval, initEnv)
import Parser (parseCUE)
import System.Environment (getArgs)
import System.IO (readFile, stdout)
import Value (Value (Int, String), buildCUEStr)

main :: IO ()
main = do
  args <- getArgs
  f <- readFile (head args)
  let expr = parseCUE f
  print expr
  let x = eval expr
  case x of
    Left err -> putStrLn err
    Right val' -> hPutBuilder stdout (buildCUEStr val')
