module Main where

import Control.Monad.Except (MonadError, runExceptT, throwError)
import Data.ByteString.Builder (hPutBuilder)
import Eval (eval)
import Parser (parseCUE)
import System.Environment (getArgs)
import System.IO (readFile, stdout)
import Value
  ( Value (Int, String),
    buildCUEStr,
    emptyPath,
  )

run :: String -> Either String Value
run s = do
  parsedE <- parseCUE s
  eval parsedE emptyPath

main :: IO ()
main = do
  args <- getArgs
  f <- readFile (head args)
  let x = run f
  case x of
    Left err -> putStrLn err
    Right val' -> hPutBuilder stdout (buildCUEStr val')
