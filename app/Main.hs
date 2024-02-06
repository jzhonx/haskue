module Main where

import           Control.Monad.Except    (MonadError, runExceptT, throwError)
import           Data.ByteString.Builder (hPutBuilder)
import           Eval                    (run)
import           Parser                  (parseCUE)
import           Path                    (emptyPath)
import           System.Environment      (getArgs)
import           System.IO               (readFile, stdout)
import           Transform               (transform)
import           Value                   (Value (Int, String), strBld)

main :: IO ()
main = do
  args <- getArgs
  f <- readFile (head args)
  let x = run f
  case x of
    Left err  -> putStrLn err
    Right val -> hPutBuilder stdout (strBld val)
