module Main where

import AST (declsBld)
import Control.Monad.Except (MonadError, runExceptT, throwError)
import Data.ByteString.Builder (hPutBuilder)
import Eval (EvalConfig (..), runIO)
import Options.Applicative
import System.IO (readFile, stdout)

options :: Parser EvalConfig
options =
  EvalConfig
    <$> switch
      ( long "debug"
          <> short 'd'
          <> help "Enable debug logging"
      )
    <*> switch
      ( long "mermaid"
          <> short 'm'
          <> help "Output mermaid graph"
      )
    <*> argument
      str
      ( metavar "FILE"
          <> help "CUE file to parse"
      )

main :: IO ()
main = do
  opts <- execParser (info (options <**> helper) fullDesc)
  file <- readFile (ecFilePath opts)
  x <- runExceptT $ runIO file opts
  case x of
    Left err -> putStrLn err
    Right decls -> hPutBuilder stdout (declsBld 0 decls)
