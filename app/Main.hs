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
      ( long "trace"
          <> help "trace execution"
      )
    <*> switch
      ( long "trace-print-tree"
          <> help "trace execution"
      )
    <*> switch
      ( long "show-mutable-args"
          <> help "Show mutable args in the mermaid graph"
      )
    <*> option
      auto
      ( long "max-tree-depth"
          <> help "Maximum depth of the tree"
          <> value 0
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
    Right b -> hPutBuilder stdout b
