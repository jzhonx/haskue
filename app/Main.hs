module Main where

import Control.Monad.Except (runExceptT)
import qualified Data.ByteString as B
import Data.ByteString.Builder (hPutBuilder)
import Eval (EvalConfig (..), runIO)
import Options.Applicative
import System.IO (stdout)

options :: Parser EvalConfig
options =
  EvalConfig
    <$> option
      str
      ( long "output"
          <> help "Output format: json, yaml, cue"
          <> value "cue"
      )
    <*> switch
      ( long "debug"
          <> short 'd'
          <> help "Enable debug mode"
      )
    <*> switch
      ( long "trace"
          <> help "trace execution"
      )
    <*> switch
      ( long "trace-print-tree"
          <> help "Print the execution tree"
      )
    <*> switch
      ( long "trace-print-extra-info"
          <> help "Print the extra info in trace output"
      )
    <*> option
      str
      ( long "trace-filter"
          <> help "Filter for trace output. If empty, all traces are shown. Delimited by commas."
          <> value "reduce,fullReduce,drainRefSysQueue,notify,bfsLoopQ"
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
  file <- B.readFile (ecFilePath opts)
  x <- runExceptT $ runIO file opts
  case x of
    Left err -> putStrLn $ "Internal bug: " ++ err
    Right b -> hPutBuilder stdout b
