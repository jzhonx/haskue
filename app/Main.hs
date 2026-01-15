module Main where

import Control.Monad.Except (runExceptT)
import qualified Data.ByteString as B
import Data.ByteString.Builder (hPutBuilder)
import Eval (Config (..), evalStr)
import Options.Applicative
import System.IO (Handle, IOMode (..), hClose, openFile, stdout)
import Util.ShowTrace (runServer)

-- New data types for subcommands
data Command
  = Export ExportConfig
  | Eval EvalConfig
  | ShowTrace FilePath String

-- Common configuration type for shared options
data CommonConfig = CommonConfig
  { ccDebug :: Bool
  , ccTrace :: Bool
  , ccTracePrintVal :: Bool
  , ccTraceExtraInfo :: Bool
  , ccTraceFilter :: String
  , ccTraceOutput :: String
  , ccMaxTreeDepth :: Int
  }

data ExportConfig = ExportConfig
  { exportFilePath :: String
  , exportFormat :: String
  , exportCommon :: CommonConfig
  }

data EvalConfig = EvalConfig
  { evalFilePath :: String
  , evalCommon :: CommonConfig
  }

-- Common options parser
commonOptions :: Parser CommonConfig
commonOptions =
  CommonConfig
    <$> switch
      ( long "debug"
          <> short 'd'
          <> help "Enable debug mode"
      )
    <*> switch
      ( long "trace"
          <> help "trace execution"
      )
    <*> switch
      ( long "trace-print-val"
          <> help "Print the value in trace output"
      )
    <*> switch
      ( long "trace-print-extra-info"
          <> help "Print the extra info in trace output"
      )
    <*> option
      str
      ( long "trace-filter"
          <> help "Filter for trace output. If empty, all traces are shown. Delimited by commas."
          <> value "reduce"
      )
    <*> option
      str
      ( long "trace-output"
          <> help "File path to output trace logs. If empty, logs are written to stdout."
          <> value ""
      )
    <*> option
      auto
      ( long "max-tree-depth"
          <> help "Maximum depth of the tree"
          <> value 0
      )

mkTraceHandle :: String -> IO Handle
mkTraceHandle "" = return stdout
mkTraceHandle path = openFile path WriteMode

-- Convert ExportConfig to EvalConfig
toEvalConfig :: ExportConfig -> IO Config
toEvalConfig exportConfig = do
  tHandle <- mkTraceHandle (ccTraceOutput (exportCommon exportConfig))
  return $
    Config
      { outputFormat = exportFormat exportConfig
      , ecDebugMode = ccDebug (exportCommon exportConfig)
      , ecTraceExec = ccTrace (exportCommon exportConfig)
      , ecTracePrintTree = ccTracePrintVal (exportCommon exportConfig)
      , ecTraceExtraInfo = ccTraceExtraInfo (exportCommon exportConfig)
      , ecTraceFilter = ccTraceFilter (exportCommon exportConfig)
      , ecTraceHandle = tHandle
      , ecMaxTreeDepth = ccMaxTreeDepth (exportCommon exportConfig)
      , ecFilePath = exportFilePath exportConfig
      }

-- Convert EvalConfig to EvalConfig (identity with new structure)
toEvalConfigEval :: EvalConfig -> IO Config
toEvalConfigEval evalConfig = do
  tHandle <- mkTraceHandle (ccTraceOutput (evalCommon evalConfig))
  return $
    Config
      { outputFormat = "cue"
      , ecDebugMode = ccDebug (evalCommon evalConfig)
      , ecTraceExec = ccTrace (evalCommon evalConfig)
      , ecTracePrintTree = ccTracePrintVal (evalCommon evalConfig)
      , ecTraceExtraInfo = ccTraceExtraInfo (evalCommon evalConfig)
      , ecTraceFilter = ccTraceFilter (evalCommon evalConfig)
      , ecTraceHandle = tHandle
      , ecMaxTreeDepth = ccMaxTreeDepth (evalCommon evalConfig)
      , ecFilePath = evalFilePath evalConfig
      }

-- Parser for export subcommand
exportParser :: Parser ExportConfig
exportParser =
  ExportConfig
    <$> argument
      str
      ( metavar "FILE"
          <> help "CUE file to parse"
      )
    <*> option
      str
      ( long "out"
          <> help "Output format, which can be one of: json, yaml, cue"
          <> value "cue"
      )
    <*> commonOptions

-- Parser for eval subcommand
evalParser :: Parser EvalConfig
evalParser =
  EvalConfig
    <$> argument
      str
      ( metavar "FILE"
          <> help "CUE file to parse"
      )
    <*> commonOptions

showTraceParser :: Parser Command
showTraceParser =
  ShowTrace
    <$> argument
      str
      ( metavar "FILEPATH"
          <> help "Path to the trace file to serve"
      )
    <*> option
      str
      ( metavar "origin"
          <> help "Origin URL for CORS, defaulting to https://ui.perfetto.dev"
          <> value "https://ui.perfetto.dev"
      )

-- Main command parser
commandParser :: Parser Command
commandParser =
  subparser $
    command
      "export"
      ( info
          (Export <$> exportParser <**> helper)
          (progDesc "Export CUE file with specified format")
      )
      <> command
        "eval"
        ( info
            (Eval <$> evalParser <**> helper)
            (progDesc "Evaluate CUE file")
        )
      <> command
        "show-trace"
        ( info
            (showTraceParser <**> helper)
            (progDesc "Serve a trace file over HTTP for viewing in a browser")
        )

runEval :: Config -> IO ()
runEval conf = do
  content <- B.readFile (ecFilePath conf)
  x <- runExceptT $ evalStr content conf
  case x of
    Left err -> putStrLn $ "Internal bug: " ++ err
    Right b -> hPutBuilder stdout b
  hClose (ecTraceHandle conf)

main :: IO ()
main = do
  cmd <- execParser (info (commandParser <**> helper) fullDesc)
  case cmd of
    Export exportConfig -> do
      conf <- toEvalConfig exportConfig
      runEval conf
    Eval evalConfig -> do
      conf <- toEvalConfigEval evalConfig
      runEval conf
    ShowTrace path originUrl -> runServer path originUrl
