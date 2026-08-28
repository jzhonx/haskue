module Main where

import Control.Monad.Except (runExceptT)
import qualified Data.ByteString as B
import Data.ByteString.Builder (hPutBuilder)
import qualified Data.ByteString.Char8 as BC
import Eval (Config (..), evalStr, explainExpr, explainStr)
import Options.Applicative
import Reduce.Monad (TraceConfig (..))
import System.IO (Handle, IOMode (..), hClose, openFile, stdout)

-- New data types for subcommands
data Command
  = Export ExportConfig
  | Eval EvalConfig
  | Explain ExplainConfig

-- Common configuration type for shared options
data CommonConfig = CommonConfig
  { ccDebug :: Bool
  , ccTrace :: Bool
  , ccTraceDisableShowValue :: Bool
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

data ExplainInput
  = ExplainFile FilePath
  | ExplainExpr String

data ExplainConfig = ExplainConfig
  { explainInput :: ExplainInput
  , explainQuery :: String
  , explainCommon :: CommonConfig
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
      ( long "trace-disable-show-value"
          <> help "Whether to disable showing values in trace output"
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

-- | Convert ExportConfig to EvalConfig
toEvalConfig :: ExportConfig -> IO Config
toEvalConfig exportConfig = do
  let cconf = exportCommon exportConfig
  tHandle <- mkTraceHandle (ccTraceOutput cconf)
  return $
    Config
      { outputFormat = exportFormat exportConfig
      , ecDebugMode = ccDebug cconf
      , ecTraceConfig =
          TraceConfig
            { stTraceEnable = ccTrace cconf
            , stTraceDisableShowValue = ccTraceDisableShowValue cconf
            }
      , ecTraceHandle = tHandle
      , ecMaxTreeDepth = ccMaxTreeDepth cconf
      , ecFilePath = exportFilePath exportConfig
      }

-- | Convert EvalConfig to EvalConfig (identity with new structure)
toEvalConfigEval :: EvalConfig -> IO Config
toEvalConfigEval evalConfig = do
  let cconf = evalCommon evalConfig
  tHandle <- mkTraceHandle (ccTraceOutput cconf)
  return $
    Config
      { outputFormat = "cue"
      , ecDebugMode = ccDebug cconf
      , ecTraceConfig =
          TraceConfig
            { stTraceEnable = ccTrace cconf
            , stTraceDisableShowValue = ccTraceDisableShowValue cconf
            }
      , ecTraceHandle = tHandle
      , ecMaxTreeDepth = ccMaxTreeDepth cconf
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

explainInputParser :: Parser ExplainInput
explainInputParser =
  ( ExplainExpr
      <$> strOption
        ( short 'e'
            <> long "expression"
            <> metavar "EXPR"
            <> help "Inline CUE expression to evaluate"
        )
  )
    <|> ( ExplainFile
            <$> argument
              str
              ( metavar "FILE"
                  <> help "CUE file to parse"
              )
        )

explainParser :: Parser ExplainConfig
explainParser =
  ExplainConfig
    <$> explainInputParser
    <*> argument
      str
      ( metavar "QUERY"
          <> help "Value path to explain"
      )
    <*> commonOptions

-- | Main command parser
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
        "explain"
        ( info
            (Explain <$> explainParser <**> helper)
            (progDesc "Explain how a CUE value is calculated")
        )

runEval :: Config -> IO ()
runEval conf = do
  content <- B.readFile (ecFilePath conf)
  x <- runExceptT $ evalStr content conf
  case x of
    Left err -> putStrLn $ "Internal bug: " ++ err
    Right b -> hPutBuilder stdout b
  hClose (ecTraceHandle conf)

toExplainEvalConfig :: ExplainConfig -> IO Config
toExplainEvalConfig explainConfig = do
  let cconf = explainCommon explainConfig
      filePath = case explainInput explainConfig of
        ExplainFile path -> path
        ExplainExpr _ -> ""
  tHandle <- mkTraceHandle (ccTraceOutput cconf)
  return $
    Config
      { outputFormat = "cue"
      , ecDebugMode = ccDebug cconf
      , ecTraceConfig =
          TraceConfig
            { stTraceEnable = ccTrace cconf
            , stTraceDisableShowValue = ccTraceDisableShowValue cconf
            }
      , ecTraceHandle = tHandle
      , ecMaxTreeDepth = ccMaxTreeDepth cconf
      , ecFilePath = filePath
      }

runExplain :: ExplainConfig -> IO ()
runExplain explainConfig = do
  conf <- toExplainEvalConfig explainConfig
  let query = BC.pack (explainQuery explainConfig)
  result <- case explainInput explainConfig of
    ExplainFile path -> do
      source <- B.readFile path
      runExceptT $ explainStr source query conf
    ExplainExpr source -> runExceptT $ explainExpr (BC.pack source) query conf
  case result of
    Left err -> putStrLn $ "error: " ++ err
    Right builder -> hPutBuilder stdout builder
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
    Explain explainConfig -> runExplain explainConfig
