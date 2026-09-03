module Main where

import Control.Monad.Except (runExceptT)
import qualified Data.ByteString as B
import Data.ByteString.Builder (hPutBuilder)
import qualified Data.ByteString.Char8 as BC
import Data.Version (showVersion)
import Eval (Config (..), evalSelectedStr, evalStr, explainExpr, explainStr)
import Options.Applicative
import qualified Paths_haskue
import Reduce.Monad (TraceConfig (..))
import System.Exit (die)
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
  , evalExpression :: Maybe String
  , evalExplain :: Bool
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
          <> help "CUE file to parse, or - for stdin"
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
          <> help "CUE file to parse, or - for stdin"
      )
    <*> optional
      ( strOption
          ( short 'e'
              <> long "expression"
              <> metavar "EXPR"
              <> help "Evaluate this reference expression only"
          )
      )
    <*> switch
      ( long "explain"
          <> help "Show the selected expression's value and conjuncts (requires -e)"
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
                  <> help "CUE file to parse, or - for stdin"
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
            (progDesc "Deprecated: use eval FILE -e EXPR --explain")
        )

runEval :: Config -> IO ()
runEval conf = do
  (content, sourcePath) <- readSource (ecFilePath conf)
  x <- runExceptT $ evalStr content conf{ecFilePath = sourcePath}
  case x of
    Left err -> putStrLn $ "Internal bug: " ++ err
    Right b -> hPutBuilder stdout b
  hClose (ecTraceHandle conf)

runEvalCommand :: EvalConfig -> Config -> IO ()
runEvalCommand evalConfig conf =
  case evalExpression evalConfig of
    Nothing -> runEval conf
    Just expression -> do
      (content, sourcePath) <- readSource (ecFilePath conf)
      let sourceConf = conf{ecFilePath = sourcePath}
          query = BC.pack expression
      result <-
        runExceptT $
          if evalExplain evalConfig
            then explainStr content query sourceConf
            else evalSelectedStr content query sourceConf
      case result of
        Left err -> die $ "error: " ++ err
        Right builder -> hPutBuilder stdout builder
      hClose (ecTraceHandle conf)

{- | Read a source file, treating @-@ as standard input. The empty source path
makes scanner diagnostics use the conventional @-:line:column@ form.
-}
readSource :: FilePath -> IO (B.ByteString, FilePath)
readSource "-" = do
  content <- B.getContents
  return (content, "")
readSource path = do
  content <- B.readFile path
  return (content, path)

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
      (source, sourcePath) <- readSource path
      runExceptT $ explainStr source query conf{ecFilePath = sourcePath}
    ExplainExpr source -> runExceptT $ explainExpr (BC.pack source) query conf
  case result of
    Left err -> putStrLn $ "error: " ++ err
    Right builder -> hPutBuilder stdout builder
  hClose (ecTraceHandle conf)

main :: IO ()
main = do
  cmd <- execParser (info (commandParser <**> helper <**> versionOption) fullDesc)
  case cmd of
    Export exportConfig -> do
      conf <- toEvalConfig exportConfig
      runEval conf
    Eval evalConfig -> do
      case (evalExplain evalConfig, evalExpression evalConfig) of
        (True, Nothing) -> die "error: --explain requires --expression"
        _ -> do
          conf <- toEvalConfigEval evalConfig
          runEvalCommand evalConfig conf
    Explain explainConfig -> runExplain explainConfig
 where
  versionOption =
    infoOption
      ("haskue " ++ showVersion Paths_haskue.version)
      (long "version" <> help "Show the Haskue version")
