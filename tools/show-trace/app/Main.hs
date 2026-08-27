module Main where

import Options.Applicative
import ShowTrace.Server (runServer)

data Config = Config
  { traceFile :: FilePath
  , originUrl :: String
  , serverPort :: Int
  }

configParser :: Parser Config
configParser =
  Config
    <$> argument
      str
      ( metavar "TRACE_FILE"
          <> help "Path to the newline-delimited JSON trace file"
      )
    <*> option
      str
      ( long "origin"
          <> metavar "URL"
          <> help "Perfetto UI origin allowed to request the trace"
          <> value "https://ui.perfetto.dev"
          <> showDefault
      )
    <*> option
      auto
      ( long "port"
          <> metavar "PORT"
          <> help "Local HTTP port used to serve the trace"
          <> value 9001
          <> showDefault
      )

main :: IO ()
main = do
  config <- execParser parserInfo
  runServer (traceFile config) (originUrl config) (serverPort config)
 where
  parserInfo =
    info
      (configParser <**> helper)
      (fullDesc <> progDesc "Serve a Haskue trace for viewing in Perfetto")
