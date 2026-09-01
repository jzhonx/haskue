module Main (main) where

import Control.Monad.Except (runExceptT)
import Criterion.Main
import qualified Data.ByteString.Char8 as BS
import Eval
import System.IO (readFile)

work :: FilePath -> IO ()
work filePath = do
  let conf = emptyConfig{ecFilePath = filePath}
  content <- readFile (ecFilePath conf)
  x <- runExceptT $ evalStr (BS.pack content) conf
  case x of
    Left err -> ioError (userError err)
    Right _ -> return ()

main :: IO ()
main =
  defaultMain
    [ bgroup
        "spec"
        [ bgroup
            "eval"
            [ bench "large1" $ nfIO $ work "tests/bench_spec/large1.cue"
            , bench "large2" $ nfIO $ work "tests/bench_spec/large2.cue"
            ]
        ]
    ]
