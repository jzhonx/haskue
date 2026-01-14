module Main (main) where

import Control.Monad.Except (MonadError, runExceptT, throwError)
import Criterion.Main
import Data.ByteString.Builder (hPutBuilder)
import qualified Data.ByteString.Char8 as BS
import Eval
import System.IO (readFile, stdout)

work :: IO ()
work = do
  let conf = emptyConfig{ecFilePath = "tests/bench_spec/large1.cue"}
  content <- readFile (ecFilePath conf)
  x <- runExceptT $ evalStr (BS.pack content) conf
  case x of
    Left err -> putStrLn err
    Right _ -> return ()

main :: IO ()
main =
  defaultMain
    [ bgroup
        "spec"
        [ bgroup
            "eval"
            [ bench "large1" $ nfIO work
            ]
        ]
    ]
