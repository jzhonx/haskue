module Main (main) where

import Common
import Control.Monad.Except (MonadError, runExceptT, throwError)
import Criterion.Main
import Data.ByteString.Builder (hPutBuilder)
import Eval
import System.IO (readFile, stdout)

work :: IO ()
work = do
  let conf = emptyEvalConfig{ecFilePath = "tests/bench_spec/large1.cue"}
  file <- readFile (ecFilePath conf)
  x <- runExceptT $ runIO file conf
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
