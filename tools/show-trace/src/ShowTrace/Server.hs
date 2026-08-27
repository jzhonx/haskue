{-
  Copyright (C) 2021 The Android Open Source Project

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-}
{-# LANGUAGE OverloadedStrings #-}

module ShowTrace.Server (runServer, transformTraceFile) where

import Control.Concurrent (forkIO, newEmptyMVar, takeMVar, tryPutMVar)
import Control.Monad (void)
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as LB
import qualified Data.Text as Text
import Network.HTTP.Types (status200, status404)
import Network.Wai (Application, pathInfo, responseLBS)
import Network.Wai.Handler.Warp (defaultSettings, runSettings, setHost, setPort)
import Network.Wai.Middleware.Cors (cors, corsMethods, corsOrigins, simpleCorsResourcePolicy)
import System.Directory (makeAbsolute)
import System.FilePath (takeFileName)

-- | Convert a newline-delimited JSON stream into a single JSON array.
transformTraceFile :: LB.ByteString -> LB.ByteString
transformTraceFile input =
  let nonEmptyLines = filter (not . LB.null) (LB.split 10 input)
   in LB.concat ["[", LB.intercalate "," nonEmptyLines, "]"]

runServer :: FilePath -> String -> Int -> IO ()
runServer path originUrl port = do
  absPath <- makeAbsolute path
  let fileName = takeFileName absPath
      route = [Text.pack fileName]

  doneSignal <- newEmptyMVar

  let app :: Application
      app request respond =
        if pathInfo request == route
          then do
            traceContent <- LB.readFile absPath
            result <-
              respond $
                responseLBS
                  status200
                  [ ("Content-Type", "application/json; charset=utf-8")
                  , ("Cache-Control", "no-cache")
                  ]
                  (transformTraceFile traceContent)
            void $ tryPutMVar doneSignal ()
            pure result
          else
            respond $ responseLBS status404 [] "File not found"

      policy =
        simpleCorsResourcePolicy
          { corsOrigins = Just ([B8.pack originUrl], True)
          , corsMethods = ["GET"]
          }
      settings = setPort port $ setHost "127.0.0.1" defaultSettings
      address =
        originUrl
          ++ "/#!/?url=http://127.0.0.1:"
          ++ show port
          ++ "/"
          ++ fileName
          ++ "&referrer=open_trace_in_ui"

  putStrLn $ "Serving trace: " ++ path
  putStrLn $ "Open URL in browser: " ++ address

  void $ forkIO $ runSettings settings (cors (const $ Just policy) app)
  takeMVar doneSignal
  putStrLn "Trace file downloaded by browser. Shutting down server."
