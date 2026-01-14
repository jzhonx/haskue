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

module Util.ShowTrace where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Monad (void)
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as LB
import Data.Text.Encoding (encodeUtf8)
import Network.HTTP.Types (status200, status404)
import Network.Wai (Application, Request (..), responseFile, responseLBS)
import Network.Wai.Handler.Warp (defaultSettings, runSettings, setHost, setPort)
import Network.Wai.Middleware.Cors (cors, corsMethods, corsOrigins, simpleCorsResourcePolicy)
import System.Console.ANSI (
  Color (..),
  ColorIntensity (Vivid),
  ConsoleLayer (Foreground),
  SGR (Reset, SetColor),
  setSGRCode,
 )
import System.Directory (makeAbsolute)
import System.FilePath (takeFileName)

-- ANSI Color Helpers
colorCode :: Color -> String
colorCode c = setSGRCode [SetColor Foreground Vivid c]

resetCode :: String
resetCode = setSGRCode [Reset]

boldCode :: String
boldCode = setSGRCode [SetColor Foreground Vivid White] -- Approximate bold with Vivid White

-- | Convert the trace file by converting the newline delimited JSON stream to a single JSON array.
transformTraceFile :: LB.ByteString -> LB.ByteString
transformTraceFile input =
  let lns = LB.split 10 input -- 10 is the ASCII code for newline
      nonEmptyLines = filter (not . LB.null) lns
      commaASCII = LB.pack [44] -- 44 is ASCII code for comma
      joined = LB.intercalate commaASCII nonEmptyLines
   in LB.concat [LB.pack [91], joined, LB.pack [93]] -- 91 = '[', 93 = ']'

-- The Core Server Logic
runServer :: FilePath -> String -> IO ()
runServer path originUrl = do
  absPath <- makeAbsolute path
  let fileName = takeFileName absPath
  let port = 9001

  -- MVar to signal when the file has been successfully requested so we can exit
  doneSignal <- newEmptyMVar

  let app :: Application
      app req respond = do
        let pathInfo = B8.unpack $ B8.tail (B8.concat (map (\s -> B8.cons '/' (encodeUtf8 s)) (Network.Wai.pathInfo req)))
        if pathInfo == fileName
          then do
            content <- LB.readFile absPath
            -- File found and served
            void $ putMVar doneSignal ()
            respond $
              responseLBS
                status200
                [ ("Content-Type", "application/octet-stream")
                , ("Cache-Control", "no-cache")
                ]
                (transformTraceFile content)
          else
            respond $ responseLBS status404 [] "File not found"

  -- Setup CORS middleware
  let corsMiddleware = cors (const $ Just policy)
       where
        policy =
          simpleCorsResourcePolicy
            { corsOrigins = Just ([B8.pack originUrl], True)
            , corsMethods = ["GET"]
            }

  let settings = setPort port $ setHost "127.0.0.1" defaultSettings
  let address = originUrl ++ "/#!/?url=http://127.0.0.1:" ++ show port ++ "/" ++ fileName ++ "&referrer=open_trace_in_ui"

  putStrLn $ "Opening the trace (" ++ path ++ ") in the browser"

  putStrLn $ "Open URL in browser: " ++ address

  -- Run Warp in a background thread
  void $ forkIO $ runSettings settings (corsMiddleware app)

  -- Block the main thread until the file is requested
  takeMVar doneSignal
  putStrLn "Trace file downloaded by browser. Shutting down server."
