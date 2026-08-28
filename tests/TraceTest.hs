{-# LANGUAGE OverloadedStrings #-}

module TraceTest (tests) where

import Control.Monad.Except (ExceptT, catchError, runExceptT, throwError)
import Control.Monad.State.Strict (StateT, runStateT)
import Data.Aeson (Value (..), decode, object, (.=))
import qualified Data.Aeson.KeyMap as KeyMap
import qualified Data.ByteString.Lazy as LB
import qualified Data.ByteString.Lazy.Char8 as LBC
import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.Text as T
import Test.Tasty
import Test.Tasty.HUnit
import Util.Trace

tests :: TestTree
tests =
  testGroup
    "Trace"
    [ testCase "attaches outermost-first scopes to event arguments" testAttachScopes
    , testCase "emits span scope only on the begin event" testSpanScopeOnce
    , testCase "restores nested scopes after success and errors" testWithTraceScope
    ]

testAttachScopes :: Assertion
testAttachScopes = do
  let trace =
        (emptyTrace $ const $ return ())
          { traceScopes = ["if_1", "for_0(k,v)", "comprehension#17"]
          }
      args = object ["message" .= ("working" :: T.Text)]
  attachTraceScopes trace args
    @?= object
      [ "message" .= ("working" :: T.Text)
      , "scope" .= (["comprehension#17", "for_0(k,v)", "if_1"] :: [T.Text])
      ]

testSpanScopeOnce :: Assertion
testSpanScopeOnce = do
  outputRef <- newIORef []
  let writeChunk chunk = modifyIORef' outputRef (chunk :)
      trace =
        (emptyTrace writeChunk)
          { traceScopes = ["for_0(k,v)", "comprehension#17"]
          }
  _ <- runStateT (traceSpanStart "span" (object []) >> traceSpanExec "span" (object [])) trace
  output <- LB.concat . reverse <$> readIORef outputRef
  let events = map decode $ LBC.lines output
  map (fmap eventHasScope) events @?= [Just True, Just False]
 where
  eventHasScope (Object event) = case KeyMap.lookup "args" event of
    Just (Object args) -> KeyMap.member "scope" args
    _ -> False
  eventHasScope _ = False

testWithTraceScope :: Assertion
testWithTraceScope = do
  result <- runExceptT $ runStateT scopeAction (emptyTrace $ const $ return ())
  case result of
    Left err -> assertFailure err
    Right ((outer, recovered, stillOuter, restored), _) -> do
      outer @?= ["outer"]
      recovered @?= ["outer"]
      stillOuter @?= ["outer"]
      restored @?= []

scopeAction :: StateT Trace (ExceptT String IO) ([T.Text], [T.Text], [T.Text], [T.Text])
scopeAction = do
  (outer, recovered, stillOuter) <- withTraceScope "outer" $ do
    outer <- getTraceScopes
    recovered <-
      withTraceScope "inner" (throwError "expected")
        `catchError` const getTraceScopes
    stillOuter <- getTraceScopes
    return (outer, recovered, stillOuter)
  restored <- getTraceScopes
  return (outer, recovered, stillOuter, restored)
