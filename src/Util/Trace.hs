{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Util.Trace where

import Control.DeepSeq (NFData)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, gets, modify')
import Data.Aeson (ToJSON, Value, encode, object, toJSON, (.=))
import qualified Data.ByteString.Lazy as LB
import qualified Data.Text as T
import Data.Time.Calendar (fromGregorian)
import Data.Time.Clock (UTCTime (..), getCurrentTime, secondsToDiffTime)
import Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds)
import GHC.Generics (Generic)
import Text.Printf (printf)

class HasTrace a where
  getTrace :: a -> Trace
  setTrace :: a -> Trace -> a

data Trace = Trace
  { traceID :: Int
  , traceTime :: UTCTime
  , tPut :: LB.ByteString -> IO ()
  }
  deriving (Generic, NFData)

instance Show Trace where
  show t = printf "id=%s" (show $ traceID t)

instance HasTrace Trace where
  getTrace = id
  setTrace :: Trace -> Trace -> Trace
  setTrace s t = t{traceID = traceID s}

type TraceM s m =
  ( MonadState s m
  , HasTrace s
  , MonadIO m
  )

data ChromeStartTrace = ChromeStartTrace
  { cstrName :: !T.Text
  , cstrTime :: !Int
  , cstrArgs :: Value
  }
  deriving (Eq, Show)

data ChromeEndTrace = ChromeEndTrace
  { cetrName :: !T.Text
  , cetrTime :: !Int
  , cetrArgs :: Value
  }
  deriving (Eq, Show)

data ChromeInstantTrace = ChromeInstantTrace
  { ctiName :: !T.Text
  , ctiStart :: !Int
  , ctiArgs :: Value
  }
  deriving (Eq, Show)

instance ToJSON ChromeStartTrace where
  toJSON ct =
    object
      [ "name" .= cstrName ct
      , "ts" .= cstrTime ct
      , "ph" .= ("B" :: T.Text)
      , "pid" .= (0 :: Int)
      , "tid" .= (0 :: Int)
      , "args" .= cstrArgs ct
      ]

instance ToJSON ChromeEndTrace where
  toJSON ct =
    object
      [ "name" .= cetrName ct
      , "ts" .= cetrTime ct
      , "ph" .= ("E" :: T.Text)
      , "pid" .= (0 :: Int)
      , "tid" .= (0 :: Int)
      , "args" .= cetrArgs ct
      ]

instance ToJSON ChromeInstantTrace where
  toJSON c =
    object
      [ "name" .= ctiName c
      , "ts" .= ctiStart c
      , "ph" .= ("i" :: T.Text)
      , "s" .= ("g" :: T.Text)
      , "pid" .= (0 :: Int)
      , "tid" .= (0 :: Int)
      , "args" .= ctiArgs c
      ]

traceSpanStart :: (TraceM s m) => T.Text -> Value -> m ()
traceSpanStart name args = do
  tr <- newTrace
  let
    timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
    st =
      encode
        ( ChromeStartTrace name timeInMicros args
        )

  dumpTrace tr.tPut st

{- | Trace the execution span of an action.

The function `g` is used to retrieve focus and result information after the action is executed.
-}
traceSpanExec :: (TraceM s m) => T.Text -> Value -> m ()
traceSpanExec name args = do
  tr <- newTrace
  let
    timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  dumpTrace tr.tPut $
    encode
      ( ChromeEndTrace name timeInMicros args
      )

debugInstant :: (TraceM s m) => T.Text -> Value -> m ()
debugInstant name args = do
  tr <- gets getTrace
  let timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  dumpTrace tr.tPut $
    encode
      ( ChromeInstantTrace name timeInMicros args
      )

dumpTrace :: (MonadIO m) => (LB.ByteString -> IO ()) -> LB.ByteString -> m ()
dumpTrace f msg = liftIO $ do
  f msg
  f "\n"

getTraceID :: (MonadState s m, HasTrace s) => m Int
getTraceID = gets $ traceID . getTrace

newTrace :: (TraceM s m) => m Trace
newTrace = do
  tr <- gets getTrace
  currentTime <- liftIO getCurrentTime
  let ntr = tr{traceTime = currentTime, traceID = traceID tr + 1}
  modify' $ \s -> setTrace s ntr
  return ntr

emptyTrace :: (LB.ByteString -> IO ()) -> Trace
emptyTrace f =
  Trace
    { traceID = 0
    , traceTime = UTCTime{utctDayTime = secondsToDiffTime 0, utctDay = fromGregorian 1970 1 1}
    , tPut = f
    }