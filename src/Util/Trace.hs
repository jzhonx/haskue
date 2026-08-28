{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Util.Trace where

import Control.DeepSeq (NFData)
import Control.Monad.Except (MonadError, catchError, throwError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, gets, modify')
import Data.Aeson (ToJSON, Value (..), encode, object, toJSON, (.=))
import qualified Data.Aeson.KeyMap as KeyMap
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
  , traceScopes :: [T.Text]
  -- ^ The current trace scope stack, with the innermost scope first.
  , tPut :: LB.ByteString -> IO ()
  }
  deriving (Generic, NFData)

instance Show Trace where
  show t = printf "id=%s" (show $ traceID t)

instance HasTrace Trace where
  getTrace = id
  setTrace :: Trace -> Trace -> Trace
  setTrace s t = t{traceID = traceID s}

type TraceM s m = (MonadState s m, HasTrace s, MonadIO m)

modifyTrace :: (MonadState s m, HasTrace s) => (Trace -> Trace) -> m ()
modifyTrace f = modify' $ \s -> setTrace s (f $ getTrace s)

getTraceScopes :: (MonadState s m, HasTrace s) => m [T.Text]
getTraceScopes = reverse . traceScopes <$> gets getTrace

setTraceScopes :: (MonadState s m, HasTrace s) => [T.Text] -> m ()
setTraceScopes scopes = modifyTrace $ \trace -> trace{traceScopes = reverse scopes}

{- | Run an action inside a trace scope.

The previous scope stack is restored when the action returns or raises a
'MonadError' error. Trace scopes are presentation-only and never affect
evaluation addresses.
-}
withTraceScope :: (MonadState s m, HasTrace s, MonadError e m) => T.Text -> m a -> m a
withTraceScope scope action = do
  oldScopes <- getTraceScopes
  setTraceScopes (oldScopes ++ [scope])
  let restore = setTraceScopes oldScopes
  result <- action `catchError` \err -> restore >> throwError err
  restore
  return result

attachTraceScopes :: Trace -> Value -> Value
attachTraceScopes trace args
  | null trace.traceScopes = args
  | otherwise =
      let scopes = toJSON $ reverse trace.traceScopes
       in case args of
            Object fields -> Object $ KeyMap.insert "scope" scopes fields
            other -> object ["scope" .= scopes, "value" .= other]

data ChromeStartTrace = ChromeStartTrace
  { cstrName :: !T.Text
  , cstrTime :: !Int
  , cstrArgs :: Value
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

data ChromeEndTrace = ChromeEndTrace
  { cetrName :: !T.Text
  , cetrTime :: !Int
  , cetrArgs :: Value
  }
  deriving (Eq, Show)

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

data ChromeInstantTrace = ChromeInstantTrace
  { ctiName :: !T.Text
  , ctiStart :: !Int
  , ctiArgs :: Value
  }
  deriving (Eq, Show)

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

data ChromeFlowEvent = ChromeFlowEvent
  { cfeTime :: !Int
  , cfePhase :: !T.Text
  , cfeID :: !T.Text
  }
  deriving (Eq, Show)

instance ToJSON ChromeFlowEvent where
  toJSON c =
    object
      [ "ts" .= cfeTime c
      , "ph" .= cfePhase c
      , "pid" .= (0 :: Int)
      , "tid" .= (0 :: Int)
      , "id" .= cfeID c
      ]

traceSpanStart :: (TraceM s m) => T.Text -> Value -> m ()
traceSpanStart name args = do
  tr <- newTrace
  let
    timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
    st =
      encode
        (ChromeStartTrace{cstrName = name, cstrTime = timeInMicros, cstrArgs = attachTraceScopes tr args})

  dumpTrace tr.tPut st

{- | Trace the execution span of an action.

The function `g` is used to retrieve focus and result information after the action is executed.
-}
traceSpanExec :: (TraceM s m) => T.Text -> Value -> m ()
traceSpanExec name args = do
  tr <- newTrace
  let
    timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  -- Chrome trace viewers merge the arguments of matching begin and end
  -- events. The begin event already contains the scope; repeating it here
  -- would make the viewer display every scope twice.
  dumpTrace tr.tPut $
    encode
      (ChromeEndTrace{cetrName = name, cetrTime = timeInMicros, cetrArgs = args})

debugInstant :: (TraceM s m) => T.Text -> Value -> m ()
debugInstant name args = do
  tr <- gets getTrace
  let timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  dumpTrace tr.tPut $
    encode
      (ChromeInstantTrace{ctiName = name, ctiStart = timeInMicros, ctiArgs = attachTraceScopes tr args})

emitFlowEvent :: (TraceM s m) => T.Text -> T.Text -> m ()
emitFlowEvent phase flowID = do
  tr <- gets getTrace
  let timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  dumpTrace tr.tPut $
    encode
      (ChromeFlowEvent{cfeTime = timeInMicros, cfePhase = phase, cfeID = flowID})

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
    , traceScopes = []
    , tPut = f
    }
