{-# LANGUAGE OverloadedStrings #-}

module Util where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Logger (
  MonadLogger,
  logDebugN,
 )
import Control.Monad.State (MonadState, gets, modify)
import Data.Aeson (ToJSON, object, toJSON, (.=))
import Data.Aeson.Text (encodeToLazyText)
import Data.Maybe (fromJust, isNothing)
import Data.Text (pack)
import Data.Text.Lazy (unpack)
import Data.Time.Calendar (fromGregorian)
import Data.Time.Clock (UTCTime (..), getCurrentTime, secondsToDiffTime)
import Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds)
import Text.Printf (printf)

class HasTrace a where
  getTrace :: a -> Trace
  setTrace :: a -> Trace -> a

data Trace = Trace
  { traceID :: Int
  , traceTime :: UTCTime
  }
  deriving (Eq)

instance Show Trace where
  show t = printf "id=%s" (show $ traceID t)

instance HasTrace Trace where
  getTrace = id
  setTrace s t = t{traceID = traceID s}

data ChromeStartTrace = ChromeStartTrace
  { cstrName :: String
  , cstrTime :: Int
  , cstrArgs :: ChromeStartTraceArgs
  }
  deriving (Eq, Show)

data ChromeEndTrace = ChromeEndTrace
  { cetrName :: String
  , cetrTime :: Int
  , cetrArgs :: ChromeEndTraceArgs
  }
  deriving (Eq, Show)

data ChromeStartTraceArgs = ChromeStartTraceArgs
  { cstaTraceID :: Int
  , cstaAddr :: String
  , cstaBeforeFocus :: String
  , cstaBeforeFocusCUEVal :: String
  , cstaCustomVal :: Maybe String
  }
  deriving (Eq, Show)

data ChromeEndTraceArgs = ChromeEndTraceArgs
  { cetaResVal :: String
  , cetaFocus :: String
  , cetaFocusCUEVal :: String
  }
  deriving (Eq, Show)

data ChromeInstantTrace = ChromeInstantTrace
  { ctiName :: String
  , ctiStart :: Int
  , ctiArgs :: ChromeInstantTraceArgs
  }
  deriving (Eq, Show)

data ChromeInstantTraceArgs = ChromeInstantTraceArgs
  { ctiTraceID :: Int
  , ctiAddr :: String
  , ctiCustomVal :: Maybe String
  }
  deriving (Eq, Show)

instance ToJSON ChromeStartTrace where
  toJSON ct =
    object
      [ "name" .= cstrName ct
      , "ts" .= cstrTime ct
      , "ph" .= ("B" :: String)
      , "pid" .= (0 :: Int)
      , "tid" .= (0 :: Int)
      , "args" .= toJSON (cstrArgs ct)
      ]

instance ToJSON ChromeEndTrace where
  toJSON ct =
    object
      [ "name" .= cetrName ct
      , "ts" .= cetrTime ct
      , "ph" .= ("E" :: String)
      , "pid" .= (0 :: Int)
      , "tid" .= (0 :: Int)
      , "args" .= toJSON (cetrArgs ct)
      ]
instance ToJSON ChromeStartTraceArgs where
  toJSON cta =
    object
      ( [ "traceid" .= show (cstaTraceID cta)
        , "addr" .= cstaAddr cta
        , "bfcs" .= cstaBeforeFocus cta
        , "bfcsCue" .= cstaBeforeFocusCUEVal cta
        ]
          ++ ( if isNothing (cstaCustomVal cta)
                then []
                else ["ctm" .= fromJust (cstaCustomVal cta)]
             )
      )

instance ToJSON ChromeEndTraceArgs where
  toJSON cta =
    object
      [ "res" .= cetaResVal cta
      , "fcs" .= cetaFocus cta
      , "fcsCue" .= cetaFocusCUEVal cta
      ]

instance ToJSON ChromeInstantTrace where
  toJSON c =
    object
      [ "name" .= ctiName c
      , "ts" .= ctiStart c
      , "ph" .= ("i" :: String)
      , "s" .= ("g" :: String)
      , "pid" .= (0 :: Int)
      , "tid" .= (0 :: Int)
      , "args" .= toJSON (ctiArgs c)
      ]
instance ToJSON ChromeInstantTraceArgs where
  toJSON c =
    object
      ( [ "traceid" .= show (ctiTraceID c)
        , "addr" .= ctiAddr c
        ]
          ++ ( if isNothing (ctiCustomVal c)
                then []
                else ["ctm" .= fromJust (ctiCustomVal c)]
             )
      )
debugSpan ::
  (MonadState s m, MonadLogger m, MonadIO m, HasTrace s, Show a) =>
  String ->
  String ->
  Maybe String ->
  (String, String) ->
  m (a, String, String) ->
  m a
debugSpan name addr args (bTraced, bTracedCUEVal) f = do
  _ <- debugSpanStart name addr args bTraced bTracedCUEVal
  debugSpanExec name addr f

debugSpanStart ::
  (MonadState s m, MonadLogger m, HasTrace s, MonadIO m) =>
  String ->
  String ->
  Maybe String ->
  String ->
  String ->
  m Trace
debugSpanStart name addr args bTraced bTracedCUEVal = do
  let msg = printf "%s, at:%s" name addr
  tr <- newTrace
  let timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  logDebugStr $
    "ChromeTrace"
      ++ unpack
        ( encodeToLazyText
            ( ChromeStartTrace msg timeInMicros (ChromeStartTraceArgs (traceID tr) addr bTraced bTracedCUEVal args)
            )
        )
  return tr

debugSpanExec ::
  (MonadState s m, MonadLogger m, HasTrace s, Show a, MonadIO m) =>
  String ->
  String ->
  m (a, String, String) ->
  m a
debugSpanExec name addr f = do
  let msg = printf "%s, at:%s" name addr
  (res, focus, focusCUEVal) <- f
  tr <- newTrace
  let timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  logDebugStr $
    "ChromeTrace"
      ++ unpack
        ( encodeToLazyText
            ( ChromeEndTrace msg timeInMicros (ChromeEndTraceArgs (show res) focus focusCUEVal)
            )
        )
  return res

debugInstant ::
  (MonadState s m, MonadLogger m, HasTrace s, MonadIO m) => String -> String -> Maybe String -> m ()
debugInstant name addr args = do
  start <- lastTraceID
  tr <- gets getTrace
  let msg = printf "%s, at:%s" name addr
  let timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  logDebugStr $
    "ChromeTrace"
      ++ unpack
        ( encodeToLazyText
            ( ChromeInstantTrace msg timeInMicros (ChromeInstantTraceArgs start addr args)
            )
        )

getTraceID :: (MonadState s m, HasTrace s) => m Int
getTraceID = gets $ traceID . getTrace

newTrace :: (MonadState s m, HasTrace s, MonadIO m) => m Trace
newTrace = do
  tr <- gets getTrace
  currentTime <- liftIO getCurrentTime
  let ntr = Trace{traceTime = currentTime, traceID = traceID tr + 1}
  modify $ \s -> setTrace s ntr
  return ntr

lastTraceID :: (MonadState s m, HasTrace s) => m Int
lastTraceID = do
  tr <- gets getTrace
  return $ traceID tr

logDebugStr :: (MonadLogger m) => String -> m ()
logDebugStr = logDebugN . pack

emptyTrace :: Trace
emptyTrace = Trace{traceID = 0, traceTime = UTCTime{utctDayTime = secondsToDiffTime 0, utctDay = fromGregorian 1970 1 1}}