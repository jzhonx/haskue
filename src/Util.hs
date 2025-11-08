{-# LANGUAGE OverloadedStrings #-}

module Util where

import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, gets, modify')
import Data.Aeson (ToJSON, Value, object, toJSON, (.=))
import Data.Aeson.Text (encodeToLazyText)
import Data.Maybe (fromJust, isNothing)
import Data.Text (pack)
import qualified Data.Text as T
import Data.Text.Lazy (toStrict)
import Data.Time.Calendar (fromGregorian)
import Data.Time.Clock (UTCTime (..), getCurrentTime, secondsToDiffTime)
import Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds)
import System.IO (hPutStr, stderr)
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
  setTrace :: Trace -> Trace -> Trace
  setTrace s t = t{traceID = traceID s}

data ChromeStartTrace = ChromeStartTrace
  { cstrName :: !T.Text
  , cstrTime :: !Int
  , cstrArgs :: ChromeStartTraceArgs
  }
  deriving (Eq, Show)

data ChromeEndTrace = ChromeEndTrace
  { cetrName :: !T.Text
  , cetrTime :: !Int
  , cetrArgs :: ChromeEndTraceArgs
  }
  deriving (Eq, Show)

data ChromeStartTraceArgs = ChromeStartTraceArgs
  { cstaTraceID :: !Int
  , cstaAddr :: !T.Text
  , cstaBeforeFocus :: Value
  , cstaCustomVal :: Maybe Value
  }
  deriving (Eq, Show)

data ChromeEndTraceArgs = ChromeEndTraceArgs
  { cetaResVal :: Value
  , cetaFocus :: Value
  }
  deriving (Eq, Show)

data ChromeInstantTrace = ChromeInstantTrace
  { ctiName :: !T.Text
  , ctiStart :: !Int
  , ctiArgs :: ChromeInstantTraceArgs
  }
  deriving (Eq, Show)

data ChromeInstantTraceArgs = ChromeInstantTraceArgs
  { ctiTraceID :: !Int
  , ctiAddr :: !T.Text
  , ctiCustomVal :: Maybe Value
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
      , "args" .= toJSON (cstrArgs ct)
      ]

instance ToJSON ChromeEndTrace where
  toJSON ct =
    object
      [ "name" .= cetrName ct
      , "ts" .= cetrTime ct
      , "ph" .= ("E" :: T.Text)
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

traceSpan ::
  (MonadState s m, MonadIO m, HasTrace s) =>
  (Bool, Bool) ->
  T.Text ->
  T.Text ->
  Maybe Value ->
  Value ->
  (a -> m Value) ->
  m (a, Value) ->
  m a
traceSpan flags name addr args bTraced g action = do
  _ <- traceSpanStart flags name addr args bTraced
  traceSpanExec flags name addr g action

traceSpanStart ::
  (MonadState s m, HasTrace s, MonadIO m) =>
  (Bool, Bool) ->
  T.Text ->
  T.Text ->
  Maybe Value ->
  Value ->
  m Trace
traceSpanStart (enable, extraInfo) name addr args bTraced = do
  let
    msg = pack $ printf "%s, at:%s" name addr
    bTracedInfo = if extraInfo then bTraced else object []
    argsInfo = if extraInfo then args else Nothing
  tr <- newTrace
  let
    timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
    st =
      toStrict
        ( encodeToLazyText
            ( ChromeStartTrace msg timeInMicros (ChromeStartTraceArgs (traceID tr) addr bTracedInfo argsInfo)
            )
        )

  dumpTrace enable st
  return tr

traceSpanExec ::
  (MonadState s m, HasTrace s, MonadIO m) =>
  (Bool, Bool) ->
  T.Text ->
  T.Text ->
  (a -> m Value) ->
  m (a, Value) ->
  m a
traceSpanExec (enable, extraInfo) name addr g f = do
  let msg = pack $ printf "%s, at:%s" name addr
  (res, focus) <- f
  tr <- newTrace
  let
    timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
    focusInfo = if extraInfo then focus else object []
  tracedInfo <- if extraInfo then g res else return $ object []
  dumpTrace enable $
    toStrict
      ( encodeToLazyText
          ( ChromeEndTrace msg timeInMicros (ChromeEndTraceArgs tracedInfo focusInfo)
          )
      )
  return res

debugInstant ::
  (MonadState s m, HasTrace s, MonadIO m) => (Bool, Bool) -> T.Text -> T.Text -> Maybe Value -> m ()
debugInstant (enable, extraInfo) name addr args = do
  start <- lastTraceID
  tr <- gets getTrace
  let msg = pack $ printf "%s, at:%s" name addr
      timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
      argsInfo = if extraInfo then args else Nothing
  dumpTrace enable $
    toStrict
      ( encodeToLazyText
          ( ChromeInstantTrace msg timeInMicros (ChromeInstantTraceArgs start addr argsInfo)
          )
      )

dumpTrace :: (MonadIO m) => Bool -> T.Text -> m ()
dumpTrace enable msg = when enable $ liftIO $ hPutStr stderr $ printf "ChromeTrace%s\n" msg

getTraceID :: (MonadState s m, HasTrace s) => m Int
getTraceID = gets $ traceID . getTrace

newTrace :: (MonadState s m, HasTrace s, MonadIO m) => m Trace
newTrace = do
  tr <- gets getTrace
  currentTime <- liftIO getCurrentTime
  let ntr = Trace{traceTime = currentTime, traceID = traceID tr + 1}
  modify' $ \s -> setTrace s ntr
  return ntr

lastTraceID :: (MonadState s m, HasTrace s) => m Int
lastTraceID = do
  tr <- gets getTrace
  return $ traceID tr

emptyTrace :: Trace
emptyTrace =
  Trace
    { traceID = 0
    , traceTime = UTCTime{utctDayTime = secondsToDiffTime 0, utctDay = fromGregorian 1970 1 1}
    }