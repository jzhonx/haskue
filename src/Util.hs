{-# LANGUAGE OverloadedStrings #-}

module Util where

import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, gets, modify)
import Data.Aeson (ToJSON, Value, object, toJSON, (.=))
import Data.Aeson.Text (encodeToLazyText)
import Data.Maybe (fromJust, isNothing)
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
  , cstaBeforeFocus :: Value
  , cstaCustomVal :: Maybe Value
  }
  deriving (Eq, Show)

data ChromeEndTraceArgs = ChromeEndTraceArgs
  { cetaResVal :: String
  , cetaFocus :: Value
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
  , ctiCustomVal :: Maybe Value
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
  (MonadState s m, MonadIO m, HasTrace s, Show a) =>
  Bool ->
  String ->
  String ->
  Maybe Value ->
  Value ->
  m (a, Value) ->
  m a
debugSpan enable name addr args bTraced f = do
  _ <- debugSpanStart enable name addr args bTraced
  debugSpanExec enable name addr f

debugSpanStart ::
  (MonadState s m, HasTrace s, MonadIO m) =>
  Bool ->
  String ->
  String ->
  Maybe Value ->
  Value ->
  m Trace
debugSpanStart enable name addr args bTraced = do
  let msg = printf "%s, at:%s" name addr
  tr <- newTrace
  let timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  dumpTrace enable $
    unpack
      ( encodeToLazyText
          ( ChromeStartTrace msg timeInMicros (ChromeStartTraceArgs (traceID tr) addr bTraced args)
          )
      )
  return tr

debugSpanExec ::
  (MonadState s m, HasTrace s, MonadIO m, Show a) =>
  Bool ->
  String ->
  String ->
  m (a, Value) ->
  m a
debugSpanExec enable name addr f = do
  let msg = printf "%s, at:%s" name addr
  (res, focus) <- f
  tr <- newTrace
  let timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  dumpTrace enable $
    unpack
      ( encodeToLazyText
          ( ChromeEndTrace msg timeInMicros (ChromeEndTraceArgs (show res) focus)
          )
      )
  return res

debugInstant ::
  (MonadState s m, HasTrace s, MonadIO m) => Bool -> String -> String -> Maybe Value -> m ()
debugInstant enable name addr args = do
  start <- lastTraceID
  tr <- gets getTrace
  let msg = printf "%s, at:%s" name addr
  let timeInMicros = round (utcTimeToPOSIXSeconds (traceTime tr) * 1000000) :: Int
  dumpTrace enable $
    unpack
      ( encodeToLazyText
          ( ChromeInstantTrace msg timeInMicros (ChromeInstantTraceArgs start addr args)
          )
      )

dumpTrace :: (MonadIO m) => Bool -> String -> m ()
dumpTrace enable msg =
  when enable $ liftIO $ putStrLn $ "ChromeTrace" ++ msg

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

emptyTrace :: Trace
emptyTrace = Trace{traceID = 0, traceTime = UTCTime{utctDayTime = secondsToDiffTime 0, utctDay = fromGregorian 1970 1 1}}