{-# LANGUAGE OverloadedStrings #-}

module Util where

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
import Text.Printf (printf)

class HasTrace a where
  getTrace :: a -> Trace
  setTrace :: a -> Trace -> a

newtype Trace = Trace
  { traceStamp :: Int
  }
  deriving (Eq)

instance Show Trace where
  show t = printf "id=%s" (show $ traceStamp t)

instance HasTrace Trace where
  getTrace = id
  setTrace s t = t{traceStamp = traceStamp s}

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
  , cstaCustomVal :: Maybe String
  }
  deriving (Eq, Show)

data ChromeEndTraceArgs = ChromeEndTraceArgs
  { cetaResVal :: String
  , cetaFocus :: String
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
  (MonadState s m, MonadLogger m, HasTrace s, Show a, Show b) => String -> String -> Maybe String -> b -> m (a, b) -> m a
debugSpan name addr args bTraced f = do
  start <- debugSpanStart name addr args bTraced
  debugSpanExec start name addr f

debugSpanStart ::
  (MonadState s m, MonadLogger m, HasTrace s, Show a) => String -> String -> Maybe String -> a -> m Int
debugSpanStart name addr args bTraced = do
  let msg = printf "%s, at:%s" name addr
  start <- newTraceStamp 1
  logDebugStr $
    "ChromeTrace"
      ++ unpack
        ( encodeToLazyText
            ( ChromeStartTrace msg start (ChromeStartTraceArgs start addr (show bTraced) args)
            )
        )
  return start

debugSpanExec ::
  (MonadState s m, MonadLogger m, HasTrace s, Show a, Show b) => Int -> String -> String -> m (a, b) -> m a
debugSpanExec start name addr f = do
  let msg = printf "%s, at:%s" name addr
  (res, focus) <- f
  end <- do
    poEnd <- lastTraceStamp
    if poEnd == start
      -- This is the leaf duration. Make sure its duration is not 0.
      then newTraceStamp 5
      else newTraceStamp 1
  logDebugStr $
    "ChromeTrace"
      ++ unpack
        ( encodeToLazyText
            ( ChromeEndTrace msg end (ChromeEndTraceArgs (show res) (show focus))
            )
        )
  return res

debugInstant ::
  (MonadState s m, MonadLogger m, HasTrace s) => String -> String -> Maybe String -> m ()
debugInstant name addr args = do
  start <- lastTraceStamp
  let msg = printf "%s, at:%s" name addr
  logDebugStr $
    "ChromeTrace"
      ++ unpack
        ( encodeToLazyText
            ( ChromeInstantTrace msg start (ChromeInstantTraceArgs start addr args)
            )
        )

getTraceID :: (MonadState s m, HasTrace s) => m Int
getTraceID = gets $ traceStamp . getTrace

newTraceStamp :: (MonadState s m, HasTrace s) => Int -> m Int
newTraceStamp delta = do
  tr <- gets getTrace
  let
    newStamp = traceStamp tr + delta
    ntr = tr{traceStamp = newStamp}
  modify $ \s -> setTrace s ntr
  return newStamp

lastTraceStamp :: (MonadState s m, HasTrace s) => m Int
lastTraceStamp = do
  tr <- gets getTrace
  return $ traceStamp tr

emptyTrace :: Trace
emptyTrace = Trace 0

logDebugStr :: (MonadLogger m) => String -> m ()
logDebugStr = logDebugN . pack
