module Util where

import Control.Monad.Logger (
  MonadLogger,
  logDebugN,
 )
import Control.Monad.State (MonadState, gets, modify)
import Data.Maybe (fromJust, isNothing)
import Data.Text (pack)
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

data ChromeTrace = ChromeTrace
  { ctrName :: String
  , ctrStart :: Int
  , ctrEnd :: Int
  , ctrArgs :: Maybe String
  }
  deriving (Eq)

instance Show ChromeTrace where
  show ct =
    printf
      "ChromeTrace{%s: %s, %s: %s, %s: %s, \"ph\": \"X\", \"pid\": 0, \"tid\": 0"
      (show "name")
      (show $ ctrName ct)
      (show "ts")
      (show $ ctrStart ct)
      (show "dur")
      (show $ ctrEnd ct - ctrStart ct)
      ++ ( if isNothing (ctrArgs ct)
            then ""
            else printf ", \"args\": {\"data\": %s}" (show (fromJust $ ctrArgs ct))
         )
      ++ "}"

debugSpan :: (MonadState s m, MonadLogger m, HasTrace s) => String -> String -> Maybe String -> m a -> m a
debugSpan name addr args f = do
  start <- newTraceStamp
  res <- f
  end <- newTraceStamp
  let msg = printf "%s, at:%s" name addr
  logDebugStr $ show $ ChromeTrace msg start end args
  return res

getTraceID :: (MonadState s m, HasTrace s) => m Int
getTraceID = gets $ traceStamp . getTrace

newTraceStamp :: (MonadState s m, HasTrace s) => m Int
newTraceStamp = do
  tr <- gets getTrace
  let
    newStamp = traceStamp tr + 1
    ntr = tr{traceStamp = newStamp}
  modify $ \s -> setTrace s ntr
  return newStamp

emptyTrace :: Trace
emptyTrace = Trace 0

logDebugStr :: (MonadLogger m) => String -> m ()
logDebugStr = logDebugN . pack
