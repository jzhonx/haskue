module Util where

import Control.Monad.Logger (
  MonadLogger,
  logDebugN,
 )
import Control.Monad.State (MonadState, gets, modify)
import Data.Text (pack)
import Text.Printf (printf)

class HasTrace a where
  getTrace :: a -> Trace
  setTrace :: a -> Trace -> a

data Trace = Trace
  { traceID :: Int
  , traceStack :: [Int]
  }
  deriving (Eq)

instance Show Trace where
  show t = printf "id=%s, stack=%s" (show $ traceID t) (show $ traceStack t)

debugSpan :: (MonadState s m, MonadLogger m, HasTrace s, Show a) => String -> m a -> m a
debugSpan msg f = do
  tr <- gets getTrace
  let ntr = tr{traceID = traceID tr + 1}
  logDebugStr $ printf "%s, begin, %s" (show ntr) msg
  modify $ \s -> setTrace s (ntr{traceStack = traceID ntr : traceStack ntr})

  res <- f

  logDebugStr $ printf "%s, _ends, %s, result: %s" (show ntr) msg (show res)
  closeTR <- gets getTrace
  modify $ \s -> setTrace s (closeTR{traceStack = tail $ traceStack closeTR})
  return res

getTraceID :: (MonadState s m, HasTrace s) => m Int
getTraceID = gets $ traceID . getTrace

emptyTrace :: Trace
emptyTrace = Trace 0 []

logDebugStr :: (MonadLogger m) => String -> m ()
logDebugStr = logDebugN . pack
