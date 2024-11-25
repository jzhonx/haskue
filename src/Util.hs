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
  modify $ \s -> setTrace s (tr{traceStack = traceID tr : traceStack tr, traceID = traceID tr + 1})
  logDebugStr $ printf "%s, begin, %s" (show tr) msg

  res <- f

  logDebugStr $ printf "%s, _ends, %s, result: %s" (show tr) msg (show res)
  tr2 <- gets getTrace
  modify $ \s -> setTrace s (tr2{traceStack = tail $ traceStack tr2})
  return res

emptyTrace :: Trace
emptyTrace = Trace 0 []

logDebugStr :: (MonadLogger m) => String -> m ()
logDebugStr = logDebugN . pack
