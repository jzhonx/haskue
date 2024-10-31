module Util where

import Control.Monad.Logger (
  MonadLogger,
  logDebugN,
 )
import Data.Text (pack)

logDebugStr :: (MonadLogger m) => String -> m ()
logDebugStr = logDebugN . pack

