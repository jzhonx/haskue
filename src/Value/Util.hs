module Value.Util where

import Control.Monad.Logger (
  MonadLogger,
  logDebugN,
 )
import Data.Text (pack)

dump :: (MonadLogger m) => String -> m ()
dump = logDebugN . pack
