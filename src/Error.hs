{-# LANGUAGE FlexibleContexts #-}

module Error where

import Control.Monad.Except (MonadError, throwError)
import GHC.Stack (HasCallStack, callStack, prettyCallStack)

throwErrSt :: (MonadError String m, HasCallStack) => String -> m a
throwErrSt msg = throwError $ "Internal bug: " ++ msg ++ "\n" ++ prettyCallStack callStack
