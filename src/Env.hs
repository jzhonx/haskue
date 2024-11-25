{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Env where

import Control.Monad.Except (MonadError)
import Control.Monad.Logger (MonadLogger)
import GHC.Stack (HasCallStack)

type Env m = (MonadError String m, MonadLogger m, HasCallStack)
