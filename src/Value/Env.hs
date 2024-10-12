{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Env where

import Control.Monad.Except (MonadError)
import Control.Monad.Logger (MonadLogger)
import Control.Monad.Reader (MonadReader)

type Env m c = (MonadError String m, MonadLogger m, MonadReader c m)
