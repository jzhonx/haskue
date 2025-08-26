{-# LANGUAGE FlexibleContexts #-}

module Reduce.Nodes where

import qualified Common
import Cursor
import Value

normalizeDisj :: (Common.EnvIO r s m) => Disj -> TrCur -> m Tree