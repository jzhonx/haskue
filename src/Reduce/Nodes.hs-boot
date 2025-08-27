{-# LANGUAGE FlexibleContexts #-}

module Reduce.Nodes where

import qualified Common
import Cursor
import Reduce.RMonad (ResolveMonad)
import Value

normalizeDisj :: (ResolveMonad r s m) => Disj -> TrCur -> m Tree