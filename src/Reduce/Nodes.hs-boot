{-# LANGUAGE FlexibleContexts #-}

module Reduce.Nodes where

import qualified Common
import Value

normalizeDisj :: (Common.Env r s m) => Disj -> m Tree