{-# LANGUAGE FlexibleContexts #-}

module Reduce.Root where

import Cursor
import Reduce.RMonad
import Value

reduce :: (ReduceMonad s r m) => TrCur -> m Tree
reduceUnifyConj :: (ReduceMonad s r m) => TrCur -> m (Maybe Tree)
