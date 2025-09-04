{-# LANGUAGE FlexibleContexts #-}

module Reduce.Root where

import Reduce.RMonad
import Value

reduce :: (ReduceMonad s r m) => m ()
reduceToNonMut :: (ReduceMonad r s m) => m ()
handleRefRes :: (ReduceMonad s r m) => Bool -> Maybe Tree -> m ()
reducePureTN :: (ReduceMonad s r m) => m ()