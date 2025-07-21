{-# LANGUAGE FlexibleContexts #-}

module Reduce.Root where

import Cursor
import Path
import Reduce.RMonad
import Value

data ResolvedPConjuncts

reduce :: (ReduceMonad s r m) => m ()
reduceRefCycles :: (ReduceMonad s r m) => [TreeAddr] -> m ()
discoverPConjs :: (ReduceMonad s r m) => m [Maybe TrCur]
handleRefRes :: (ReduceMonad s r m) => Bool -> Maybe Tree -> m ()
resolvePendingConjuncts :: (ResolveMonad s r m) => [Maybe TrCur] -> TrCur -> m ResolvedPConjuncts
handleResolvedPConjsForStruct :: (ResolveMonad s r m) => ResolvedPConjuncts -> TrCur -> m (Maybe Tree)
