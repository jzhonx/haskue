{-# LANGUAGE FlexibleContexts #-}

module Reduce.Root where

import Reduce.RMonad
import Value

reduce :: RM ()
reducePureFocus :: RM ()
reduceToNonMut :: RM ()
reducePureTN :: RM ()