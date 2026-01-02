{-# LANGUAGE FlexibleContexts #-}

module Reduce.Root where

import Reduce.RMonad

reduce :: RM ()
reducePureFocus :: RM ()
reduceToNonMut :: RM ()
reducePureVN :: RM ()