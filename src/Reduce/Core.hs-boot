{-# LANGUAGE FlexibleContexts #-}

module Reduce.Core where

import Reduce.Monad

reduce :: RM ()
reducePureFocus :: RM ()
reduceToNonMut :: RM ()
reducePureVN :: RM ()