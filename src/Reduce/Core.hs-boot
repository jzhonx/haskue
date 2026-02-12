{-# LANGUAGE FlexibleContexts #-}

module Reduce.Core where

import Reduce.Monad

reduce :: RM ()
reducePureFocus :: RM ()
forceReduceMut :: RM ()
reducePureVN :: RM ()
pushCurValToRootQ :: RM ()