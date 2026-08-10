{-# LANGUAGE FlexibleContexts #-}

module Reduce.Core where

import Feature (EvalAddr)
import Reduce.Monad
import Value.Val (VNode, Val)

reduce :: EvalAddr -> VNode -> RM VNode
reduceVal :: EvalAddr -> Val -> RM Val
reduceConstraintsInCnstrs :: EvalAddr -> VNode -> RM VNode
signalReduced :: EvalAddr -> RM ()
