{-# LANGUAGE FlexibleContexts #-}

module Reduce.Core where

import EvalAddr (EvalAddr)
import Reduce.Monad
import Value.Val (VNode, Val)

reduce :: EvalAddr -> VNode -> RM VNode
reduceVal :: EvalAddr -> Val -> RM Val
reduceConstraintPass :: EvalAddr -> VNode -> RM VNode
signalReduced :: EvalAddr -> Bool -> RM ()
