{-# LANGUAGE FlexibleContexts #-}

module Reduce.Core where

import Feature (ValAddr)
import Reduce.Monad
import Value.Val (VNode, Val)

reduce :: ValAddr -> VNode -> RM VNode
reduceVal :: ValAddr -> Val -> RM Val
reduceConstraintsInCnstrs :: ValAddr -> VNode -> RM VNode
signalReduced :: ValAddr -> RM ()