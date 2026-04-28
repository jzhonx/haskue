{-# LANGUAGE FlexibleContexts #-}

module Reduce.Core where

import Feature (ValAddr)
import Reduce.Monad
import Value.Val (VNode, Val)

reduce :: ValAddr -> VNode -> RM VNode
reduceWithInitVN :: ValAddr -> Val -> VNode -> RM VNode
reduceVN :: ValAddr -> Val -> RM Val
reduceOpOnce :: Bool -> Val -> ValAddr -> VNode -> RM VNode
signalReduced :: ValAddr -> RM ()
signalNeedRecalc :: ValAddr -> RM ()