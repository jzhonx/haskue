{-# LANGUAGE FlexibleContexts #-}

module Reduce.Core where

import Feature (ValAddr)
import Reduce.Monad
import Value.Op (SOp)
import Value.Val (Val)

reduce :: ValAddr -> Val -> RM Val
reducePure :: ValAddr -> Val -> RM Val
forceReduceMut :: Bool -> ValAddr -> Val -> RM Val
reducePureVN :: ValAddr -> Val -> RM Val
handleMutRes :: Maybe Val -> Bool -> SOp -> ValAddr -> Val -> RM Val
signalReduced :: ValAddr -> RM ()
signalNeedRecalc :: ValAddr -> RM ()