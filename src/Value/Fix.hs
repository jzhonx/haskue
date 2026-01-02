{-# LANGUAGE DeriveGeneric #-}

module Value.Fix where

import Feature (ValAddr)
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Val (Val, ValNode)

{- | Fix is used to represent unify operation that has references that reference its fields as its conjuncts.

Conjuncts can be reference cycles and comprehensions that reference its parent fields.
-}
data Fix = Fix
  { val :: ValNode
  , conjs :: [FixConj]
  , unknownExists :: Bool
  -- ^ Indicates whether there exists unknown (noval) nodes that are represented by the ValAddrs.
  }
  deriving (Generic)

data FixConj = FixSelect ValAddr | FixCompreh Val
  deriving (Generic)
