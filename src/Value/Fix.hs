{-# LANGUAGE DeriveGeneric #-}

module Value.Fix where

import Feature (TreeAddr)
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree (Tree, TreeNode)

{- | Fix is used to represent unify operation that has references that reference its fields as its conjuncts.

Conjuncts can be reference cycles and comprehensions that reference its parent fields.
-}
data Fix = Fix
  { val :: TreeNode
  , conjs :: [FixConj]
  , unknownExists :: Bool
  -- ^ Indicates whether there exists unknown (noval) nodes that are represented by the TreeAddrs.
  }
  deriving (Generic)

data FixConj = FixSelect TreeAddr | FixCompreh Tree
  deriving (Generic)
