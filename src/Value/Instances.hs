{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Instances where

import Control.DeepSeq (NFData (..))
import Data.Maybe (fromJust, isNothing)
import Value.Comprehension
import Value.Disj
import Value.DisjoinOp
import Value.Interpolation
import Value.List
import Value.Mutable
import Value.Reference
import Value.Struct
import Value.Tree
import Value.UnifyOp

-----
-- Eq
-----

deriving instance Eq Comprehension
deriving instance Eq IterClause
deriving instance Eq ComprehIterBinding

deriving instance Eq Reference
deriving instance Eq RefArg

deriving instance Eq Interpolation

deriving instance Eq DisjoinOp
deriving instance Eq DisjTerm

deriving instance Eq UnifyOp

deriving instance Eq Mutable
deriving instance Eq MutOp
deriving instance Eq MutFrame
deriving instance Eq RegularOp

deriving instance Eq Block
deriving instance Eq Struct
deriving instance Eq Field
deriving instance Eq LetBinding
deriving instance Eq DynamicField
deriving instance Eq StructCnstr
deriving instance Eq Embedding
deriving instance Eq BlockElemAdder

deriving instance Eq List

deriving instance Eq Disj

instance Eq TreeNode where
  (==) (TNBlock s1) (TNBlock s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNAtom l1) (TNAtom l2) = l1 == l2
  (==) (TNAtomCnstr c1) (TNAtomCnstr c2) = c1 == c2
  (==) (TNDisj dj1) n2@(TNAtom _) =
    if isNothing (dsjDefault dj1)
      then False
      else treeNode (fromJust $ dsjDefault dj1) == n2
  (==) (TNAtom a1) (TNDisj dj2) = (==) (TNDisj dj2) (TNAtom a1)
  (==) (TNMutable f1) (TNMutable f2) = f1 == f2
  (==) (TNBounds b1) (TNBounds b2) = b1 == b2
  (==) (TNBottom _) (TNBottom _) = True
  (==) TNTop TNTop = True
  (==) (TNRefCycle a1) (TNRefCycle a2) = a1 == a2
  (==) _ _ = False

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

-----
-- Show
-----

deriving instance Show Comprehension
deriving instance Show IterClause
deriving instance Show ComprehIterBinding

deriving instance Show Reference
instance Show RefArg where
  show (RefPath s _) = "ref_v_" ++ show s
  show (RefIndex _) = "index"

deriving instance Show Interpolation

deriving instance Show DisjoinOp
deriving instance Show DisjTerm

deriving instance Show UnifyOp

deriving instance Show Mutable
deriving instance Show MutOp
deriving instance Show MutFrame
deriving instance Show RegularOp

deriving instance Show Block
deriving instance Show Struct
deriving instance Show Field
deriving instance Show LetBinding
deriving instance Show DynamicField
deriving instance Show StructCnstr
deriving instance Show Embedding
deriving instance Show BlockElemAdder

deriving instance Show List

deriving instance Show Disj

-----
-- NFData
-----

deriving instance NFData Comprehension
deriving instance NFData IterClause
deriving instance NFData ComprehIterBinding

deriving instance NFData Reference
deriving instance NFData RefArg

deriving instance NFData Interpolation

deriving instance NFData DisjoinOp
deriving instance NFData DisjTerm

deriving instance NFData UnifyOp

deriving instance NFData Mutable
deriving instance NFData MutOp
deriving instance NFData MutFrame
deriving instance NFData RegularOp

deriving instance NFData Block
deriving instance NFData Struct
deriving instance NFData Field
deriving instance NFData LetBinding
deriving instance NFData DynamicField
deriving instance NFData StructCnstr
deriving instance NFData Embedding

deriving instance NFData List

deriving instance NFData Disj

deriving instance NFData TreeNode
deriving instance NFData Tree