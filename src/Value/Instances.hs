{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Instances where

import Control.DeepSeq (NFData (..))
import Data.Aeson (ToJSON (..))
import Data.Maybe (fromJust, isNothing)
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (..))
import Value.Comprehension
import Value.Constraint
import Value.Disj
import Value.DisjoinOp
import Value.Fix
import Value.Interpolation
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.Tree
import Value.UnifyOp

-----
-- Eq
-----

deriving instance Eq Comprehension
deriving instance Eq ComprehArg

deriving instance Eq Reference
deriving instance Eq RefArg

deriving instance Eq Interpolation

deriving instance Eq DisjoinOp
deriving instance Eq DisjTerm

deriving instance Eq UnifyOp

deriving instance Eq SOp
deriving instance Eq Op
deriving instance Eq OpFrame
deriving instance Eq RegularOp

instance Eq Struct where
  (==) s1 s2 = stcFields s1 == stcFields s2 && stcClosed s1 == stcClosed s2 && stcIsConcrete s1 == stcIsConcrete s2

instance Eq Field where
  (==) f1 f2 = f1.ssfValue == f2.ssfValue && f1.ssfAttr == f2.ssfAttr

deriving instance Eq DynamicField
deriving instance Eq StructCnstr

deriving instance Eq List
deriving instance Eq Disj
deriving instance Eq AtomCnstr
deriving instance Eq Binding
deriving instance Eq Fix
deriving instance Eq FixConj

instance Eq TreeNode where
  (==) (TNStruct s1) (TNStruct s2) = s1 == s2
  (==) (TNList ts1) (TNList ts2) = ts1 == ts2
  (==) (TNDisj d1) (TNDisj d2) = d1 == d2
  (==) (TNAtom l1) (TNAtom l2) = l1 == l2
  (==) (TNAtomCnstr c1) (TNAtomCnstr c2) = c1 == c2
  (==) (TNDisj dj1) n2@(TNAtom _) =
    if isNothing (rtrDisjDefVal dj1)
      then False
      else treeNode (fromJust $ rtrDisjDefVal dj1) == n2
  (==) (TNAtom a1) (TNDisj dj2) = (==) (TNDisj dj2) (TNAtom a1)
  (==) (TNBounds b1) (TNBounds b2) = b1 == b2
  (==) (TNBottom _) (TNBottom _) = True
  (==) TNTop TNTop = True
  -- Only compare the TreeNode part of Fix.
  (==) (TNFix r1) (TNFix r2) = r1.val == r2.val
  (==) TNNoVal TNNoVal = True
  (==) _ _ = False

instance Eq Tree where
  (==) t1 t2 = treeNode t1 == treeNode t2

-----
-- Show
-----

deriving instance Show Comprehension
deriving instance Show ComprehArg

deriving instance Show Reference
instance Show RefArg where
  show (RefPath s _) = "ref_v_" ++ show s
  show (RefIndex _) = "index"

deriving instance Show Interpolation

deriving instance Show DisjoinOp
deriving instance Show DisjTerm

deriving instance Show UnifyOp

deriving instance Show SOp
deriving instance Show Op
deriving instance Show OpFrame
deriving instance Show RegularOp

deriving instance Show Struct
deriving instance Show Field
deriving instance Show DynamicField
deriving instance Show StructCnstr

deriving instance Show Binding
deriving instance Show List
deriving instance Show Disj
deriving instance Show AtomCnstr
deriving instance Show Fix
deriving instance Show FixConj

instance ShowWTIndexer FixConj where
  tshow (FixSelect addr) = tshow addr
  tshow (FixCompreh t) = tshow t

deriving instance Show TreeNode
deriving instance Show Tree

instance ShowWTIndexer Tree where
  tshow = oneLinerStringOfTree

instance ToJSON Tree where
  toJSON t = toJSON (show t)

instance ToJSONWTIndexer Tree where
  ttoJSON t = do
    s <- oneLinerStringOfTree t
    return $ toJSON s

-----
-- NFData
-----

deriving instance NFData Comprehension
deriving instance NFData ComprehArg

deriving instance NFData Reference
deriving instance NFData RefArg

deriving instance NFData Interpolation

deriving instance NFData DisjoinOp
deriving instance NFData DisjTerm

deriving instance NFData UnifyOp

deriving instance NFData SOp
deriving instance NFData Op
deriving instance NFData OpFrame
deriving instance NFData RegularOp

deriving instance NFData Struct
deriving instance NFData Field
deriving instance NFData DynamicField
deriving instance NFData StructCnstr

deriving instance NFData Binding
deriving instance NFData List
deriving instance NFData Disj
deriving instance NFData AtomCnstr
deriving instance NFData Fix
deriving instance NFData FixConj

deriving instance NFData TreeNode
deriving instance NFData EmbedType
deriving instance NFData Tree