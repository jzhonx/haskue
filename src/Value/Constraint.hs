{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.Constraint where

import qualified AST
import Control.DeepSeq (NFData (..))
import GHC.Generics (Generic)
import Value.Atom (Atom)
import {-# SOURCE #-} Value.Tree

data AtomCnstr = AtomCnstr
  { cnsAtom :: Atom
  -- ^ cnsAtom is the atom of the constraint. Any operation that changes the constraint should update this atom.
  , cnsValidator :: AST.Expression
  -- ^ validator is used when validateCnstrs is called. It is the unification operation node.
  -- The reason for using AST.Expression instead of value is that the tree could be reduced by RefCycleTail.
  -- Consider the case, {a: (a + 1) & 200}. If a+1 is reduced first, then the "a" becomes a RCTail, which will be
  -- reduced to atom with 200. Then the validator would be incorrectly set to RCTail. The original expr of the (a+1) is
  -- the correct validator.
  }
  deriving (Eq, Generic, NFData)

updateCnstrAtom :: Atom -> AtomCnstr -> AtomCnstr
updateCnstrAtom atom c = c{cnsAtom = atom}

{- | CnstredVal is a value that is either a constraint's value or a unification that contains the constraint's value.

It is a wrapper so that when a value is unified with a temporary constraint's value and the result is a bottom, the
whole value will not be a permanent bottom.
-}
data CnstredVal = CnstredVal
  { cnsedVal :: Tree
  , cnsedOrigExpr :: Maybe AST.Expression
  -- ^ cnsedOrigExpr is the original expression without constraints. It is used for showing the original expression
  -- without constraints applied.
  }
  deriving (Generic)
