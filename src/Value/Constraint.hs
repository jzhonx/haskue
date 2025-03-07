module Value.Constraint where

import qualified AST
import Value.Atom

data AtomCnstr t = AtomCnstr
  { cnsAtom :: AtomV
  -- ^ cnsAtom is the atom of the constraint. Any operation that changes the constraint should update this atom.
  , cnsOrigAtom :: AtomV
  -- ^ cnsOrigAtom is the original atom when the constraint was created.
  -- It should only be used in validating the constraint.
  , cnsValidator :: AST.Expression
  -- ^ validator is used when validateCnstrs is called. It is the unification operation node.
  -- The reason for using AST.Expression instead of value is that the tree could be reduced by RefCycleTail.
  -- Consider the case, {a: (a + 1) & 200}. If a+1 is reduced first, then the "a" becomes a RCTail, which will be
  -- reduced to atom with 200. Then the validator would be incorrectly set to RCTail. The original expr of the (a+1) is
  -- the correct validator.
  }

instance (Eq t) => Eq (AtomCnstr t) where
  (==) (AtomCnstr a1 o1 v1) (AtomCnstr a2 o2 v2) = a1 == a2 && v1 == v2 && o1 == o2

updateCnstrAtom :: AtomV -> AtomCnstr t -> AtomCnstr t
updateCnstrAtom atom c = c{cnsAtom = atom}

-- | CnstredVal is a value that is either a constraint's value or a unification that contains the constraint's value.
data CnstredVal t = CnstredVal
  { cnsedVal :: t
  , cnsedOrigExpr :: Maybe AST.Expression
  -- ^ cnsedOrigExpr is the original expression without constraints.
  }
  deriving (Eq, Show)
