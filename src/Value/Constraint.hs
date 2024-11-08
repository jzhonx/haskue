module Value.Constraint where

import Value.Atom

data Constraint t = Constraint
  { -- cnsAtom is the atom of the constraint. Any operation that changes the constraint should update this atom.
    cnsAtom :: AtomV
  , -- cnsOrigAtom is the original atom when the constraint was created.
    -- It should only be used in validating the constraint.
    cnsOrigAtom :: AtomV
  , -- validator is used when validateCnstrs is called. It is the unification operation node.
    cnsValidator :: t
  }

instance (Eq t) => Eq (Constraint t) where
  (==) (Constraint a1 o1 v1) (Constraint a2 o2 v2) = a1 == a2 && v1 == v2 && o1 == o2

updateCnstrAtom :: AtomV -> Constraint t -> Constraint t
updateCnstrAtom atom c = c{cnsAtom = atom}
