module Value.Constraint where

import Value.Atom

data Constraint t = Constraint
  { cnsAtom :: AtomV
  , -- validator is used when validateCnstrs is called.
    cnsValidator :: t
  }

instance (Eq t) => Eq (Constraint t) where
  (==) (Constraint a1 v1) (Constraint a2 v2) = a1 == a2 && v1 == v2

updateCnstrAtom :: AtomV -> Constraint t -> Constraint t
updateCnstrAtom atom c = c{cnsAtom = atom}
