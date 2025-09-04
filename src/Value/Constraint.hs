{-# LANGUAGE DeriveGeneric #-}

module Value.Constraint where

import GHC.Generics (Generic)
import Value.Atom (Atom)
import {-# SOURCE #-} Value.Tree

data AtomCnstr = AtomCnstr
  { value :: Atom
  -- ^ cnsAtom is the atom of the constraint. Any operation that changes the constraint should update this atom.
  , cnsValidator :: Tree
  -- ^ validator is used when validateCnstrs is called. It is the unification operation node.
  }
  deriving (Generic)

updateCnstrAtom :: Atom -> AtomCnstr -> AtomCnstr
updateCnstrAtom atom c = c{value = atom}
