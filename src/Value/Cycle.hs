module Value.Cycle where

import Common (BuildASTExpr (..))
import Exception (throwErrSt)
import Path (TreeAddr)

{- | A reference cycle occurs if a field references itself, either directly or indirectly.


It should only be created after deref function call because if there exists a self cycle, and deref returns
the cycle head, then notify will notify nodes in the reverse order of the cycle.
-}
newtype RefCycle
  = -- | The address must be absolute address.
    -- Consider the case:
    -- {a: b + 100, b: a - 100} & {}
    -- a and b in the first argument are not referable.
    RefCycle TreeAddr
  deriving (Show)

instance Eq RefCycle where
  (==) (RefCycle p1) (RefCycle p2) = p1 == p2

instance BuildASTExpr RefCycle where
  -- The tree should use the original expression instead.
  buildASTExpr _ _ = throwErrSt "RefCycle should not be used in the AST"
