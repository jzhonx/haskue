module Value.Cycle where

import Class
import Error
import Path

-- RefCycle is the cycle head.
-- The only flag indicates whether the cycle is self-reference.
-- It is not reducible. If field "a" is a RefCyle and field "b" references the field "a", and later "a" is
-- updated to a new value by an evaluated dynamic field, then "b" should be updated to the new value.
-- It should only be created after deref function call because if there exists a self cycle, and deref returns
-- the cycle head, then notify will notify nodes in the reverse order of the cycle.
data RefCycle
  = -- | RefCycleVertMerger is only used to facilitate the cycle detection.
    -- The first element in the tuple is the absolute addr of the cycle head, the second element is the relative addr of
    -- the cycle tail.
    -- It is always reducible. It should be reduced until the cycle head is found.
    RefCycleVertMerger (TreeAddr, TreeAddr)
  | -- | RefCycleVert is a verticle cycle.
    --  In the unification, the original expression should be tried to reduce again.
    RefCycleVert
  | -- | RefCycleHori is a cycle consisting of only reference nodes.
    -- It might contain a loop (cycle with only one node) ref.
    -- The first element should be in the referable form and it is the start of the cycle.
    -- The second element is the end of the cycle.
    RefCycleHori (TreeAddr, TreeAddr)
  deriving (Show)

instance Eq RefCycle where
  (==) (RefCycleVertMerger p1) (RefCycleVertMerger p2) = p1 == p2
  (==) RefCycleVert RefCycleVert = True
  (==) (RefCycleHori _) (RefCycleHori _) = True
  (==) _ _ = False

instance BuildASTExpr RefCycle where
  -- The tree should use the original expression instead.
  buildASTExpr _ _ = throwErrSt "RefCycle should not be used in the AST"
