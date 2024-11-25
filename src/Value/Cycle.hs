module Value.Cycle where

import Class
import Error
import Path

data RefCycle
  = -- The flag indicates whether the cycle is self-reference.
    RefCycle Bool
  | --  RefCycleTail is only used to facilitate the cycle detection.
    -- The first element in the tuple is the absolute path of the cycle head, the second element is the relative path of
    -- the cycle tail.
    -- It is always reducible.
    RefCycleTail (Path, Path)
  deriving (Show)

instance Eq RefCycle where
  (==) (RefCycle p1) (RefCycle p2) = p1 == p2
  (==) (RefCycleTail p1) (RefCycleTail p2) = p1 == p2
  (==) _ _ = False

instance BuildASTExpr RefCycle where
  -- The tree should use the original expression instead.
  buildASTExpr _ _ = throwErrSt "RefCycle should not be used in the AST"
