module Value.Cycle where

import Control.Monad.Except (throwError)
import Path
import Value.Class

data RefCycle
  = RefCycle Path
  | RefCycleTail
  deriving (Show)

instance Eq RefCycle where
  (==) (RefCycle _) (RefCycle _) = True
  (==) RefCycleTail RefCycleTail = True
  (==) _ _ = False

instance BuildASTExpr RefCycle where
  buildASTExpr _ _ = throwError "RefCycle should not be used in the AST"
