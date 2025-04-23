module Value.UnifyOp where

import qualified AST
import Common (BuildASTExpr (..), Env)
import Control.Monad (foldM, when)
import Exception (throwErrSt)

{- | UnifyOp is commutative, associative, and idempotent.

The op tree can be flattened to a list of conjuncts.

It is used to handle reference unifications, so that when values of references change, the new unification can be
created correctly.
-}
data UnifyOp t = UnifyOp
  { ufConjuncts :: [t]
  , ufValue :: Maybe t
  }
  deriving (Eq, Show)

instance (BuildASTExpr t) => BuildASTExpr (UnifyOp t) where
  buildASTExpr c op = do
    when (length (ufConjuncts op) < 2) $
      throwErrSt "Conjuncts should be at least 2"

    leftMost <- buildASTExpr c (head (ufConjuncts op))
    foldM
      ( \acc x -> do
          right <- buildASTExpr c x
          return $ AST.ExprBinaryOp AST.Unify acc right
      )
      leftMost
      (tail (ufConjuncts op))