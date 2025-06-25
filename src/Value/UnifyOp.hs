{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.UnifyOp where

import qualified AST
import Common (BuildASTExpr (..))
import Control.DeepSeq (NFData (..))
import Control.Monad (foldM)
import qualified Data.Sequence as Seq
import Exception (throwErrSt)
import GHC.Generics (Generic)

{- | UnifyOp is commutative, associative, and idempotent.

The op tree can be flattened to a list of conjuncts.

It is used to handle reference unifications, so that when values of references change, the new unification can be
created correctly.
-}
data UnifyOp t = UnifyOp
  { ufConjuncts :: Seq.Seq t
  , ufValue :: Maybe t
  }
  deriving (Eq, Show, Generic, NFData)

instance (BuildASTExpr t) => BuildASTExpr (UnifyOp t) where
  buildASTExpr c op
    | fstConj Seq.:<| rest <- ufConjuncts op
    , -- The rest should be a non-empty sequence.
      _ Seq.:|> _ <- rest = do
        leftMost <- buildASTExpr c fstConj
        foldM
          ( \acc x -> do
              right <- buildASTExpr c x
              return $ pure $ AST.ExprBinaryOp (pure AST.Unify) acc right
          )
          leftMost
          rest
    | otherwise = throwErrSt "UnifyOp should have at least two conjuncts"

emptyUnifyOp :: UnifyOp t
emptyUnifyOp = UnifyOp Seq.empty Nothing