{-# LANGUAGE DeriveFunctor #-}

module Value.Comprehension where

import qualified AST
import Common (BuildASTExpr (..))

data Comprehension t = Comprehension
  { cphStart :: t
  , cphIterClauses :: [IterClause t]
  , cphStruct :: t
  , cphValue :: Maybe t
  }
  deriving (Eq, Show)

-- instance BuildASTExpr (Comprehension t) where
--   buildASTExpr c t =

data IterClause t = IterClauseLet String t | IterClauseIf t
  deriving (Eq, Show, Functor)

mkComprehension :: t -> [IterClause t] -> t -> Comprehension t
mkComprehension start clauses sv =
  Comprehension
    { cphStart = start
    , cphIterClauses = clauses
    , cphStruct = sv
    , cphValue = Nothing
    }

getValFromIterClause :: IterClause t -> t
getValFromIterClause (IterClauseLet _ v) = v
getValFromIterClause (IterClauseIf v) = v
