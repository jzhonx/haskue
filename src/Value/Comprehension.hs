{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Comprehension where

import qualified Data.Text as T
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

data Comprehension = Comprehension
  { cphIsListCompreh :: !Bool
  , cphIterClauses :: [IterClause]
  , cphStruct :: Tree
  , cphIterBindings :: [ComprehIterBinding]
  -- ^ Bindings are temporary on each iteration.
  , cphIterVal :: Maybe Tree
  , cphValue :: Maybe Tree
  }
  deriving (Generic)

data IterClause
  = IterClauseLet T.Text Tree
  | IterClauseIf Tree
  | IterClauseFor T.Text (Maybe T.Text) Tree
  deriving (Generic)

mkComprehension :: Bool -> [IterClause] -> Tree -> Comprehension
mkComprehension isListCompreh clauses sv =
  Comprehension
    { cphIsListCompreh = isListCompreh
    , cphIterClauses = clauses
    , cphStruct = sv
    , cphIterBindings = []
    , cphIterVal = Nothing
    , cphValue = Nothing
    }

getValFromIterClause :: IterClause -> Tree
getValFromIterClause (IterClauseLet _ v) = v
getValFromIterClause (IterClauseIf v) = v
getValFromIterClause (IterClauseFor _ _ v) = v

setValInIterClause :: Tree -> IterClause -> IterClause
setValInIterClause v (IterClauseLet n _) = IterClauseLet n v
setValInIterClause v (IterClauseIf _) = IterClauseIf v
setValInIterClause v (IterClauseFor n m _) = IterClauseFor n m v

data ComprehIterBinding = ComprehIterBinding
  { cphBindName :: T.Text
  , cphBindValue :: Tree
  }
  deriving (Generic)