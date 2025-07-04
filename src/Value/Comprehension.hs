{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Comprehension where

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

data Comprehension = Comprehension
  { cphIsListCompreh :: !Bool
  , cphClauses :: Seq.Seq ComprehClause
  , cphIterBindings :: Map.Map T.Text Tree
  -- ^ Temporary iteration bindings for the comprehension so far.
  , cphBlock :: Tree
  }
  deriving (Generic)

data ComprehClause
  = ComprehClauseLet T.Text Tree
  | ComprehClauseIf Tree
  | ComprehClauseFor T.Text (Maybe T.Text) Tree
  deriving (Generic)

mkComprehension :: Bool -> [ComprehClause] -> Tree -> Comprehension
mkComprehension isListCompreh clauses sv =
  Comprehension
    { cphIsListCompreh = isListCompreh
    , cphClauses = Seq.fromList clauses
    , cphIterBindings = Map.empty
    , cphBlock = sv
    }

getValFromIterClause :: ComprehClause -> Tree
getValFromIterClause (ComprehClauseLet _ v) = v
getValFromIterClause (ComprehClauseIf v) = v
getValFromIterClause (ComprehClauseFor _ _ v) = v

setValInIterClause :: Tree -> ComprehClause -> ComprehClause
setValInIterClause v (ComprehClauseLet n _) = ComprehClauseLet n v
setValInIterClause v (ComprehClauseIf _) = ComprehClauseIf v
setValInIterClause v (ComprehClauseFor n m _) = ComprehClauseFor n m v
