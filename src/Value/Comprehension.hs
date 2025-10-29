{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Comprehension where

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import StringIndex (TextIndex)
import {-# SOURCE #-} Value.Tree

data Comprehension = Comprehension
  { isListCompreh :: !Bool
  , args :: Seq.Seq ComprehArg
  , iterBindings :: Map.Map TextIndex Tree
  -- ^ Temporary iteration bindings for the comprehension so far.
  }
  deriving (Generic)

data ComprehArg
  = ComprehArgLet TextIndex Tree
  | ComprehArgIf Tree
  | ComprehArgFor TextIndex (Maybe TextIndex) Tree
  | ComprehArgStructTmpl Tree
  deriving (Generic)

mkComprehension :: Bool -> [ComprehArg] -> Tree -> Comprehension
mkComprehension isListCompreh clauses sv =
  Comprehension
    { isListCompreh = isListCompreh
    , args = Seq.fromList (clauses ++ [ComprehArgStructTmpl sv])
    , iterBindings = Map.empty
    }

getValFromIterClause :: ComprehArg -> Tree
getValFromIterClause (ComprehArgLet _ v) = v
getValFromIterClause (ComprehArgIf v) = v
getValFromIterClause (ComprehArgFor _ _ v) = v
getValFromIterClause (ComprehArgStructTmpl v) = v

setValInIterClause :: Tree -> ComprehArg -> ComprehArg
setValInIterClause v (ComprehArgLet n _) = ComprehArgLet n v
setValInIterClause v (ComprehArgIf _) = ComprehArgIf v
setValInIterClause v (ComprehArgFor n m _) = ComprehArgFor n m v
setValInIterClause v (ComprehArgStructTmpl _) = ComprehArgStructTmpl v
