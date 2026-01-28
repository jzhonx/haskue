{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Comprehension where

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import StringIndex (TextIndex)
import {-# SOURCE #-} Value.Val

data Comprehension = Comprehension
  { isListCompreh :: !Bool
  , args :: Seq.Seq ComprehArg
  , iterBindings :: Map.Map TextIndex Val
  -- ^ Temporary iteration bindings for the comprehension so far.
  }
  deriving (Generic)

data ComprehArg
  = ComprehArgLet TextIndex Val
  | ComprehArgIf Val
  | ComprehArgFor TextIndex (Maybe TextIndex) Val
  | -- | The template value that will be used to construct iteration value.
    -- The template might be modified during iteration by upper comprehension layer.
    -- For example, the suffix of references in the template might be replaced by unique ids.
    ComprehArgTmpl Val
  | -- | A place for reducing iteration value.
    ComprehArgIterVal Val
  deriving (Generic)

mkComprehension :: Bool -> [ComprehArg] -> Val -> Comprehension
mkComprehension isListCompreh clauses sv =
  Comprehension
    { isListCompreh = isListCompreh
    , args = Seq.fromList (clauses ++ [ComprehArgTmpl sv, ComprehArgIterVal sv])
    , iterBindings = Map.empty
    }

getValFromIterClause :: ComprehArg -> Val
getValFromIterClause (ComprehArgLet _ v) = v
getValFromIterClause (ComprehArgIf v) = v
getValFromIterClause (ComprehArgFor _ _ v) = v
getValFromIterClause (ComprehArgTmpl v) = v
getValFromIterClause (ComprehArgIterVal v) = v

setValInIterClause :: Val -> ComprehArg -> ComprehArg
setValInIterClause v (ComprehArgLet n _) = ComprehArgLet n v
setValInIterClause v (ComprehArgIf _) = ComprehArgIf v
setValInIterClause v (ComprehArgFor n m _) = ComprehArgFor n m v
setValInIterClause v (ComprehArgTmpl _) = ComprehArgTmpl v
setValInIterClause v (ComprehArgIterVal _) = ComprehArgIterVal v
