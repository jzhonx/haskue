{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Comprehension where

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import StringIndex (TextIndex)
import {-# SOURCE #-} Value.Val

data Comprehension = Comprehension
  { cid :: !Int
  , isListCompreh :: !Bool
  , args :: Seq.Seq ComprehArg
  }
  deriving (Generic)

data ComprehArg
  = ComprehArgLet TextIndex VNode
  | ComprehArgIf VNode
  | ComprehArgFor TextIndex (Maybe TextIndex) VNode
  | -- | The template value that will be used to construct iteration value.
    -- The template might be modified during iteration by upper comprehension layer.
    -- For example, the suffix of references in the template might be replaced by unique ids.
    ComprehArgTmpl VNode
  deriving (Generic)

mkComprehension :: Int -> Bool -> [ComprehArg] -> VNode -> Comprehension
mkComprehension cid isListCompreh clauses sv =
  Comprehension
    { cid
    , isListCompreh = isListCompreh
    , args = Seq.fromList (clauses ++ [ComprehArgTmpl sv])
    }

getValFromIterClause :: ComprehArg -> VNode
getValFromIterClause (ComprehArgLet _ v) = v
getValFromIterClause (ComprehArgIf v) = v
getValFromIterClause (ComprehArgFor _ _ v) = v
getValFromIterClause (ComprehArgTmpl v) = v

setValInIterClause :: VNode -> ComprehArg -> ComprehArg
setValInIterClause v (ComprehArgLet n _) = ComprehArgLet n v
setValInIterClause v (ComprehArgIf _) = ComprehArgIf v
setValInIterClause v (ComprehArgFor n m _) = ComprehArgFor n m v
setValInIterClause v (ComprehArgTmpl _) = ComprehArgTmpl v
