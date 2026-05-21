{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import Control.DeepSeq (NFData)
import qualified Data.Sequence as Seq
import Feature (ValAddr)
import GHC.Generics (Generic)
import StringIndex (TextIndex)
import {-# SOURCE #-} Value.Val

-- | Reference denotes a reference starting with an identifier.
data Reference = Reference
  { ident :: TextIndex
  , selectors :: Seq.Seq VNode
  , resolvedIdentType :: RefIdentType
  , resolvedIdentAddr :: ValAddr
  -- ^ The resolved address of the identifier.
  -- Resolved identifier can be resolved in a field, a stub dyanmic field.
  , resolvedFullAddr :: Maybe ValAddr
  -- ^ The resolved full address of the reference.
  , isRefCycle :: !Bool
  }
  deriving (Generic)

data RefIdentType
  = ITField
  | ITLetBinding
  | ITIterBinding
  deriving (Eq, Show, Generic, NFData)

mapRefSels :: (Seq.Seq VNode -> Seq.Seq VNode) -> Reference -> Reference
mapRefSels f ref = ref{selectors = f (selectors ref)}

singletonIdentRef :: TextIndex -> RefIdentType -> ValAddr -> Reference
singletonIdentRef ident typ addr =
  Reference
    { ident = ident
    , selectors = Seq.empty
    , resolvedIdentType = typ
    , resolvedIdentAddr = addr
    , resolvedFullAddr = Nothing
    , isRefCycle = False
    }

appendRefArg :: VNode -> Reference -> Reference
appendRefArg v ref = ref{selectors = selectors ref Seq.|> v}

{- | ValueSelect denotes a select operation with a base and multiple selectors.

The base (receiver) is a value instead of an identifier.
-}
data ValueSelect = ValueSelect
  { bvID :: !Int
  , base :: VNode
  , iSelectors :: Seq.Seq VNode
  }
  deriving (Generic)

appendValueSelectArg :: VNode -> ValueSelect -> ValueSelect
appendValueSelectArg y vs@(ValueSelect _ _ xs) = vs{iSelectors = xs Seq.|> y}