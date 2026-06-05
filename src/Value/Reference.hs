{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import Control.DeepSeq (NFData)
import qualified Data.Sequence as Seq
import Feature (CanonicalAddr, Feature, ValAddr)
import GHC.Generics (Generic)
import StringIndex (TextIndex)
import {-# SOURCE #-} Value.Val

-- | Reference denotes a reference starting with an identifier.
data Reference = Reference
  { ident :: TextIndex
  , identFeat :: Feature
  , selectors :: Seq.Seq VNode
  , selectorTypes :: Seq.Seq Bool
  -- ^ selectorTypes stores the type of each selector, where True means index select (e.g. `a[0]`) and False means field
  -- select (e.g. `a.b`).
  , resolvedIdentType :: RefIdentType
  , resolvedIdentAddr :: ResolvedIdentAddr
  -- ^ The resolved address of the identifier.
  , resolvedFullAddr :: Maybe ValAddr
  -- ^ The resolved full address of the reference.
  , resolvedComprehClauseIdx :: Maybe Int
  -- ^ The resolved comprehension binding of the reference, represented as (comprehension depth, identifier).
  , isRefCycle :: !Bool
  }
  deriving (Generic)

data RefIdentType
  = ITField
  | ITLetBinding
  | ITIterBinding
  deriving (Eq, Show, Generic, NFData)

data ResolvedIdentAddr
  = ResolvedIdentFromTop ValAddr
  | ToTargetScopeDiff CanonicalAddr
  deriving (Eq, Show, Generic, NFData)

mapRefSels :: (Seq.Seq VNode -> Seq.Seq VNode) -> Reference -> Reference
mapRefSels f ref = ref{selectors = f (selectors ref)}

singletonIdentRef :: TextIndex -> Feature -> RefIdentType -> ResolvedIdentAddr -> Reference
singletonIdentRef ident identFeat typ addr =
  Reference
    { ident = ident
    , identFeat
    , selectors = Seq.empty
    , selectorTypes = Seq.empty
    , resolvedIdentType = typ
    , resolvedIdentAddr = addr
    , resolvedFullAddr = Nothing
    , resolvedComprehClauseIdx = Nothing
    , isRefCycle = False
    }

comprehensionIdentRef :: TextIndex -> Feature -> Int -> ResolvedIdentAddr -> Reference
comprehensionIdentRef ident identFeat cIdx addr =
  Reference
    { ident = ident
    , identFeat
    , selectors = Seq.empty
    , selectorTypes = Seq.empty
    , resolvedIdentType = ITIterBinding
    , resolvedIdentAddr = addr
    , resolvedFullAddr = Nothing
    , resolvedComprehClauseIdx = Just cIdx
    , isRefCycle = False
    }

appendRefArg :: VNode -> Bool -> Reference -> Reference
appendRefArg v typ ref = ref{selectors = selectors ref Seq.|> v, selectorTypes = selectorTypes ref Seq.|> typ}

{- | ValueSelect denotes a select operation with a base and multiple selectors.

The base (receiver) is a value instead of an identifier.
-}
data ValueSelect = ValueSelect
  { bvID :: !Int
  , base :: VNode
  , iSelectors :: Seq.Seq VNode
  , iSelectorTypes :: Seq.Seq Bool
  }
  deriving (Generic)

appendValueSelectArg :: VNode -> Bool -> ValueSelect -> ValueSelect
appendValueSelectArg y typ vs = vs{iSelectors = iSelectors vs Seq.|> y, iSelectorTypes = iSelectorTypes vs Seq.|> typ}