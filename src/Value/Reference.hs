{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import qualified Data.Sequence as Seq
import Feature (ReferableAddr)
import GHC.Generics (Generic)
import StringIndex (TextIndex)
import {-# SOURCE #-} Value.Val

-- | Reference denotes a reference starting with an identifier.
data Reference = Reference
  { ident :: TextIndex
  , selectors :: Seq.Seq Val
  , resolvedIdentAddr :: Maybe ReferableAddr
  -- ^ The resolved address of the identifier.
  , resolvedFullAddr :: Maybe ReferableAddr
  -- ^ The resolved full address of the reference.
  }
  deriving (Generic)

getRefSels :: Reference -> Seq.Seq Val
getRefSels (Reference _ xs _ _) = xs

mapRefSels :: (Seq.Seq Val -> Seq.Seq Val) -> Reference -> Reference
mapRefSels f ref = ref{selectors = f (selectors ref)}

singletonIdentRef :: TextIndex -> Reference
singletonIdentRef ident =
  Reference
    { ident = ident
    , selectors = Seq.empty
    , resolvedIdentAddr = Nothing
    , resolvedFullAddr = Nothing
    }

appendRefArg :: Val -> Reference -> Reference
appendRefArg v ref = ref{selectors = selectors ref Seq.|> v}

-- | InplaceIndex denotes a reference starts with an in-place value. For example, ({x:1}.x).
newtype InplaceIndex = InplaceIndex (Seq.Seq Val)
  deriving (Generic)

appendInplaceIndexArg :: Val -> InplaceIndex -> InplaceIndex
appendInplaceIndexArg y (InplaceIndex xs) = InplaceIndex (xs Seq.|> y)