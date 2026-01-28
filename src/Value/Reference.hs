{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import StringIndex (TextIndex)
import {-# SOURCE #-} Value.Val

-- | Reference denotes a reference starting with an identifier.
data Reference = Reference
  { ident :: TextIndex
  , selectors :: Seq.Seq Val
  }
  deriving (Generic)

getRefSels :: Reference -> Seq.Seq Val
getRefSels (Reference _ xs) = xs

mapRefSels :: (Seq.Seq Val -> Seq.Seq Val) -> Reference -> Reference
mapRefSels f (Reference s xs) = Reference s (f xs)

singletonIdentRef :: TextIndex -> Reference
singletonIdentRef ident =
  Reference
    { ident = ident
    , selectors = Seq.empty
    }

appendRefArg :: Val -> Reference -> Reference
appendRefArg y (Reference s xs) = Reference s (xs Seq.|> y)

-- | InplaceIndex denotes a reference starts with an in-place value. For example, ({x:1}.x).
newtype InplaceIndex = InplaceIndex (Seq.Seq Val)
  deriving (Generic)

appendInplaceIndexArg :: Val -> InplaceIndex -> InplaceIndex
appendInplaceIndexArg y (InplaceIndex xs) = InplaceIndex (xs Seq.|> y)