{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.Interpolation where

import Control.DeepSeq (NFData (..))
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Val

{- | An Interpolation is made up of string segments and expressions.

For example, "hello, \(name)" is make up of the string segment "hello, " and the expression `name`.
-}
data Interpolation = Interpolation
  { itpSegs :: [IplSeg]
  , itpExprs :: Seq.Seq Val
  }
  deriving (Generic)

-- | Interpolation segments can be either expressions or string literals.
data IplSeg
  = -- | Index of the expression in `itpExprs`
    IplSegExpr !Int
  | IplSegStr T.Text
  deriving (Eq, Show, Generic, NFData)

emptyInterpolation :: Interpolation
emptyInterpolation = Interpolation [] Seq.empty