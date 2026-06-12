{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.Interpolation where

import Control.DeepSeq (NFData (..))
import qualified Data.ByteString.Char8 as BC
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Val

{- | An Interpolation is made up of string segments and expressions.

For example, "hello, \(name)" is make up of the string segment "hello, " and the expression `name`.
-}
data Interpolation = Interpolation
  { itpSegs :: [IplSeg]
  , itpExprs :: Seq.Seq VNode
  , itpIsBytes :: Bool
  }
  deriving (Generic)

-- | Interpolation segments can be either expressions or string literals.
data IplSeg
  = -- | VSelect of the expression in `itpExprs`
    IplSegExpr !Int
  | IplSegStr BC.ByteString
  deriving (Eq, Show, Generic, NFData)

emptyInterpolation :: Interpolation
emptyInterpolation = Interpolation [] Seq.empty False