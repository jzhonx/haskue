{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.Interpolation where

import Control.DeepSeq (NFData (..))
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

data Interpolation = Interpolation
  { itpSegs :: [IplSeg]
  , itpExprs :: Seq.Seq Tree
  }
  deriving (Generic)

data IplSeg = IplSegExpr !Int | IplSegStr T.Text
  deriving (Eq, Show, Generic, NFData)

emptyInterpolation :: Interpolation
emptyInterpolation = Interpolation [] Seq.empty