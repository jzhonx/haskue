{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.Interpolation where

import Control.DeepSeq (NFData (..))
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import GHC.Generics (Generic)

data IplSeg = IplSegExpr !Int | IplSegStr T.Text
  deriving (Eq, Show, Generic, NFData)

data Interpolation t = Interpolation
  { itpSegs :: [IplSeg]
  , itpExprs :: Seq.Seq t
  , itpValue :: Maybe t
  }
  deriving (Eq, Show, Generic, NFData)

emptyInterpolation :: Interpolation t
emptyInterpolation = Interpolation [] Seq.empty Nothing