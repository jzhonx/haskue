{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.Bottom where

import Control.DeepSeq (NFData (..))
import GHC.Generics (Generic)

newtype Bottom = Bottom {btmMsg :: String}
  deriving (Generic, NFData)

instance Eq Bottom where
  (==) _ _ = True

instance Show Bottom where
  show (Bottom m) = m
