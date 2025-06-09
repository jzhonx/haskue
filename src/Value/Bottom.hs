{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.Bottom where

import qualified AST
import Common (BuildASTExpr (..))
import Control.DeepSeq (NFData (..))
import GHC.Generics (Generic)

newtype Bottom = Bottom {btmMsg :: String}
  deriving (Generic, NFData)

instance Eq Bottom where
  (==) _ _ = True

instance BuildASTExpr Bottom where
  buildASTExpr _ _ = return $ AST.litCons (pure AST.BottomLit)

instance Show Bottom where
  show (Bottom m) = m
