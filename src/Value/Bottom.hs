module Value.Bottom where

import qualified AST
import Common (BuildASTExpr (..))

newtype Bottom = Bottom {btmMsg :: String}

instance Eq Bottom where
  (==) _ _ = True

instance BuildASTExpr Bottom where
  buildASTExpr _ _ = return $ AST.litCons (pure AST.BottomLit)

instance Show Bottom where
  show (Bottom m) = m
