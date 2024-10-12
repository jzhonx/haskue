module Value.Bottom where

import qualified AST
import Value.Class

newtype Bottom = Bottom {btmMsg :: String}

instance Eq Bottom where
  (==) _ _ = True

instance BuildASTExpr Bottom where
  buildASTExpr _ _ = return $ AST.litCons AST.BottomLit

instance Show Bottom where
  show (Bottom m) = m
