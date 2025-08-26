{-# LANGUAGE FlexibleContexts #-}

module Value.Util.BuildASTExpr where

import qualified AST
import Common (ErrorEnv)
import {-# SOURCE #-} Value.Tree

buildASTExprDebug :: (ErrorEnv m) => Tree -> m AST.Expression