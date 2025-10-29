{-# LANGUAGE FlexibleContexts #-}

module Value.Util.BuildASTExpr where

import qualified AST
import Common (ErrorEnv)
import StringIndex (TextIndexerMonad)
import {-# SOURCE #-} Value.Tree

buildASTExprDebug :: (ErrorEnv m, TextIndexerMonad s m) => Tree -> m AST.Expression