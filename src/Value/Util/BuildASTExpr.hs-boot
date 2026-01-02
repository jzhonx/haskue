{-# LANGUAGE FlexibleContexts #-}

module Value.Util.BuildASTExpr where

import qualified AST
import Control.Monad.Except (Except)
import StringIndex (TextIndexer)
import {-# SOURCE #-} Value.Val

buildASTExprDebug :: Val -> TextIndexer -> (Except String) (AST.Expression, TextIndexer)