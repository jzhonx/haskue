{-# LANGUAGE FlexibleContexts #-}

module Value.Util.BuildASTExpr where

import qualified AST
import Control.Monad.Except (Except)
import StringIndex (TextIndexer)
import {-# SOURCE #-} Value.Tree

buildASTExprDebug :: Tree -> TextIndexer -> (Except String) (AST.Expression, TextIndexer)