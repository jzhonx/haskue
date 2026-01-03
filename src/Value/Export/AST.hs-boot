{-# LANGUAGE FlexibleContexts #-}

module Value.Export.AST where

import qualified AST
import Control.Monad.Except (Except)
import StringIndex (TextIndexer)
import {-# SOURCE #-} Value.Val

buildExprDebug :: Val -> TextIndexer -> (Except String) (AST.Expression, TextIndexer)