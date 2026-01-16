{-# LANGUAGE FlexibleContexts #-}

module Value.Export.AST where

import Control.Monad.Except (Except)
import StringIndex (TextIndexer)
import qualified Syntax.AST as AST
import {-# SOURCE #-} Value.Val

buildExprDebug :: Val -> TextIndexer -> (Except String) (AST.Expression, TextIndexer)