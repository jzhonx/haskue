{-# LANGUAGE FlexibleContexts #-}

module Class where

import qualified AST
import Env
import Path

class BuildASTExpr a where
  -- The first argument is a flag to indicate whether the expression is required to be concrete.
  buildASTExpr :: (Env m) => Bool -> a -> m AST.Expression

class TreeRepBuilder a where
  repTree :: Int -> a -> String

class TreeRepBuilderIter a where
  -- (symbol, meta, fields, listedMetas)
  -- field : (Label, Attr, Value)
  iterRepTree :: a -> (String, String, [(String, String, a)], [(String, String)])

class TreeOp a where
  -- step down the tree with the given selector.
  -- This should only be used by TreeCursor.
  subTree :: Selector -> a -> Maybe a

  -- Set the subtree to the given tree with the selector. The first argument is the selector, the second argument is the
  -- sub tree, and the third argument is the tree to be updated.
  setSubTree :: (Env m) => Selector -> a -> a -> m a

  -- Get the var field with the given selector when the tree is a struct.
  getVarField :: StructSelector -> a -> Maybe a

  isTreeAtom :: a -> Bool
  isTreeBottom :: a -> Bool
  isTreeCnstr :: a -> Bool
  isTreeRefCycle :: a -> Bool
  isTreeFunc :: a -> Bool
  isTreeValue :: a -> Bool

  -- isTreeReducible :: a -> Bool
  treeHasRef :: a -> Bool
  treeHasAtom :: a -> Bool
