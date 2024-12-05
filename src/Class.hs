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

class TreeOp a where
  -- step down the tree with the given segment.
  -- This should only be used by TreeCursor.
  subTree :: TASeg -> a -> Maybe a

  -- Set the subtree to the given tree with the segment. The first argument is the segment, the second argument is the
  -- sub tree, and the third argument is the tree to be updated.
  setSubTree :: (Env m) => TASeg -> a -> a -> m a

  -- delete the temp value in the tree.
  delTemp :: a -> a

  isTreeAtom :: a -> Bool
  isTreeBottom :: a -> Bool
  isTreeCnstr :: a -> Bool
  isTreeRefCycle :: a -> Bool
  isTreeMutable :: a -> Bool
  isTreeValue :: a -> Bool

  treeHasRef :: a -> Bool
  treeHasAtom :: a -> Bool
