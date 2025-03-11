{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Value.Disj where

import qualified AST
import Class (BuildASTExpr (..))

data Disj t = Disj
  { dsjDefault :: Maybe t
  , dsjDisjuncts :: [t]
  }

instance (Eq t) => Eq (Disj t) where
  (==) (Disj ds1 js1) (Disj ds2 js2) = ds1 == ds2 && js1 == js2

instance (BuildASTExpr t) => BuildASTExpr (Disj t) where
  buildASTExpr c dj =
    maybe
      ( do
          xs <- mapM (buildASTExpr c) (dsjDisjuncts dj)
          return $
            foldr1
              (AST.ExprBinaryOp AST.Disjunction)
              xs
      )
      (buildASTExpr c)
      (dsjDefault dj)
