module Value.List where

import qualified AST
import Class (BuildASTExpr (..))

newtype List t = List {lstSubs :: [t]}

instance (Eq t) => Eq (List t) where
  (==) l1 l2 = lstSubs l1 == lstSubs l2

instance (BuildASTExpr t) => BuildASTExpr (List t) where
  buildASTExpr c l =
    AST.litCons . AST.ListLit . AST.EmbeddingList <$> mapM (buildASTExpr c) (lstSubs l)
