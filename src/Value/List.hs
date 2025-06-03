module Value.List where

import qualified AST
import Common (BuildASTExpr (..))

newtype List t = List {lstSubs :: [t]}

instance (Eq t) => Eq (List t) where
  (==) l1 l2 = lstSubs l1 == lstSubs l2

instance (BuildASTExpr t) => BuildASTExpr (List t) where
  buildASTExpr c l = do
    ls <-
      mapM
        ( \x -> do
            e <- buildASTExpr c x
            return $ pure $ AST.AliasExpr e
        )
        (lstSubs l)
    return $ AST.litCons $ AST.ListLit AST.<^> pure (AST.EmbeddingList ls)
