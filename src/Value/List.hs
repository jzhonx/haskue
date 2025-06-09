{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.List where

import qualified AST
import Common (BuildASTExpr (..))
import Control.DeepSeq (NFData (..))
import GHC.Generics (Generic)

newtype List t = List {lstSubs :: [t]} deriving (Show, Generic, NFData)

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
