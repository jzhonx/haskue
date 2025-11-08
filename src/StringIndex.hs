{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module StringIndex where

import Control.DeepSeq (NFData (..))
import Control.Monad.State (MonadState, gets, modify')
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)

type TextIndexerMonad s m = (MonadState s m, HasTextIndexer s, HasCallStack)

class HasTextIndexer a where
  getTextIndexer :: a -> TextIndexer
  setTextIndexer :: TextIndexer -> a -> a

class (Show a) => ShowWithTextIndexer a where
  tshow :: (MonadState s m, HasTextIndexer s) => a -> m T.Text
  tshow = return . T.pack . show

instance (ShowWithTextIndexer a) => ShowWithTextIndexer [a] where
  tshow xs = do
    ts <- mapM tshow xs
    return $ if null ts then "[]" else T.pack $ "[" ++ T.unpack (T.intercalate "," ts) ++ "]"

instance (ShowWithTextIndexer k, ShowWithTextIndexer v) => ShowWithTextIndexer (Map.Map k v) where
  tshow xs = do
    kvs <- mapM go (Map.toList xs)
    return $ T.pack $ "{" ++ T.unpack (T.intercalate "," kvs) ++ "}"
   where
    go (k, v) = do
      kt <- tshow k
      vt <- tshow v
      return $ kt <> ":" <> vt

data TextIndexer = TextIndexer
  { labels :: V.Vector T.Text
  , labelToIndex :: Map.Map T.Text Int
  }
  deriving (Eq, Show, Generic, NFData)

emptyTextIndexer :: TextIndexer
emptyTextIndexer = TextIndexer V.empty Map.empty

fetchTextIndex :: T.Text -> TextIndexer -> (Int, TextIndexer)
fetchTextIndex t indexer =
  case Map.lookup t indexer.labelToIndex of
    Just i -> (i, indexer)
    Nothing ->
      let
        i = V.length indexer.labels
        newLabels = V.snoc (labels indexer) t
        newLabelToIndex = Map.insert t i (labelToIndex indexer)
        newIndexer = TextIndexer newLabels newLabelToIndex
       in
        (i, newIndexer)

-- | TextIndex is an index to a text in the TextIndexer.
newtype TextIndex = TextIndex {getTextIndex :: Int}
  deriving (Eq, Ord, Generic, NFData)

instance Show TextIndex where
  show (TextIndex i) = "ti_" ++ show i

instance ShowWithTextIndexer TextIndex where
  tshow (TextIndex i) = do
    indexer <- gets getTextIndexer
    -- It must exist.
    return $ indexer.labels V.! i

textToTextIndex :: (TextIndexerMonad s m) => T.Text -> m TextIndex
textToTextIndex t = do
  indexer <- gets getTextIndexer
  let (i, newIndexer) = fetchTextIndex t indexer
  modify' (setTextIndexer newIndexer)
  return $ TextIndex i

strToTextIndex :: (TextIndexerMonad s m) => String -> m TextIndex
strToTextIndex s = textToTextIndex (T.pack s)
