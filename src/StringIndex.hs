{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module StringIndex where

import Control.DeepSeq (NFData (..))
import Control.Monad.State (MonadState, gets, modify)
import qualified Data.Map.Strict as Map
import Data.Text (unpack)
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)

type TextIndexerMonad s m = (MonadState s m, HasTextIndexer s)

class HasTextIndexer a where
  getTextIndexer :: a -> TextIndexer
  setTextIndexer :: TextIndexer -> a -> a

class (Show a) => ShowWithTextIndexer a where
  tshow :: (MonadState s m, HasTextIndexer s) => a -> m String
  tshow = return . show

data TextIndexer = TextIndexer
  { labels :: V.Vector T.Text
  , labelToIndex :: Map.Map T.Text Int
  }
  deriving (Eq, Show, Generic, NFData)

emptyTextIndexer :: TextIndexer
emptyTextIndexer = TextIndexer V.empty Map.empty

getTextIndex :: T.Text -> TextIndexer -> (Int, TextIndexer)
getTextIndex t indexer =
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
newtype TextIndex = TextIndex Int
  deriving (Eq, Ord, Generic, NFData)

instance Show TextIndex where
  show (TextIndex i) = "ti_" ++ show i

instance ShowWithTextIndexer TextIndex where
  tshow s = unpack <$> textIndexToText s

textIndexToText :: (TextIndexerMonad s m) => TextIndex -> m T.Text
textIndexToText (TextIndex i) = do
  indexer <- gets getTextIndexer
  -- It must exist.
  return $ indexer.labels V.! i

textToTextIndex :: (TextIndexerMonad s m) => T.Text -> m TextIndex
textToTextIndex t = do
  indexer <- gets getTextIndexer
  let (i, newIndexer) = getTextIndex t indexer
  modify (setTextIndexer newIndexer)
  return $ TextIndex i

strToTextIndex :: (TextIndexerMonad s m) => String -> m TextIndex
strToTextIndex s = textToTextIndex (T.pack s)
