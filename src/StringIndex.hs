{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module StringIndex where

import Control.DeepSeq (NFData (..))
import Control.Monad.State (MonadState, gets, modify')
import Data.Aeson (ToJSON, ToJSONKey, Value, toJSON)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)

type TextIndexerMonad s m = (MonadState s m, HasTextIndexer s, HasCallStack)

class HasTextIndexer a where
  getTextIndexer :: a -> TextIndexer
  setTextIndexer :: TextIndexer -> a -> a

class (Show a) => ShowWTIndexer a where
  tshow :: (MonadState s m, HasTextIndexer s) => a -> m T.Text
  tshow = return . T.pack . show

instance {-# OVERLAPPABLE #-} (ShowWTIndexer a) => ShowWTIndexer [a] where
  tshow xs = do
    ts <- mapM tshow xs
    return $ if null ts then "[]" else T.pack $ "[" ++ T.unpack (T.intercalate "," ts) ++ "]"

-- Specific instance for String to avoid matching [Char] with the list instance
instance ShowWTIndexer String where
  tshow = return . T.pack

instance (ShowWTIndexer k, ShowWTIndexer v) => ShowWTIndexer (Map.Map k v) where
  tshow xs = do
    kvs <- mapM go (Map.toList xs)
    return $ T.pack $ "{" ++ T.unpack (T.intercalate "," kvs) ++ "}"
   where
    go (k, v) = do
      kt <- tshow k
      vt <- tshow v
      return $ kt <> ":" <> vt

instance ShowWTIndexer Int
instance ShowWTIndexer Bool
instance ShowWTIndexer Char
instance ShowWTIndexer T.Text
instance (ShowWTIndexer a) => ShowWTIndexer (Maybe a)
instance (ShowWTIndexer a, ShowWTIndexer b) => ShowWTIndexer (a, b)

class (ToJSON a) => ToJSONWTIndexer a where
  ttoJSON :: (MonadState s m, HasTextIndexer s) => a -> m Value
  ttoJSON = return . toJSON

instance ToJSONWTIndexer ()
instance ToJSONWTIndexer Bool
instance ToJSONWTIndexer T.Text
instance (ToJSONWTIndexer a, ToJSONWTIndexer b) => ToJSONWTIndexer (a, b)
instance (ToJSONWTIndexer a) => ToJSONWTIndexer [a] where
  ttoJSON xs = do
    vs <- mapM ttoJSON xs
    return $ toJSON vs
instance (ToJSONWTIndexer a) => ToJSONWTIndexer (Maybe a) where
  ttoJSON Nothing = return $ toJSON (Nothing :: Maybe Value)
  ttoJSON (Just x) = do
    v <- ttoJSON x
    return $ toJSON (Just v)
instance (ShowWTIndexer k, ToJSONKey k, ToJSONWTIndexer v) => ToJSONWTIndexer (Map.Map k v) where
  ttoJSON m = do
    kvs <- mapM go (Map.toList m)
    return $ toJSON kvs
   where
    go (k, v) = do
      kt <- tshow k
      vt <- ttoJSON v
      return (toJSON kt, vt)

data TextIndexer = TextIndexer
  { labels :: V.Vector T.Text
  , labelToIndex :: Map.Map T.Text Int
  }
  deriving (Eq, Show, Generic, NFData)

instance HasTextIndexer TextIndexer where
  getTextIndexer = id
  setTextIndexer newIndexer _ = newIndexer

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

instance ToJSONKey TextIndex

instance Show TextIndex where
  show (TextIndex i) = "ti_" ++ show i

instance ShowWTIndexer TextIndex where
  tshow (TextIndex i) = do
    indexer <- gets getTextIndexer
    -- It must exist.
    return $ indexer.labels V.! i

instance ToJSON TextIndex where
  toJSON (TextIndex i) = toJSON i
instance ToJSONWTIndexer TextIndex

textToTextIndex :: (TextIndexerMonad s m) => T.Text -> m TextIndex
textToTextIndex t = do
  indexer <- gets getTextIndexer
  let (i, newIndexer) = fetchTextIndex t indexer
  modify' (setTextIndexer newIndexer)
  return $ TextIndex i

strToTextIndex :: (TextIndexerMonad s m) => String -> m TextIndex
strToTextIndex s = textToTextIndex (T.pack s)
