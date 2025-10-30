{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import Data.Foldable (toList)
import Data.List (intercalate)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import GHC.Generics (Generic)
import Path
import StringIndex (ShowWithTextIndexer (..), TextIndex, TextIndexerMonad, textToTextIndex)
import Text.Printf (printf)
import Value.Atom
import {-# SOURCE #-} Value.Tree

newtype Reference = Reference {refArg :: RefArg} deriving (Generic)

data RefArg
  = -- | RefPath denotes a reference starting with an identifier.
    RefPath TextIndex (Seq.Seq Tree)
  | -- | RefIndex denotes a reference starts with an in-place value. For example, ({x:1}.x).
    RefIndex (Seq.Seq Tree)
  deriving (Generic)

-- newtype RefIdent = RefIdent TextIndex deriving (Show, Generic, Eq, Ord)

-- instance ShowWithTextIndexer RefIdent where
--   tshow (RefIdent s) = tshow s

-- tshow (RefIdentWithOID s i) = do
--   sStr <- tshow s
--   return $ T.pack $ printf "%s_%s" sStr (show i)

-- refIdentToTextIndex :: (TextIndexerMonad s m) => RefIdent -> m TextIndex
-- refIdentToTextIndex (RefIdent s) = return s

-- refIdentToTextIndex (RefIdentWithOID s i) = do
--   str <- tshow s
--   let x = str `T.append` T.pack ("_" ++ show i)
--   textToTextIndex x

-- refIdentToLetTASeg :: (TextIndexerMonad s m) => RefIdent -> m Feature
-- refIdentToLetTASeg (RefIdent s) = mkLetFeature s Nothing

-- refIdentToLetTASeg (RefIdentWithOID s i) = mkLetFeature s (Just i)

-- letTASegToRefIdent :: TextIndex -> RefIdent
-- letTASegToRefIdent s = RefIdent s

-- letTASegToRefIdent s (Just i) = RefIdentWithOID s i

showRefArg :: RefArg -> (Tree -> Maybe String) -> String
showRefArg (RefPath s xs) f = intercalate "." (show s : map (\x -> maybe "_" id (f x)) (toList xs))
showRefArg (RefIndex xs) f = "index." ++ intercalate "." (map (\x -> maybe "_" id (f x)) (toList xs))

refHasRefPath :: Reference -> Bool
refHasRefPath r = case refArg r of
  RefPath _ _ -> True
  RefIndex _ -> False

getIndexSegs :: Reference -> Maybe (Seq.Seq Tree)
getIndexSegs r = case refArg r of
  RefPath _ _ -> Nothing
  RefIndex xs -> Just xs

-- fieldPathFromRefArg :: (Tree -> Maybe Atom) -> RefArg -> Maybe FieldPath
-- fieldPathFromRefArg treeToA arg = case arg of
--   RefPath ident xs -> do
--     sels <-
--       mapM
--         ( \x -> case treeToA x of
--             Just (String s) -> return $ StringSel (TE.encodeUtf8 s)
--             Just (Int i) -> return $ IntSel (fromIntegral i)
--             _ -> Nothing
--         )
--         (toList xs)
--     return $ FieldPath (StringSel (TE.encodeUtf8 $ refIdentToTextIndex ident) : sels)
--   -- RefIndex does not start with a string.
--   RefIndex _ -> Nothing

-- fieldPathFromRef :: (Tree -> Maybe Atom) -> Reference -> Maybe FieldPath
-- fieldPathFromRef treeToA ref = fieldPathFromRefArg treeToA (refArg ref)

appendRefArg :: Tree -> RefArg -> RefArg
appendRefArg y (RefPath s xs) = RefPath s (xs Seq.|> y)
appendRefArg y (RefIndex xs) = RefIndex (xs Seq.|> y)

subRefArgs :: RefArg -> Seq.Seq Tree
subRefArgs (RefPath _ xs) = xs
subRefArgs (RefIndex xs) = xs

modifySubRefArgs :: (Seq.Seq Tree -> Seq.Seq Tree) -> RefArg -> RefArg
modifySubRefArgs f (RefPath s xs) = RefPath s (f xs)
modifySubRefArgs f (RefIndex xs) = RefIndex (f xs)

mkIndexRef :: Seq.Seq Tree -> Reference
mkIndexRef ts =
  Reference
    { refArg = RefIndex ts
    }

emptyIdentRef :: TextIndex -> Reference
emptyIdentRef ident =
  Reference
    { refArg = RefPath ident Seq.empty
    }

mkRefFromFieldPath :: (TextIndexerMonad s m) => (Atom -> Tree) -> TextIndex -> FieldPath -> m Reference
mkRefFromFieldPath aToTree ident (FieldPath xs) = do
  ys <-
    mapM
      ( \y -> case y of
          StringSel s -> do
            str <- tshow s
            return $ aToTree (String str)
          IntSel i -> return $ aToTree (Int $ fromIntegral i)
      )
      xs
  return $
    Reference
      { refArg = RefPath ident (Seq.fromList ys)
      }