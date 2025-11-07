{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import Data.Foldable (toList)
import Data.List (intercalate)
import qualified Data.Sequence as Seq
import Feature
import GHC.Generics (Generic)
import StringIndex (ShowWithTextIndexer (..), TextIndex, TextIndexerMonad)
import Value.Atom
import {-# SOURCE #-} Value.Tree

newtype Reference = Reference {refArg :: RefArg} deriving (Generic)

data RefArg
  = -- | RefPath denotes a reference starting with an identifier.
    RefPath TextIndex (Seq.Seq Tree)
  | -- | RefIndex denotes a reference starts with an in-place value. For example, ({x:1}.x).
    RefIndex (Seq.Seq Tree)
  deriving (Generic)

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