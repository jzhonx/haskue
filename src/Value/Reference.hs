{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import StringIndex (TextIndex)
import {-# SOURCE #-} Value.Tree

newtype Reference = Reference {refArg :: RefArg} deriving (Generic)

data RefArg
  = -- | RefPath denotes a reference starting with an identifier.
    RefPath TextIndex (Seq.Seq Tree)
  | -- | RefIndex denotes a reference starts with an in-place value. For example, ({x:1}.x).
    RefIndex (Seq.Seq Tree)
  deriving (Generic)

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
