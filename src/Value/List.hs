{-# LANGUAGE DeriveGeneric #-}

module Value.List where

import qualified Data.Vector as V
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

data List = List
  { store :: V.Vector Tree
  -- ^ Stores the variants of the list, including the comprehensions.
  , final :: V.Vector Tree
  -- ^ Stores the finalized elements of the list.
  -- Reference to the list should only read from the final field.
  }
  deriving (Generic)

mkList :: [Tree] -> [Tree] -> List
mkList x y =
  List
    { store = V.fromList x
    , final = V.fromList y
    }

getListStoreAt :: Int -> List -> Maybe Tree
getListStoreAt i lst = store lst V.!? i

updateListStoreAt :: Int -> Tree -> List -> List
updateListStoreAt i t lst = lst{store = store lst V.// [(i, t)]}

getListFinalAt :: Int -> List -> Maybe Tree
getListFinalAt i lst = final lst V.!? i

updateListFinalAt :: Int -> Tree -> List -> List
updateListFinalAt i t lst = lst{final = final lst V.// [(i, t)]}
