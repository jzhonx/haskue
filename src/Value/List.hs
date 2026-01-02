{-# LANGUAGE DeriveGeneric #-}

module Value.List where

import qualified Data.Vector as V
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Val

data List = List
  { store :: V.Vector Val
  -- ^ Stores the variants of the list, including the comprehensions.
  , final :: V.Vector Val
  -- ^ Stores the finalized elements of the list.
  -- Reference to the list should only read from the final field.
  }
  deriving (Generic)

mkList :: [Val] -> [Val] -> List
mkList x y =
  List
    { store = V.fromList x
    , final = V.fromList y
    }

getListStoreAt :: Int -> List -> Maybe Val
getListStoreAt i lst = store lst V.!? i

updateListStoreAt :: Int -> Val -> List -> List
updateListStoreAt i t lst = lst{store = store lst V.// [(i, t)]}

getListFinalAt :: Int -> List -> Maybe Val
getListFinalAt i lst = final lst V.!? i

updateListFinalAt :: Int -> Val -> List -> List
updateListFinalAt i t lst = lst{final = final lst V.// [(i, t)]}
