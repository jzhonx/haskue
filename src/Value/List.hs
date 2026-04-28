{-# LANGUAGE DeriveGeneric #-}

module Value.List where

import qualified Data.Vector as V
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Val

data List = List
  { store :: V.Vector VNode
  -- ^ Stores the variants of the list, including the comprehensions.
  , final :: V.Vector VNode
  -- ^ Stores the finalized elements of the list.
  -- Reference to the list should only read from the final field.
  }
  deriving (Generic)

mkList :: [VNode] -> [VNode] -> List
mkList x y =
  List
    { store = V.fromList x
    , final = V.fromList y
    }

getListStoreAt :: Int -> List -> Maybe VNode
getListStoreAt i lst = store lst V.!? i

updateListStoreAt :: Int -> (VNode -> VNode) -> List -> List
updateListStoreAt i f lst = lst{store = store lst V.// [(i, f (store lst V.! i))]}

getListFinalAt :: Int -> List -> Maybe VNode
getListFinalAt i lst = final lst V.!? i

updateListFinalAt :: Int -> (VNode -> VNode) -> List -> List
updateListFinalAt i f lst = lst{final = final lst V.// [(i, f (final lst V.! i))]}
