{-# LANGUAGE DeriveGeneric #-}

module Value.List where

import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

newtype List = List {lstSubs :: [Tree]} deriving (Generic)
