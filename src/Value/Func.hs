{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Func where

import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Val

newtype FuncCall = FuncCall
  { fnFrame :: Seq.Seq VNode
  -- ^ The first element should be resolved to the function address.
  }
  deriving (Generic)
