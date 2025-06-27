{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Mutate where

import Common (ctxNotifGraph)
import Cursor
import qualified Data.Map.Strict as Map
import Path
import Reduce.RMonad (
  ReduceMonad,
  debugSpanArgsRM,
  modifyRMContext,
 )
import {-# SOURCE #-} Reduce.Root (reduce)
import Value

{- | Delete the notification receivers that have the specified prefix.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delRefSysRecvPrefix :: (ReduceMonad s r m) => TreeAddr -> m ()
delRefSysRecvPrefix addrPrefix = do
  modifyRMContext $ \ctx -> ctx{ctxNotifGraph = delEmptyElem $ del (ctxNotifGraph ctx)}
 where
  delEmptyElem :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  delEmptyElem = Map.filter (not . null)

  del :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  del = Map.map (filter (\p -> not (isPrefix addrPrefix p)))

{- | Delete the notification receivers of the sub values of the mutval.

If the receiver addresss is the mutable address itself, then it should be skipped because the mutable could be a
reference.

If the receiver addresss is the mutable address plus the argument segment, then it should be skipped.
-}
delMutValRecvs :: (ReduceMonad s r m) => TreeAddr -> m ()
delMutValRecvs mutAddr = modifyRMContext $ \ctx -> ctx{ctxNotifGraph = delRecvsInMap mutAddr (ctxNotifGraph ctx)}

-- | Delete the receivers that have the mutable address as the prefix.
delRecvsInMap :: TreeAddr -> Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
delRecvsInMap mutAddr =
  Map.mapMaybe
    ( \l ->
        let r =
              filter
                ( \recv ->
                    let
                      mutValAddr = appendSeg mutAddr SubValTASeg
                     in
                      not $ {-# SCC "isPrefix" #-} isPrefix mutValAddr recv
                )
                l
         in if null r
              then Nothing
              else Just r
    )

-- | Reduce the tree cursor to non-mutable.
reduceToNonMut :: (ReduceMonad s r m) => TrCur -> m (Maybe Tree)
reduceToNonMut tc = debugSpanArgsRM "reduceToNonMut" (show tc) id tc $ do
  r <- reduce tc
  return $ rtrNonMut r
