{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Mutate where

import Common (ctxNotifGraph)
import Control.Monad.Reader (asks)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified MutEnv
import qualified Path
import qualified Reduce.RMonad as RM
import qualified TCOps
import qualified Value.Tree as VT

{- | Delete the notification receivers that have the specified prefix.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delRefSysRecvPrefix :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m ()
delRefSysRecvPrefix addrPrefix = do
  RM.modifyRMContext $ \ctx -> ctx{ctxNotifGraph = delEmptyElem $ del (ctxNotifGraph ctx)}
 where
  delEmptyElem :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  delEmptyElem = Map.filter (not . null)

  del :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  del = Map.map (filter (\p -> not (Path.isPrefix addrPrefix p)))

{- | Delete the notification receivers of the sub values of the mutval.

If the receiver addresss is the mutable address itself, then it should be skipped because the mutable could be a
reference.

If the receiver addresss is the mutable address plus the argument segment, then it should be skipped.
-}
delMutValRecvs :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m ()
delMutValRecvs mutAddr = RM.modifyRMContext $ \ctx -> ctx{ctxNotifGraph = delRecvsInMap mutAddr (ctxNotifGraph ctx)}

-- | Delete the receivers that have the mutable address as the prefix.
delRecvsInMap :: Path.TreeAddr -> Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
delRecvsInMap mutAddr =
  Map.mapMaybe
    ( \l ->
        let r =
              filter
                ( \recv ->
                    let
                      mutValAddr = Path.appendSeg mutAddr Path.SubValTASeg
                     in
                      not $ {-# SCC "isPrefix" #-} Path.isPrefix mutValAddr recv
                )
                l
         in if null r
              then Nothing
              else Just r
    )

-- | Reduce the tree cursor to non-mutable.
reduceToNonMut :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m (Maybe VT.Tree)
reduceToNonMut tc = RM.debugSpanArgsRM "reduceToNonMut" (show tc) id tc $ do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  r <- reduce tc
  return $ VT.getNonMutFromTree r

-- | Reduce the argument of the mutable to non-mutable.
reduceMutableArg :: (RM.ReduceMonad s r m) => Path.TASeg -> TCOps.TrCur -> m VT.Tree
reduceMutableArg seg mutTC = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  argTC <- TCOps.goDownTCSegMust seg mutTC
  r <- reduce argTC
  let nonMutM = VT.getNonMutFromTree r
  return $ fromMaybe r nonMutM
