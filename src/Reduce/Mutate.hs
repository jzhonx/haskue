{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Mutate where

import Common (TreeOp (isTreeBottom, treeHasRef), ctxNotifGraph, showRefNotifiers)
import Control.Monad (unless, when)
import Control.Monad.Reader (asks)
import qualified Cursor
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isNothing)
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.RMonad as RM
import qualified TCOps
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

-- | Replace the mutable tree node with the mutval.
reduceToMutVal :: (RM.ReduceTCMonad s r m) => VT.Tree -> m ()
reduceToMutVal val = do
  RM.modifyTMTN (VT.treeNode val)
  handleRefCycleRM

{- | Convert the RefCycleTail to VT.RefCycle if the addr is the same as the cycle start addr.

RefCycleTail is like Bottom.
-}
handleRefCycleRM :: (RM.ReduceTCMonad s r m) => m ()
handleRefCycleRM = undefined

{- | Delete the notification receivers that have the specified prefix.

we need to delete receiver starting with the addr, not only the addr. For example, if the function
is index and the first argument is a reference, then the first argument dependency should also be
deleted.
-}
delRefSysRecvPrefix :: (RM.ReduceTCMonad s r m) => Path.TreeAddr -> m ()
delRefSysRecvPrefix addrPrefix = do
  RM.modifyRMContext $ \ctx -> ctx{ctxNotifGraph = delEmptyElem $ del (ctxNotifGraph ctx)}
  RM.withAddrAndFocus $ \addr _ -> do
    notifiers <- ctxNotifGraph <$> RM.getRMContext
    logDebugStr $
      printf
        "delRefSysRecvs: addr: %s delete receiver prefix: %s, updated notifiers: %s"
        (show addr)
        (show addrPrefix)
        (showRefNotifiers notifiers)
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
delMutValRecvs mutAddr = do
  RM.modifyRMContext $ \ctx -> ctx{ctxNotifGraph = delEmptyElem $ delRecvs (ctxNotifGraph ctx)}
 where
  delEmptyElem :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  delEmptyElem = Map.filter (not . null)

  -- Delete the receivers that have the mutable address as the prefix.
  delRecvs :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  delRecvs =
    Map.map
      ( filter
          ( \recv ->
              let
                mutValAddr = Path.appendSeg Path.SubValTASeg mutAddr
               in
                not $ Path.isPrefix mutValAddr recv
          )
      )

mutateDisjOp :: (RM.ReduceMonad s r m) => Bool -> VT.DisjoinOp VT.Tree -> TCOps.TrCur -> m (Maybe VT.Tree)
mutateDisjOp asConj terms disjOpTC = RM.debugSpanRM "mutateDisjoinOp" disjOpTC $ do
  disjuncts <- procMarkedTerms asConj (VT.djoTerms terms) disjOpTC
  RM.debugInstantRM "mutateDisjOp" (printf "disjuncts: %s" (show disjuncts)) disjOpTC
  let
    d = VT.emptyDisj{VT.dsjDisjuncts = disjuncts}
  r <- VT.normalizeDisj VT.getDisjFromTree VT.mkDisjTree d
  return $ Just r

{- | Construct a disjunction from the default and the disjuncts.

Some existing rules for marked disjunctions:
M0:  ⟨v⟩    => ⟨v⟩        don't introduce defaults for unmarked term
M1: *⟨v⟩    => ⟨v, v⟩     introduce identical default for marked term
M2: *⟨v, d⟩ => ⟨v, d⟩     keep existing defaults for marked term
M3:  ⟨v, d⟩ => ⟨v⟩        strip existing defaults from unmarked term
-}
procMarkedTerms :: (RM.ReduceMonad s r m) => Bool -> [VT.DisjTerm VT.Tree] -> TCOps.TrCur -> m [VT.Tree]
procMarkedTerms asConj terms tc = do
  -- disjoin operation allows incompleteness.

  let hasMarked = any VT.dstMarked terms
  reducedTerms <-
    -- If the unification is a conjunct, there is no need to reduce the terms.
    if asConj
      then return terms
      else
        mapM
          ( \(i, term) -> do
              a <- reduceMutableArg (Path.MutableArgTASeg i) tc
              return $ term{VT.dstValue = a}
          )
          (zip [0 ..] terms)
  return $
    foldr
      ( \term accDisjuncts ->
          let val = VT.dstValue term
           in if
                -- Apply Rule M1 and M2
                | hasMarked && VT.dstMarked term ->
                    VT.setTN
                      val
                      ( VT.TNDisj $
                          maybe
                            -- Rule M1
                            (VT.emptyDisj{VT.dsjDefIndexes = [0], VT.dsjDisjuncts = [val]})
                            ( \d ->
                                if null (VT.dsjDefIndexes d)
                                  -- Rule M1
                                  then d{VT.dsjDefIndexes = [0 .. length (VT.dsjDisjuncts d)]}
                                  -- Rule M2
                                  else d
                            )
                            (VT.getDisjFromTree val)
                      )
                      : accDisjuncts
                -- Apply Rule M0 and M3
                | hasMarked ->
                    maybe
                      val
                      (\d -> VT.setTN val $ VT.TNDisj $ d{VT.dsjDefIndexes = []})
                      (VT.getDisjFromTree val)
                      : accDisjuncts
                | otherwise -> val : accDisjuncts
      )
      []
      reducedTerms

-- | Reduce the tree cursor to concrete.
reduceToConcrete :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m (Maybe VT.Tree)
reduceToConcrete tc = RM.debugSpanArgsRM "reduceToConcrete" (show tc) tc $ do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  r <- reduce tc
  return $ VT.getNonMutFromTree r

-- | Reduce the argument of the mutable to non-mutable.
reduceMutableArg :: (RM.ReduceMonad s r m) => Path.TASeg -> TCOps.TrCur -> m VT.Tree
reduceMutableArg seg mutTC = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  argTC <- TCOps.goDownTCSegMust seg mutTC
  r <- reduce argTC
  let concreteM = VT.getNonMutFromTree r
  return $ fromMaybe r concreteM

-- * VT.Mutable Environment

{- | Go to the parent mutable and run the action in an argument environment, then come back to the mutval environment.

The mutable must see changes propagated from the argument environment.
-}
mutValToArgsRM :: (RM.ReduceTCMonad s r m) => Path.TASeg -> m a -> m a
mutValToArgsRM subSeg f = doInMutRM $ RM.mustMutable $ \_ -> RM.inSubTM subSeg f
 where
  -- Run the action in the parent tree. All changes will be propagated to the parent tree and back to the current
  -- tree.
  -- After evaluating the argument environment, the focus of the tree should still be the mutable.
  doInMutRM :: (RM.ReduceTCMonad s r m) => m a -> m a
  doInMutRM action = do
    seg <- RM.getTMTASeg
    RM.propUpTM
    r <- action
    ok <- RM.descendTMSeg seg
    unless ok $ throwErrSt $ printf "failed to go down with seg %s" (show seg)
    return r

_runInMutValEnv :: (RM.ReduceTCMonad s r m) => m a -> m a
_runInMutValEnv f = RM.mustMutable $ \_ -> do
  ok <- RM.descendTMSeg Path.SubValTASeg
  unless ok $ throwErrSt "can not descend to the mutable value"
  r <- f
  RM.propUpTM
  return r

_resetRMMutVal :: (RM.ReduceTCMonad s r m) => m ()
_resetRMMutVal = _mustSetMutVal Nothing

_mustSetMutVal :: (RM.ReduceTCMonad s r m) => Maybe VT.Tree -> m ()
_mustSetMutVal m = RM.mustMutable $ \mut -> RM.modifyTMTN (VT.TNMutable $ VT.setMutVal m mut)

{- | Get the mutable value of the mutable node.

If the function can not generate a value due to incomplete arguments, then Nothing is returned.
-}
_getRMMutVal :: (RM.ReduceTCMonad s r m) => m (Maybe VT.Tree)
_getRMMutVal = RM.mustMutable $ \mut -> return (VT.getMutVal mut)

-- | Run the function with the existing mutable value if it exists.
_runWithExtMutVal :: (RM.ReduceTCMonad s r m) => (VT.Tree -> m ()) -> m ()
_runWithExtMutVal f = maybe (return ()) f =<< _getRMMutVal
