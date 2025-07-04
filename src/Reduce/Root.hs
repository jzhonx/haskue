{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Root where

import Common (
  Context (Context, ctxReduceStack),
  hasCtxNotifSender,
 )
import Cursor
import Data.Foldable (toList)
import Data.Maybe (catMaybes, fromJust, isJust, listToMaybe)
import Exception (throwErrSt)
import Path
import Reduce.Nodes (
  close,
  reduceBlock,
  reduceCompreh,
  reduceDisj,
  reduceDisjOp,
  reduceInterpolation,
  reduceList,
 )
import qualified Reduce.Notif as Notif
import Reduce.RMonad (
  ReduceMonad,
  ReduceTCMonad,
  addToRMReadyQ,
  debugInstantRM,
  debugSpanRM,
  debugSpanTM,
  delMutValRecvs,
  getRMContext,
  getRMGlobalVers,
  getRMNotifEnabled,
  getTMCursor,
  modifyRMContext,
  putTMCursor,
  putTMTree,
  treeDepthCheck,
 )
import Reduce.RefSys (DerefResult (DerefResult), index)
import qualified Reduce.RegOps as RegOps
import Reduce.UnifyOp (unify)
import Text.Printf (printf)
import Value

fullReduce :: (ReduceTCMonad s r m) => m ()
fullReduce = debugSpanTM "fullReduce" $ do
  tc <- getTMCursor
  r <- reduce tc
  putTMTree r
  ntc <- getTMCursor
  rtc <- Notif.drainRefSysQueue ntc
  putTMCursor rtc

-- | Reduce the tree to the lowest form.
reduce :: (ReduceMonad s r m) => TrCur -> m Tree
reduce tc = debugSpanRM "reduce" Just tc $ do
  let addr = tcCanAddr tc
  result <- reduceTCFocus tc

  notifyEnabled <- getRMNotifEnabled
  isSender <- hasCtxNotifSender addr <$> getRMContext
  -- Only notify dependents when we are not in a temporary node.
  let refAddrM = getReferableAddr addr
  if isSender && isTreeAddrAccessible addr && notifyEnabled && isJust refAddrM
    then do
      let refAddr = fromJust refAddrM
      addToRMReadyQ refAddr
    else return ()

  vers <- getRMGlobalVers
  return $ result{treeVersion = vers}

withTreeDepthLimit :: (ReduceMonad s r m) => TrCur -> m a -> m a
withTreeDepthLimit tc f = do
  let addr = tcCanAddr tc
  treeDepthCheck tc
  push addr
  r <- f
  pop

  return r
 where
  push addr = modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}

  pop = modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}

reduceTCFocus :: (ReduceMonad s r m) => TrCur -> m Tree
reduceTCFocus tc = withTreeDepthLimit tc $ do
  let orig = tcFocus tc

  r <- case treeNode orig of
    TNMutable mut@(Mutable mop _) -> do
      (r, isIterBinding) <- case mop of
        Ref ref -> do
          (DerefResult rM isIterBinding) <- index ref tc
          maybe
            (return (Nothing, False))
            ( \r -> do
                -- If the target is cyclic, and it is not used to only reduce mutable, we should return structural
                -- cycle.
                -- This handles two cases:
                -- 1. The ref had not been marked as cyclic. For example, f: {out: null | f}, the inner f.
                -- 2. The ref had been marked as cyclic. For example, reducing f when reducing the y.
                -- { f: {out: null | f },  y: f }
                if treeIsCyclic r
                  then return (Just $ mkBottomTree "structural cycle", False)
                  else do
                    res <- reduceTCFocus (r `setTCFocus` tc)
                    return (Just res, isIterBinding)
            )
            rM
        _ -> do
          r <- case mop of
            RegOp rop -> case ropOpType rop of
              InvalidOpType -> throwErrSt "invalid op type"
              UnaryOpType op -> do
                uTC <- goDownTCSegMust unaryOpTASeg tc
                a <- reduceToNonMut uTC
                RegOps.execUnaryOp op a
              BinOpType op -> do
                lTC <- goDownTCSegMust binOpLeftTASeg tc
                rTC <- goDownTCSegMust binOpRightTASeg tc
                a0 <- reduceToNonMut lTC
                a1 <- reduceToNonMut rTC
                RegOps.execRegBinOp op a0 a1 tc
              CloseFunc -> close (toList $ ropArgs rop) tc
            Compreh compreh -> do
              rM <- reduceCompreh compreh tc
              -- the result of the comprehension could be an un-reduced tree or a unification op tree.
              maybe
                (return Nothing)
                (\r -> Just <$> reduceTCFocus (r `setTCFocus` tc))
                rM
            DisjOp disjOp -> do
              rM <- reduceDisjOp False disjOp tc
              maybe
                (return Nothing)
                (\r -> Just <$> reduceTCFocus (r `setTCFocus` tc))
                rM
            UOp u -> do
              rM <- unify (toList $ ufConjuncts u) tc
              maybe
                (return Nothing)
                (\r -> Just <$> reduceTCFocus (r `setTCFocus` tc))
                rM
            Itp itp -> do
              reduceInterpolation itp tc
          return (r, False)
      setMutRes isIterBinding mut r tc
    TNBlock _ -> reduceBlock tc
    TNList l -> reduceList l tc
    TNDisj d -> reduceDisj d tc
    _ -> return orig

  -- Overwrite the treenode of the raw with the reduced tree's TreeNode to preserve tree attributes.
  return $ setTN orig (treeNode r)

setMutRes :: (ReduceMonad s r m) => Bool -> Mutable -> Maybe Tree -> TrCur -> m Tree
setMutRes isIterBinding mut rM tc = do
  let
    mutT = tcFocus tc
    addr = tcCanAddr tc

  -- If the rM is another mutable tree, we need to check if the mutval exists by trying to get it.
  r <- case listToMaybe (catMaybes [rM >>= rtrNonMut, rM]) of
    -- Result is not found.
    Nothing -> do
      -- We still remove receivers in case some refs have been reduced.
      delMutValRecvs addr
      return $ updateMutVal Nothing mutT
    Just r
      -- If the value does not have immediate references or it is an iter binding, we can just return the reduced value.
      | isMutableReducible mut || isIterBinding -> do
          -- TODO: change receivers
          return r
      | otherwise -> do
          delMutValRecvs addr
          return $ updateMutVal (Just r) mutT
  debugInstantRM "setMutRes" (printf "rM: %s, mut: %s, res: %s" (show rM) (show $ mkMutableTree mut) (show r)) tc
  return r
 where
  -- update the mutval for the mutable tree. If the mutable tree is a reference, we update the reference value and
  -- version.
  updateMutVal m mutT = case mutT of
    IsRef _ ref ->
      let
        newMut = setMutOp (Ref ref{refVers = treeVersion <$> m}) mut
       in
        setTN mutT (TNMutable $ setMutVal m newMut)
    _ -> setTN mutT (TNMutable $ setMutVal m mut)

{- | Check whether the mutator is reducible.

If the mutible tree is a reference or any of recursively true for its args, then it is not reducible.

For example, if the argument of the unify is a struct which has references as its fields, then it is reducible because
the holding block of the reference is not going to be changed.
-}
isMutableReducible :: Mutable -> Bool
isMutableReducible mut = not $ mutHasRefAsImChild mut

{- | Check whether the mutable tree has a reference as its immediate child, which means it is not a child of a container
node, such as a struct or a list.
-}
mutHasRefAsImChild :: Mutable -> Bool
mutHasRefAsImChild (MutOp (Ref _)) = True
mutHasRefAsImChild mut = any go (getMutArgs mut)
 where
  go argT = case treeNode argT of
    TNMutable mutArg -> mutHasRefAsImChild mutArg
    _ -> False

{- | Reduce the conjunct for unification.

It only returns Nothing if the ref does not locate the reference.
-}
reduceUnifyConj :: (ReduceMonad s r m) => TrCur -> m (Maybe Tree)
reduceUnifyConj tc = debugSpanRM "reduceUnifyConj" id tc $ withTreeDepthLimit tc $ do
  let orig = tcFocus tc
  case treeNode orig of
    TNMutable mut
      | MutOp (Ref ref) <- mut -> do
          (DerefResult rM _) <- index ref tc
          -- If the ref is reduced to another mutable tree, we further reduce it.
          maybe
            (return Nothing)
            (\r -> reduceUnifyConj (r `setTCFocus` tc))
            rM
      | MutOp (DisjOp disjOp) <- mut -> reduceDisjOp True disjOp tc
    _ -> return $ Just $ Cursor.tcFocus tc

-- | Reduce the tree cursor to non-mutable.
reduceToNonMut :: (ReduceMonad s r m) => TrCur -> m (Maybe Tree)
reduceToNonMut tc = do
  r <- reduce tc
  return $ rtrNonMut r
