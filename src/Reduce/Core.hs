{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Core where

import Control.Monad (foldM, when)
import Cursor
import Data.Foldable (toList)
import Data.Maybe (catMaybes, fromJust, isJust)
import Reduce.Comprehension (reduceCompreh)
import Reduce.Disjunction (reduceDisj, resolveDisjOp)
import Reduce.Monad (
  Context (..),
  RM,
  getIsReducingRC,
  getTMCursor,
  getTMVal,
  inRemoteTM,
  inSubTM,
  modifyRMContext,
  modifyTMVN,
  modifyTMVal,
  throwFatal,
  treeDepthCheck,
 )
import Reduce.Primitives (reduceList, resolveCloseFunc, resolveInterpolation)
import qualified Reduce.Primitives as Primitives
import Reduce.Recalc (recalc)
import Reduce.Reference (
  CycleDetection (..),
  DerefResult (DerefResult),
  index,
 )
import Reduce.Struct (
  handleSObjChange,
  reduceStruct,
 )
import Reduce.TraceSpan (
  debugInstantTM,
  traceSpanTM,
 )
import Reduce.Unification (ResolvedPConjuncts (..), partialReduceUnifyOp, reduceFix)
import Text.Printf (printf)
import Util.Format (msprintf)
import Value

-- | Reduce the tree to the lowest form.
reduce :: RM ()
reduce = do
  traceSpanTM "reduce" reducePureFocus
  recalc

  -- If the reduced node is a struct object, we need to handle the side effects.
  affectedAddrs <- handleSObjChange
  mapM_ (\afAddr -> inRemoteTM afAddr reduce) affectedAddrs

withValDepthLimit :: RM a -> RM a
withValDepthLimit f = do
  vc <- getTMCursor
  let addr = vcAddr vc
  treeDepthCheck vc
  push addr
  r <- f
  pop

  return r
 where
  push addr = modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = addr : stack}
  pop = modifyRMContext $ \ctx@(Context{ctxReduceStack = stack}) -> ctx{ctxReduceStack = tail stack}

reducePureFocus :: RM ()
reducePureFocus = withValDepthLimit $ do
  orig <- getTMVal

  case orig of
    -- When the node has TGen, we reduce it anyway, ignoring the tree node.
    IsValMutable mut -> reduceMutable mut
    _ -> reducePureVN

  modifyTMVal $ \t ->
    (setVN (valNode t) orig)
      { isSCyclic = isSCyclic orig || isSCyclic t
      }

reduceMutable :: SOp -> RM ()
reduceMutable (SOp mop _) = case mop of
  Ref _ -> do
    (_, isReady) <- reduceArgs reduce rtrVal
    isReducingRCs <- getIsReducingRC
    if
      | not isReady -> return ()
      | isReducingRCs -> do
          -- Since the value of the reference was populated without reducing it, we need to reduce it if there is a
          -- mutval populated.
          -- TODO: set NoValRef
          vc <- getTMCursor
          (DerefResult rM _ _ _) <- index vc
          handleRefRes rM
      | otherwise -> do
          vc <- getTMCursor
          (DerefResult rM _ cd _) <- index vc
          case cd of
            NoCycleDetected -> handleRefRes rM
            RCDetected -> do
              debugInstantTM "reduceMutable" (msprintf "detected ref cycle" [])
              -- If we are not in the reducing reference cycles, this contains two cases:
              -- 1. No oldDesp
              -- 2. OldDesp has been added but in the unfinished expression evaluation, we find a new reference cycle.
              --    But this new reference cycle should not contain new info about the SCC as they are the same SCC.
              -- we should treat the reference cycle as an incomplete result.
              handleRefRes Nothing
  RegOp rop -> do
    r <-
      case ropOpType rop of
        InvalidOpType -> throwFatal "invalid op type"
        UnaryOpType op -> do
          (as, _) <- reduceArgs reduce rtrVal
          Primitives.resolveUnaryOp op (head as)
        -- Operands of the binary operation can be incomplete.
        BinOpType op -> do
          (as, _) <- reduceArgs reduce rtrVal
          getTMCursor >>= Primitives.resolveRegBinOp op (head as) (as !! 1)
        CloseFunc -> do
          (as, _) <- reduceArgs reduceToNonMut rtrVal
          getTMCursor >>= resolveCloseFunc (catMaybes as)
    handleMutRes r False
  Itp itp -> do
    (xs, isReady) <- reduceArgs reduce rtrVal
    r <-
      if isReady
        then resolveInterpolation itp (fromJust $ sequence xs)
        else return Nothing
    handleMutRes r False
  Compreh compreh -> reduceCompreh compreh
  DisjOp _ -> do
    -- Disjunction operation can have incomplete arguments.
    (_, _) <- reduceArgs reduce rtrVal
    r <- getTMCursor >>= resolveDisjOp
    handleMutRes r True
  UOp _ -> partialReduceUnifyOp >>= handleResolvedPConjsForUnifyMut

handleRefRes :: Maybe Val -> RM ()
handleRefRes Nothing = return ()
handleRefRes (Just result) = do
  vc <- getTMCursor
  case vc of
    VCFocus (IsRef _ _) -> do
      modifyTMVN (valNode result)
      -- If the result is Fix, we need to reduce it further since the target of the reference cycles might point to
      -- self.
      case result of
        IsFix f -> reduceFix f
        _ -> return ()
      when result.isSCyclic $ modifyTMVal $ \t -> t{isSCyclic = True}
    _ -> throwFatal $ printf "handleRefRes: not a reference tree cursor, got %s" (show vc)

handleMutRes :: Maybe Val -> Bool -> RM ()
handleMutRes Nothing _ = return ()
handleMutRes (Just result) furtherReduce = do
  vc <- getTMCursor
  case vc of
    (VCFocus (IsRef _ _)) -> throwFatal "handleMutRes: tree cursor can not be a reference"
    (VCFocus (IsValMutable _)) -> do
      modifyTMVN (valNode result)
      when furtherReduce reducePureVN
    _ -> throwFatal "handleMutRes: not a mutable tree"

reducePureVN :: RM ()
reducePureVN = do
  t <- getTMVal
  case t of
    IsStruct _ -> reduceStruct
    IsList l -> reduceList l
    IsDisj d -> reduceDisj d
    IsFix f -> reduceFix f
    _ -> return ()

{- | Reduce the arguments of a mutable tree.

It writes the reduced arguments back to the mutable tree and returns the reduced tree cursor.
It also returns the reduced arguments and whether the arguments are all reduced.
-}
reduceArgs :: RM () -> (Val -> Maybe Val) -> RM ([Maybe Val], Bool)
reduceArgs reduceFunc rtr = traceSpanTM "reduceArgs" $ do
  vc <- getTMCursor
  case focus vc of
    IsValMutable mut@(SOp _ _) -> do
      reducedArgs <-
        foldM
          ( \accArgs (f, _) -> do
              r <- inSubTM f $ reduceFunc >> rtr <$> getTMVal
              return (r : accArgs)
          )
          []
          (toList $ getSOpArgs mut)

      return (reverse reducedArgs, isJust $ sequence reducedArgs)
    _ -> throwFatal "reduceArgs: not a mutable tree"

-- | Handle the resolved pending conjuncts for mutable trees.
handleResolvedPConjsForUnifyMut :: ResolvedPConjuncts -> RM ()
handleResolvedPConjsForUnifyMut IncompleteConjuncts = modifyTMVN VNNoVal
handleResolvedPConjsForUnifyMut (AtomCnstrConj ac) = modifyTMVN (VNAtomCnstr ac)
handleResolvedPConjsForUnifyMut (CompletelyResolved t) = handleMutRes (Just t) True

reduceToNonMut :: RM ()
reduceToNonMut = do
  t <- getTMVal
  case t of
    IsNoVal -> reduce
    _ -> return ()