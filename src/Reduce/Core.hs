{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Core where

import Control.Monad (unless)
import Data.Foldable (toList)
import Data.Maybe (fromJust, isJust)
import Feature (ValAddr, emptyValAddr)
import Reduce.Comprehension (reduceCompreh)
import Reduce.Disjunction (reduceDisj, resolveDisjOp)
import Reduce.Monad (
  Context (..),
  RM,
  getRMContext,
  throwFatal,
  treeDepthCheck,
 )
import Reduce.Primitives (reduceList, resolveCloseFunc, resolveInterpolation)
import qualified Reduce.Primitives as Primitives
import Reduce.Recalc (sendToRootRecalcQ)
import Reduce.Reference (
  DerefResult (..),
  deref,
  select,
 )
import Reduce.Store (storeVal)
import Reduce.Struct (
  reduceStruct,
 )
import Reduce.TraceSpan (
  debugInstJV,
  traceSpanValTM,
 )
import Reduce.Unification (ResolvedPConjuncts (..), partialReduceUnifyOp, reduceFix)
import StringIndex (ToJSONWTIndexer (..))
import Text.Printf (printf)
import Value

-- | Reduce the tree to the lowest form.
reduce :: ValAddr -> Val -> RM Val
reduce addr v = traceSpanValTM "reduce" addr v $ do
  debugInstJV
    "pre reduce"
    addr
    ( do
        store <- vStore <$> getRMContext
        ttoJSON store
    )

  v' <- reducePure addr v
  storeVal addr v'

  debugInstJV
    "post reduce"
    addr
    ( do
        store <- vStore <$> getRMContext
        ttoJSON store
    )

  ctx <- getRMContext
  unless ctx.noSignalReduced $ signalReduced addr
  return v'

withValDepthLimit :: ValAddr -> RM a -> RM a
withValDepthLimit addr f = do
  treeDepthCheck addr
  f

reducePure :: ValAddr -> Val -> RM Val
reducePure addr v = withValDepthLimit addr $ do
  case v of
    IsValMutable mut -> reduceMutable mut True addr v
    _ -> reducePureVN addr v

-- | Force re-reduce a mutable.
forceReduceMut :: Bool -> ValAddr -> Val -> RM Val
forceReduceMut furtherReduce addr v = do
  case v of
    IsValMutable mut -> reduceMutable mut furtherReduce addr v
    _ -> return v

reduceMutable :: SOp -> Bool -> ValAddr -> Val -> RM Val
reduceMutable sop@(SOp op _) furtherReduce addr v = case op of
  UOp uop -> do
    (udpuop, rtype) <- partialReduceUnifyOp uop addr v
    let updsop = setOpInSOp (UOp udpuop) sop
    case rtype of
      IncompleteConjuncts -> return $ v{valNode = VNNoVal, op = Just updsop}
      AtomCnstrConj r -> return $ v{valNode = valNode r, op = Just updsop}
      CompletelyResolved r -> handleMutRes (Just r) furtherReduce updsop addr v
  Compreh compreh -> do
    r <- reduceCompreh compreh addr v
    handleMutRes (Just r) furtherReduce sop addr v
  RegOp rop | ropOpType rop == CloseFunc -> do
    r <- resolveCloseFunc (toList $ ropArgs rop) v addr
    handleMutRes (Just r) furtherReduce sop addr v
  VSelect _ -> do
    updop <- vtmapM reduce addr op
    let updsop = setOpInSOp updop sop
    reduceNoUnify updsop addr (setTOp updsop v)
  _ -> do
    updop <- vtmapM (forceReduceMut False) addr op
    let updsop = setOpInSOp updop sop
    reduceNoUnify updsop addr (setTOp updsop v)

reduceNoUnify :: SOp -> ValAddr -> Val -> RM Val
reduceNoUnify sop@(SOp op _) addr v = case op of
  Ref ref -> do
    let (_, isReady) = retrieveArgs rtrVal sop
    if not isReady
      then return v
      else do
        dr <- deref ref addr v
        handleRefRes dr addr v
  VSelect slct -> do
    let (_, isReady) = retrieveArgs rtrVal sop
        valIsReady = isJust $ rtrVal slct.base
    if isReady && valIsReady
      then do
        tar <- select slct addr v
        handleMutRes tar False sop addr v
      else return v
  RegOp rop -> do
    let (as, _) = retrieveArgs rtrVal sop
    r <-
      case ropOpType rop of
        InvalidOpType -> throwFatal "invalid op type"
        UnaryOpType opType -> Primitives.resolveUnaryOp opType (head as)
        -- Operands of the binary operation can be incomplete.
        BinOpType opType -> Primitives.resolveRegBinOp opType (head as) (as !! 1) addr
        CloseFunc -> throwFatal "should not reach here"
    handleMutRes r False sop addr v
  Itp itp -> do
    let (xs, isReady) = retrieveArgs rtrVal sop
    r <-
      if isReady
        then resolveInterpolation itp (fromJust $ sequence xs)
        else return Nothing
    handleMutRes r False sop addr v
  DisjOp djop -> do
    -- Disjunction operation can have incomplete arguments.
    r <- resolveDisjOp djop addr v
    handleMutRes r True sop addr v
  _ -> throwFatal "reduceMutable: unsupported mutable op"

handleRefRes :: DerefResult -> ValAddr -> Val -> RM Val
handleRefRes DerefResult{targetValue = Nothing} _ v = case v of
  -- The result is not found
  IsRef _ _ -> return $ setVN VNNoVal v
  _ -> throwFatal $ printf "handleRefRes: not a reference tree, got %s" (show v)
handleRefRes DerefResult{targetValue = Just result, isIdentIterVal} addr v = do
  case v of
    (IsRef _ _) -> do
      let nv = if isIdentIterVal then result else setVN (valNode result) v
      -- If the result is Fix, we need to reduce it further since the target of the reference cycles might point to
      -- self.
      case result of
        IsFix f -> reduceFix f addr nv
        _ -> return nv
    _ -> throwFatal $ printf "handleRefRes: not a reference tree, got %s" (show v)

handleMutRes :: Maybe Val -> Bool -> SOp -> ValAddr -> Val -> RM Val
handleMutRes Nothing _ sop _ v = return $ v{valNode = VNNoVal, op = Just sop}
handleMutRes (Just result) furtherReduce sop addr v = traceSpanValTM "handleMutRes" addr v $ do
  case v of
    IsRef _ _ -> throwFatal "handleMutRes: tree cursor can not be a reference"
    IsValMutable _ -> do
      let nv = v{valNode = valNode result, op = Just sop}
      if furtherReduce
        then do
          r <- reducePureVN addr nv
          return $ setTOp sop r
        else return nv
    _ -> throwFatal "handleMutRes: not a mutable tree"

reducePureVN :: ValAddr -> Val -> RM Val
reducePureVN addr v = do
  case v of
    IsStruct _ -> reduceStruct addr v
    IsList l -> reduceList l addr v
    IsDisj d -> reduceDisj d addr v
    IsFix f -> reduceFix f addr v
    _ -> return v

retrieveArgs :: (Val -> Maybe Val) -> SOp -> ([Maybe Val], Bool)
retrieveArgs rtr op = let args = vtmapQ (\_ v -> rtr v) emptyValAddr op in (args, isJust $ sequence args)

signalReduced :: ValAddr -> RM ()
signalReduced = sendToRootRecalcQ True

signalNeedRecalc :: ValAddr -> RM ()
signalNeedRecalc = sendToRootRecalcQ False
