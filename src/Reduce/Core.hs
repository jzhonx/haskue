{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Core where

import Control.Monad (foldM, unless)
import Control.Monad.Reader.Class (asks)
import Data.Aeson (ToJSON (..), toJSON)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromJust, isJust)
import qualified Data.Sequence as Seq
import Feature (
  ValAddr (..),
  appendSeg,
  canonicalToAddr,
  emptyValAddr,
  mkObjectFeature,
  mkOpArgFeature,
  mkRegCnstrFeature,
  trimAddrToCanonical,
 )
import Reduce.Comprehension (reduceCompreh)
import Reduce.Disjunction (reduceDisj, resolveDisjOp)
import Reduce.Monad (
  Context (..),
  RM,
  createCnstr,
  getRMContext,
  params,
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
  debugInst,
  debugInstStr,
  emptySpanValue,
  traceSpanAdaptTM,
  traceSpanTermsRepTM,
 )
import Reduce.Unification (unifyVals)
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (..))
import Text.Printf (printf)
import Value
import Value.Export.Debug (
  cnstrsToTermsRep,
  defaultTermsRepOption,
  termsRepToJSONWithAddr,
  vnToStringTermsRep,
 )
import Value.Instances (mapMSeqWAddr)

-- | Reduce the tree to the lowest form.
reduce :: ValAddr -> VNode -> RM VNode
reduce addr = reduceWithInitVN addr VNoVal

withValDepthLimit :: ValAddr -> RM a -> RM a
withValDepthLimit addr f = do
  treeDepthCheck addr
  f

reduceWithInitVN :: ValAddr -> Val -> VNode -> RM VNode
reduceWithInitVN addr vn v = traceSpanTermsRepTM "reduce" addr v $ do
  debugInst
    "pre reduce"
    addr
    ( do
        store <- vStore <$> getRMContext
        ttoJSON store
    )

  v' <-
    withValDepthLimit addr $
      if hasEmptyCnstrs (constraints v)
        then do
          -- FIXME: Currently, the input vn is only used for reducing constraints. And it is actually not used.
          vn' <- reduceVN addr (value v)
          return v{value = vn', constraints = (constraints v){allResolved = True}}
        else reduceConstraintsAdapt addr v vn False reduceConstraintsSetFix

  storeVal addr v'

  debugInst
    "post reduce"
    addr
    ( do
        store <- vStore <$> getRMContext
        ttoJSON store
    )

  ctx <- getRMContext
  unless ctx.noSignalReduced $ signalReduced addr
  return v'

{- | Reduce the constraints of a value, and update the value's node and constraints with the reduced result.

The initial Val is provided as an argument.
-}
reduceConstraintsAdapt ::
  ValAddr ->
  VNode ->
  Val ->
  Bool ->
  (Bool -> Int -> ValAddr -> Val -> ConstraintsSet -> RM (Val, ConstraintsSet)) ->
  RM VNode
reduceConstraintsAdapt addr v initVN stopAfter f = do
  (vn', cnstrs') <- f stopAfter 0 addr initVN v.constraints
  return
    v
      { value = vn'
      , constraints = cnstrs'
      }

reduceConstraintsSetFix ::
  Bool -> Int -> ValAddr -> Val -> ConstraintsSet -> RM (Val, ConstraintsSet)
reduceConstraintsSetFix stopAfter count addr vn constraints = do
  (vn', constraints', info) <- traceSpanAdaptTM
    (printf "reduceConstraintsSetFix %d" count)
    addr
    (termsRepToJSONWithAddr addr vn)
    ( \(a, _, b) -> do
        aT <- tshow a
        bJ <- ttoJSON b
        return $ toJSON (aT, bJ)
    )
    $ do
      (res, staticCnstrs', dyn', info) <- reduceCnstrsInner count False addr vn constraints.static constraints.dynamic
      res' <- reduceVN addr res
      -- Update the knowledge base with the temporary result.
      debugInstStr "reduceConstraintsSetFix" addr (return "storing intermediate result")
      storeVal addr (mkValVN res')
      return (res', constraints{static = staticCnstrs', dynamic = dyn', allResolved = info.incompleteCnstrs == 0}, info)
  createCnstr <- asks (createCnstr . params)
  if
    | vn' == vn || stopAfter -> return (vn', constraints')
    | createCnstr && not (null info.atomCnstrs) && info.incompleteCnstrs > 0 ->
        return (snd $ head info.atomCnstrs, constraints')
    | otherwise -> reduceConstraintsSetFix stopAfter (count + 1) addr vn' constraints'

reduceCnstrsInner ::
  Int ->
  Bool ->
  ValAddr ->
  Val ->
  ConstraintSeq ->
  IntMap.IntMap ConstraintSeq ->
  RM (Val, ConstraintSeq, IntMap.IntMap ConstraintSeq, CnstrInfo)
reduceCnstrsInner count isEmbed addr curVN staticCnstrs dynCnstrs = traceSpanAdaptTM
  (printf "reduceCnstrsInner %d" count)
  addr
  emptySpanValue
  ( \(a, b, _, _) -> do
      aJ <- ttoJSON a
      bJ <- toJSON <$> cnstrsToTermsRep (toList b) defaultTermsRepOption
      return $ toJSON (aJ, bJ)
  )
  do
    (staticCnstrs', revPairs, info) <- foldCnstrsSeqM (reduceConstraint count curVN) addr staticCnstrs
    (dynCnstrs', revDynPairs, dynInfo) <- reduceDynCnstrs count addr curVN dynCnstrs
    vn' <- mergeReducedCnstrs (revDynPairs ++ revPairs) isEmbed addr
    return (vn', staticCnstrs', dynCnstrs', mergeCnstrInfo info dynInfo)

reduceDynCnstrs ::
  Int ->
  ValAddr ->
  Val ->
  IntMap.IntMap ConstraintSeq ->
  RM (IntMap.IntMap ConstraintSeq, [(ValAddr, Val)], CnstrInfo)
reduceDynCnstrs count addr curVN dynCnstrs = traceSpanAdaptTM
  (printf "foldDynCnstrsM %d" count)
  addr
  emptySpanValue
  (\(a, b, _) -> emptySpanValue)
  do
    (revL, revPairs, info) <-
      foldM
        ( \(acc, accL, accInfo) (i, cnstrs) -> do
            let p = addr `appendSeg` mkRegCnstrFeature i
            (cnstrs', revPairs, info) <- foldCnstrsSeqM (reduceConstraint count curVN) p cnstrs
            return
              ( (i, cnstrs') : acc
              , revPairs ++ accL
              , mergeCnstrInfo info accInfo
              )
        )
        ([], [], emptyCnstrInfo)
        (IntMap.toList dynCnstrs)
    return (IntMap.fromList revL, revPairs, info)

{- | Discover conjuncts from a **unreduced** tree node that contains conjuncts as its children.

It reduces every conjunct node it finds.
-}
reduceConstraint :: Int -> Val -> ValAddr -> Constraint -> RM (Constraint, Val, CnstrInfo)
reduceConstraint count curVN addr constraint = traceSpanAdaptTM
  (printf "reduceConstraint %d" count)
  addr
  emptySpanValue
  ( \(a, b, _) -> do
      cnstrsRep <- cnstrsToTermsRep [a] defaultTermsRepOption
      let aJ = toJSON cnstrsRep
      bJ <- ttoJSON b
      return $ toJSON (aJ, bJ)
  )
  $ case constraint of
    ValCnstr vn -> do
      return
        ( constraint
        , vn
        , case vn of
            VNoVal -> mkInCompleteCnstr
            VAtom a -> mkAtomCnstrInfo addr a
            _ -> emptyCnstrInfo
        )
    OpCnstr op -> do
      (r, c') <- reduceOp False addr curVN op
      return
        ( c'
        , r
        , case r of
            -- IsRef _ (Reference{isRefCycle = True, resolvedFullAddr = Just a}) -> mkRefCycleCnstr a
            VNoVal -> mkInCompleteCnstr
            VAtom a -> mkAtomCnstrInfo addr a
            _ -> emptyCnstrInfo
        )
    StructEmbedCnstr embedCnstrs -> case embedCnstrs of
      ValCnstr (VStruct _) Seq.:<| _ -> do
        (evn', constraints', _, info) <- reduceCnstrsInner count True addr curVN embedCnstrs IntMap.empty
        return (StructEmbedCnstr constraints', evn', info)
      _ -> do
        cnstrsRep <- cnstrsToTermsRep (toList embedCnstrs) defaultTermsRepOption
        let s = show cnstrsRep
        throwFatal $ printf "unexpected non-struct constraint in StructEmbedCnstr, constraints: %s" s

mergeReducedCnstrs :: [(ValAddr, Val)] -> Bool -> ValAddr -> RM Val
mergeReducedCnstrs revPairs isEmbed addr =
  if
    | length revPairs > 1 -> unifyVals (reverse revPairs) addr isEmbed
    | length revPairs == 1 -> return (snd $ head revPairs)
    | otherwise -> return VNoVal

foldCnstrsSeqM ::
  (ValAddr -> Constraint -> RM (Constraint, Val, CnstrInfo)) ->
  ValAddr ->
  ConstraintSeq ->
  RM (ConstraintSeq, [(ValAddr, Val)], CnstrInfo)
foldCnstrsSeqM f addr constraints =
  foldM
    ( \(accSeq, accL, accInfo) (i, c) -> do
        let p = addr `appendSeg` mkRegCnstrFeature i
        (nc, nv, info) <- f p c
        return
          ( accSeq Seq.|> nc
          , case nv of
              VNoVal -> accL
              _ -> (p, nv) : accL
          , mergeCnstrInfo info accInfo
          )
    )
    (Seq.empty, [], emptyCnstrInfo)
    (zip [0 ..] (toList constraints))

data CnstrInfo = CnstrInfo
  { atomCnstrs :: [(ValAddr, Val)]
  , incompleteCnstrs :: !Int
  , refCycles :: [ValAddr]
  }
  deriving (Show)

instance ToJSON CnstrInfo where
  toJSON info =
    let
      s :: String
      s =
        printf
          "CnstrInfo: atomCnstrs: %s, incompleteCnstrs: %d, refCycles: %s"
          (show info.atomCnstrs)
          info.incompleteCnstrs
          (show info.refCycles)
     in
      toJSON s

instance ToJSONWTIndexer CnstrInfo where
  ttoJSON info = do
    atomCnstrsStr <-
      mapM
        ( \(a, v) -> do
            aStr <- tshow a
            vStr <- vnToStringTermsRep v
            let
              s :: String
              s = printf "(%s, %s)" aStr vStr
            return s
        )
        info.atomCnstrs
    let
      s :: String
      s =
        printf
          "CnstrInfo: atomCnstrs: %s, incompleteCnstrs: %d, refCycles: %s"
          (show atomCnstrsStr)
          info.incompleteCnstrs
          (show info.refCycles)
    return $ toJSON s

emptyCnstrInfo :: CnstrInfo
emptyCnstrInfo = CnstrInfo{atomCnstrs = [], incompleteCnstrs = 0, refCycles = []}

mkAtomCnstrInfo :: ValAddr -> Atom -> CnstrInfo
mkAtomCnstrInfo addr a = emptyCnstrInfo{atomCnstrs = [(addr, VAtom a)]}

mkInCompleteCnstr :: CnstrInfo
mkInCompleteCnstr = emptyCnstrInfo{incompleteCnstrs = 1}

mkRefCycleCnstr :: ValAddr -> CnstrInfo
mkRefCycleCnstr addr = emptyCnstrInfo{refCycles = [addr]}

mergeCnstrInfo :: CnstrInfo -> CnstrInfo -> CnstrInfo
mergeCnstrInfo c1 c2 =
  CnstrInfo
    { atomCnstrs = atomCnstrs c1 ++ atomCnstrs c2
    , incompleteCnstrs = incompleteCnstrs c1 + incompleteCnstrs c2
    , refCycles = refCycles c1 ++ refCycles c2
    }

-- | Force re-reduce a mutable.
reduceOpOnce :: Bool -> Val -> ValAddr -> VNode -> RM VNode
reduceOpOnce furtherReduce curVN addr v@VNode{constraints} = do
  case v of
    _
      | not (hasEmptyCnstrs constraints) -> reduceConstraintsAdapt addr v curVN True reduceConstraintsSetFix
      | otherwise -> return v

reduceOp :: Bool -> ValAddr -> Val -> Op -> RM (Val, Constraint)
reduceOp furtherReduce addr curVN op = case op of
  Compreh compreh -> do
    r <- reduceCompreh compreh (appendSeg addr (mkObjectFeature compreh.cid)) curVN
    return (r, OpCnstr op)
  RegOp rop | ropOpType rop == CloseFunc -> do
    r <- resolveCloseFunc (toList $ ropArgs rop) addr
    return (r, OpCnstr op)
  VSelect vs -> do
    -- The base of the vselect should have a canonical address, so that we can fully reduce it.
    let baseAddr = canonicalToAddr $ trimAddrToCanonical $ appendSeg addr (mkObjectFeature vs.bvID)
    v' <- reduce baseAddr vs.base
    xs' <- mapMSeqWAddr reduce mkOpArgFeature addr (iSelectors vs)
    let vs' = vs{base = v', iSelectors = xs'}
    reduceNoUnify addr (VSelect vs')
  _ -> do
    op' <- vtmapM (applyAddrFOnVal $ reduceOpOnce False curVN) addr op
    reduceNoUnify addr op'

reduceNoUnify :: ValAddr -> Op -> RM (Val, Constraint)
reduceNoUnify addr op = case op of
  Ref ref -> do
    let (_, isReady) = retrieveArgs rtrValue op
    if not isReady
      then return (VNoVal, OpCnstr op)
      else do
        dr <- deref addr ref
        handleRefRes dr addr ref
  VSelect slct -> do
    let (_, isReady) = retrieveArgs rtrValue op
        valIsReady = isJust $ (rtrValue . value) slct.base
    if isReady && valIsReady
      then do
        tar <- select slct addr
        return (tar, OpCnstr op)
      else return (VNoVal, OpCnstr op)
  RegOp rop -> do
    let (as, _) = retrieveArgs rtrValue op
    r <-
      case ropOpType rop of
        InvalidOpType -> throwFatal "invalid op type"
        UnaryOpType opType -> Primitives.resolveUnaryOp opType (head as)
        -- Operands of the binary operation can be incomplete.
        BinOpType opType -> Primitives.resolveRegBinOp opType (head as) (as !! 1) addr
        CloseFunc -> throwFatal "should not reach here"
    return (r, OpCnstr op)
  Itp itp -> do
    let (xs, isReady) = retrieveArgs rtrValue op
    r <-
      if isReady
        then resolveInterpolation itp (fromJust $ sequence xs)
        else return VNoVal
    return (r, OpCnstr op)
  DisjOp djop -> do
    -- Disjunction operation can have incomplete arguments.
    r <- resolveDisjOp djop addr
    return (r, OpCnstr op)
  _ -> throwFatal "reduceOp: unsupported mutable op"

handleRefRes :: DerefResult -> ValAddr -> Reference -> RM (Val, Constraint)
handleRefRes DerefResult{targetValue, isIdentIterVal, targetAddr, isRefCycle} _ ref = do
  let newRef = ref{resolvedFullAddr = targetAddr, isRefCycle}
  case targetValue of
    Nothing -> return (VNoVal, OpCnstr (Ref newRef))
    Just result ->
      if isIdentIterVal
        then return (value result, ValCnstr $ value result)
        else return (value result, OpCnstr (Ref newRef))

reduceVN :: ValAddr -> Val -> RM Val
reduceVN addr v = do
  case v of
    VStruct s -> reduceStruct s addr
    VList l -> reduceList l addr
    VDisj d -> reduceDisj d addr
    _ -> return v

retrieveArgs :: (Val -> Maybe Val) -> Op -> ([Maybe Val], Bool)
retrieveArgs rtr op =
  let args =
        vtmapQ
          ( \_ vt -> do
              case vt of
                -- The immediate children of the op node can only be VNode.
                VTVNode v -> rtr (value v)
                _ -> Nothing
          )
          emptyValAddr
          op
   in (args, isJust $ sequence args)

signalReduced :: ValAddr -> RM ()
signalReduced = sendToRootRecalcQ True

signalNeedRecalc :: ValAddr -> RM ()
signalNeedRecalc = sendToRootRecalcQ False
