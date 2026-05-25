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
  addrIsCanonical,
  appendSeg,
  canonicalToAddr,
  collapseToCanonical,
  emptyValAddr,
  mkObjectFeature,
  mkOpArgFeature,
  mkRegCnstrFeature,
 )
import Reduce.Comprehension (reduceCompreh)
import Reduce.Disjunction (reduceDisj, resolveDisjOp)
import Reduce.Monad (
  Context (..),
  RM,
  createCnstr,
  getNoSignalReduced,
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
  valToStringTermsRep,
 )
import Value.Instances (mapMSeqWAddr, pretravsVTQ)

-- | Reduce the tree to the lowest form.
reduce :: ValAddr -> VNode -> RM VNode
reduce addr vn = traceSpanTermsRepTM "reduce" addr vn $ do
  debugInst
    "pre reduce"
    addr
    ( do
        store <- vStore <$> getRMContext
        ttoJSON store
    )

  vn' <- do
    treeDepthCheck addr
    if hasEmptyCnstrs (constraints vn)
      then do
        -- FIXME: Currently, the input vn is only used for reducing constraints. And it is actually not used.
        v' <- reduceVal addr (value vn)
        return vn{value = v', constraints = (constraints vn){allResolved = True}}
      else reduceConstraints addr vn False

  storeVal addr vn'

  debugInst
    "post reduce"
    addr
    ( do
        store <- vStore <$> getRMContext
        ttoJSON store
    )

  noSignal <- getNoSignalReduced
  unless noSignal $ signalReduced addr
  return vn'

-- | Reduce the constraints of a value, and update the value's node and constraints with the reduced result.
reduceConstraints :: ValAddr -> VNode -> Bool -> RM VNode
reduceConstraints addr vn stopAfterOneIter = reduceConstraintsSetFix stopAfterOneIter 0 addr vn

-- | Reduce the constraints of a VNode when encountering VNode in reducing constraints.
reduceConstraintsInCnstrs :: ValAddr -> VNode -> RM VNode
reduceConstraintsInCnstrs addr vn@VNode{value = v, constraints} = do
  (v', staticCnstrs', dyn', info) <- reduceCnstrsInner 0 False addr constraints.static constraints.dynamic
  let
    isEqual = v' == v
    nextVersion = if isEqual then vn.version else vn.version + 1
    constraints' = constraints{static = staticCnstrs', dynamic = dyn', allResolved = info.incompleteCnstrs == 0}
    vn' = vn{value = v', constraints = constraints', version = nextVersion}

  return vn'

reduceConstraintsSetFix :: Bool -> Int -> ValAddr -> VNode -> RM VNode
reduceConstraintsSetFix stopAfterOneIter count addr vn@VNode{value = v, constraints} = do
  (v', constraints', info) <- traceSpanAdaptTM
    (printf "reduceConstraintsSetFix %d" count)
    addr
    (termsRepToJSONWithAddr addr v)
    ( \(a, b, c) -> do
        aT <- tshow a
        let
          bS :: String
          bS = printf "allResolved: %s" (show b.allResolved)
        cJ <- ttoJSON c
        return $ toJSON (aT, bS, cJ)
    )
    $ do
      (res, staticCnstrs', dyn', info) <- reduceCnstrsInner count False addr constraints.static constraints.dynamic
      res' <- reduceVal addr res
      return (res', constraints{static = staticCnstrs', dynamic = dyn', allResolved = info.incompleteCnstrs == 0}, info)
  let
    isEqual = v' == v
    nextVersion = if isEqual then vn.version else vn.version + 1
    vn' = vn{value = v', constraints = constraints', version = nextVersion}

  -- Update the knowledge base with the temporary result.
  storeVal addr vn'

  let toHandleRCInNext = not (null info.refCycles) && isJust (addrIsCanonical addr)
  createCnstr <- asks (createCnstr . params)
  if
    | isEqual || stopAfterOneIter || not toHandleRCInNext -> return vn'
    | createCnstr && not (null info.atomCnstrs) && info.incompleteCnstrs > 0 ->
        return vn'{value = snd $ head info.atomCnstrs}
    | otherwise -> reduceConstraintsSetFix stopAfterOneIter (count + 1) addr vn'

reduceCnstrsInner ::
  Int ->
  Bool ->
  ValAddr ->
  ConstraintSeq ->
  IntMap.IntMap ConstraintSeq ->
  RM (Val, ConstraintSeq, IntMap.IntMap ConstraintSeq, CnstrInfo)
reduceCnstrsInner count isEmbed addr staticCnstrs dynCnstrs = traceSpanAdaptTM
  (printf "reduceCnstrsInner %d" count)
  addr
  emptySpanValue
  ( \(a, b, _, _) -> do
      aJ <- ttoJSON a
      bJ <- toJSON <$> cnstrsToTermsRep (toList b) defaultTermsRepOption
      return $ toJSON (aJ, bJ)
  )
  do
    (staticCnstrs', revPairs, info) <- foldCnstrsSeqM (reduceConstraint count) addr staticCnstrs
    (dynCnstrs', revDynPairs, dynInfo) <- reduceDynCnstrs count addr dynCnstrs
    vn' <- mergeReducedCnstrs (revDynPairs ++ revPairs) isEmbed addr
    return (vn', staticCnstrs', dynCnstrs', mergeCnstrInfo info dynInfo)

reduceDynCnstrs ::
  Int ->
  ValAddr ->
  IntMap.IntMap ConstraintSeq ->
  RM (IntMap.IntMap ConstraintSeq, [(ValAddr, Val)], CnstrInfo)
reduceDynCnstrs count addr dynCnstrs = traceSpanAdaptTM
  (printf "foldDynCnstrsM %d" count)
  addr
  emptySpanValue
  (const emptySpanValue)
  do
    (revL, revPairs, info) <-
      foldM
        ( \(acc, accL, accInfo) (i, cnstrs) -> do
            let p = addr `appendSeg` mkRegCnstrFeature i
            (cnstrs', revPairs, info) <- foldCnstrsSeqM (reduceConstraint count) p cnstrs
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
reduceConstraint :: Int -> ValAddr -> Constraint -> RM (Constraint, Val, CnstrInfo)
reduceConstraint count addr constraint = traceSpanAdaptTM
  (printf "reduceConstraint %d" count)
  addr
  ( do
      cnstrsRep <- cnstrsToTermsRep [constraint] defaultTermsRepOption
      let aJ = toJSON cnstrsRep
      return aJ
  )
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
            VUnknown -> mkInCompleteCnstr
            VAtom a -> mkAtomCnstrInfo addr a
            _ -> emptyCnstrInfo
        )
    OpCnstr op -> do
      (r, c') <- reduceOp addr op
      let subInfo = discoverRefCyclesForOp addr c'
      return
        ( c'
        , r
        , subInfo `mergeCnstrInfo` case r of
            VUnknown -> mkInCompleteCnstr
            VAtom a -> mkAtomCnstrInfo addr a
            _ -> emptyCnstrInfo
        )
    StructEmbedCnstr embedCnstrs -> case embedCnstrs of
      ValCnstr (VStruct _) Seq.:<| _ -> do
        (evn', constraints', _, info) <- reduceCnstrsInner count True addr embedCnstrs IntMap.empty
        return (StructEmbedCnstr constraints', evn', info)
      _ -> do
        cnstrsRep <- cnstrsToTermsRep (toList embedCnstrs) defaultTermsRepOption
        let s = show cnstrsRep
        throwFatal $ printf "unexpected non-struct constraint in StructEmbedCnstr, constraints: %s" s

discoverRefCyclesForOp :: ValAddr -> Constraint -> CnstrInfo
discoverRefCyclesForOp addr (OpCnstr op) =
  pretravsVTQ
    mergeCnstrInfo
    ( \_ vt -> do
        case vt of
          VTOp (Ref Reference{isRefCycle = True, resolvedFullAddr = Just a}) -> mkRefCycleCnstr a
          _ -> emptyCnstrInfo
    )
    addr
    (VTOp op)
discoverRefCyclesForOp _ _ = emptyCnstrInfo

mergeReducedCnstrs :: [(ValAddr, Val)] -> Bool -> ValAddr -> RM Val
mergeReducedCnstrs revPairs isEmbed addr =
  if
    | length revPairs > 1 -> unifyVals (reverse revPairs) addr isEmbed
    | length revPairs == 1 -> return (snd $ head revPairs)
    | otherwise -> return VUnknown

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
              VUnknown -> accL
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
            vStr <- valToStringTermsRep v
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

reduceOp :: ValAddr -> Op -> RM (Val, Constraint)
reduceOp addr op = case op of
  Compreh compreh -> do
    (r, cph') <- reduceCompreh addr compreh
    return (r, OpCnstr (Compreh cph'))
  RegOp rop | ropOpType rop == CloseFunc -> do
    r <- resolveCloseFunc (toList $ ropArgs rop) addr
    return (r, OpCnstr op)
  VSelect vs -> do
    let baseAddr = canonicalToAddr $ collapseToCanonical $ appendSeg addr (mkObjectFeature vs.bvID)
    -- The base of the vselect should be fully reduced so that we have full info about its sub fields.
    v' <- reduce baseAddr vs.base
    xs' <- mapMSeqWAddr reduceConstraintsInCnstrs mkOpArgFeature addr (iSelectors vs)
    let vs' = vs{base = v', iSelectors = xs'}
    reduceNoUnify addr (VSelect vs')
  _ -> do
    op' <- vtmapM (applyAddrFOnVN reduceConstraintsInCnstrs) addr op
    reduceNoUnify addr op'

reduceNoUnify :: ValAddr -> Op -> RM (Val, Constraint)
reduceNoUnify addr op = case op of
  Ref ref -> do
    let (_, isReady) = retrieveArgs rtrValue op
    if not isReady
      then return (VUnknown, OpCnstr op)
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
      else return (VUnknown, OpCnstr op)
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
        else return VUnknown
    return (r, OpCnstr op)
  DisjOp djop -> do
    -- Disjunction operation can have incomplete arguments.
    r <- resolveDisjOp djop addr
    return (r, OpCnstr op)
  _ -> throwFatal "reduceOp: unsupported mutable op"

handleRefRes :: DerefResult -> ValAddr -> Reference -> RM (Val, Constraint)
handleRefRes DerefResult{targetValue, targetAddr, isRefCycle} _ ref = do
  let newRef = ref{resolvedFullAddr = targetAddr, isRefCycle}
  case targetValue of
    Nothing -> return (VUnknown, OpCnstr (Ref newRef))
    Just result -> return (value result, OpCnstr (Ref newRef))

reduceVal :: ValAddr -> Val -> RM Val
reduceVal addr v = do
  case v of
    VStruct s -> reduceStruct s addr
    VList l -> reduceList l addr
    VDisj d -> reduceDisj addr d
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
signalReduced = sendToRootRecalcQ
