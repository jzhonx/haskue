{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Reference where

import Control.Monad (when)
import Cursor
import Data.Aeson (ToJSON, object, toJSON)
import Data.Foldable (toList)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isNothing)
import qualified Data.Text as T
import DepGraph
import Feature
import Reduce.Monad (
  RCResolver (..),
  RM,
  depGraph,
  getRCResolver,
  getRMContext,
  lastDerefs,
  mapRCResolver,
  modifyRMContext,
  putRMContext,
  throwFatal,
 )
import Reduce.Store (copyVal, fetchValFromStore, fetchValMust)
import Reduce.TraceSpan (
  debugInstStr,
  emptySpanValue,
  traceSpanArgsTM,
  traceSpanTM,
  traceSpanValAnyTM,
  valDebugRep,
  valDebugRepJSON,
 )
import StringIndex (ShowWTIndexer (..), TextIndex, ToJSONWTIndexer (..))
import Syntax.Token (Location (..))
import Text.Printf (printf)
import Value
import Value.Export.Debug (valToFullRepString)
import Value.Instances (pretravsVal)

data DerefResult = DerefResult
  { targetValue :: Maybe Val
  , targetAddr :: Maybe ValAddr
  , cycleDetection :: CycleDetection
  , isIdentIterVal :: Bool
  }
  deriving (Show)

instance ShowWTIndexer DerefResult where
  tshow DerefResult{targetValue, targetAddr, cycleDetection, isIdentIterVal} = do
    vStr <- tshow targetValue
    addrStr <- tshow targetAddr
    cdStr <- tshow cycleDetection
    ibStr <- tshow isIdentIterVal
    return $ T.pack $ printf "DR(%s, %s, %s, %s)" vStr addrStr cdStr ibStr

instance ToJSON DerefResult where
  toJSON _ = object []

instance ToJSONWTIndexer DerefResult where
  ttoJSON r = do
    vJ <- ttoJSON r.targetValue
    addrJ <- ttoJSON r.targetAddr
    cdJ <- ttoJSON r.cycleDetection
    ibJ <- ttoJSON r.isIdentIterVal
    return $
      object
        [ ("value", vJ)
        , ("target_addr", addrJ)
        , ("cycle_detection", cdJ)
        , ("isIdentIterVal", ibJ)
        ]

notFound :: DerefResult
notFound =
  DerefResult
    { targetValue = Nothing
    , targetAddr = Nothing
    , cycleDetection = NoCycleDetected
    , isIdentIterVal = False
    }

mkNoCycleDerefRes :: ValAddr -> Val -> DerefResult
mkNoCycleDerefRes addr v =
  DerefResult
    { targetValue = Just v
    , targetAddr = Just addr
    , cycleDetection = NoCycleDetected
    , isIdentIterVal = False
    }

{- | VSelect the tree with the segments.

VSelect has the form of either "a" or "a.b.c" or "{}.b".

If the index operand is a tree node, the vc is used as the environment to evaluate the tree node.

The return value will not be another reference.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
deref :: Reference -> ValAddr -> Val -> RM DerefResult
deref ref addr v = traceSpanArgsTM
  "deref"
  addr
  (valDebugRepJSON addr v)
  ( const $ do
      identT <- tshow ref.ident
      return $ T.unpack identT
  )
  $ do
    lparamsM <- lparamsFromRef ref
    maybe (return notFound) (`getDstVal` addr) lparamsM

-- | TODO: the value indexed should not be another reference. It should always be resolved.
select :: ValueSelect -> ValAddr -> Val -> RM (Maybe Val)
-- in-place expression, like ({}).a, or regular functions. Notice the selector must exist.
select vsel addr v = traceSpanValAnyTM "select" addr v $ do
  vsFieldPathM <- concreteVSelSels vsel
  let
    tarVM = do
      baseV <- getSubVal valueSelectFeature v
      reducedBase <- rtrVal baseV
      case reducedBase of
        -- If the operand evaluates to a bottom, we should return the bottom.
        IsBottom _ -> return reducedBase
        _ -> do
          idxFieldPath <- vsFieldPathM
          getSubValByAddr (fieldPathToAddr idxFieldPath) reducedBase

  maybe
    (return Nothing)
    -- set the target value to be immutable since the receiver value can be mutated.
    (\r -> return $ Just (setValImmutable r))
    tarVM

-- | Resolve the reference value path using the tree cursor and replace the focus with the resolved value.
lparamsFromRef :: Reference -> RM (Maybe LocateParams)
lparamsFromRef ref@Reference{resolvedIdentAddr} = do
  m <- concreteRefSels ref
  case m of
    Just sels ->
      return $
        Just
          ( LocateParams
              { identAddr = resolvedIdentAddr
              , selectors = sels
              , isIdentIterVal = ref.resolvedIdentType == ITIterBinding
              }
          )
    Nothing -> return Nothing

-- | Get the concrete selectors from the reference.
concreteRefSels :: Reference -> RM (Maybe Selectors)
concreteRefSels (Reference{selectors}) = do
  restM <- mapM valToSel (toList selectors)
  return $ do
    rest <- sequence restM
    return $ Selectors rest

concreteVSelSels :: ValueSelect -> RM (Maybe Selectors)
concreteVSelSels (ValueSelect _ xs) = do
  m <- mapM valToSel (toList xs)
  return $ Selectors <$> sequence m

{- | Get the value pointed by the value path and the original addresses.

The env is to provide the context for the dereferencing the reference.
-}
getDstVal :: LocateParams -> ValAddr -> RM DerefResult
getDstVal lp@(LocateParams identAddr _ _) addr = do
  -- Make deref see the latest tree, even with unreduced nodes.
  traceSpanTM "getDstVal" addr emptySpanValue $ do
    lr <- locateRef lp addr
    case lr of
      LRIdentNotFound err ->
        return
          (DerefResult{targetValue = Just err, targetAddr = Nothing, cycleDetection = NoCycleDetected, isIdentIterVal = False})
      LRPartialFound potentialTarAddr -> do
        cd <- watch identAddr potentialTarAddr addr
        return
          (DerefResult{targetValue = Nothing, targetAddr = Just potentialTarAddr, cycleDetection = cd, isIdentIterVal = False})
      LRIdentIsBottom potentialTarAddr identV -> do
        cd <- watch identAddr potentialTarAddr addr
        return
          ( DerefResult
              { targetValue = Just identV
              , targetAddr = Just potentialTarAddr
              , cycleDetection = cd
              , isIdentIterVal = False
              }
          )
      LRRefCycle tarAddr tarV ->
        return
          ( DerefResult
              { targetValue = Just tarV
              , targetAddr = Just tarAddr
              , cycleDetection = RCDetected
              , isIdentIterVal = False
              }
          )
      LRRefFound tarAddr isIdentIterVal tarV -> do
        cd <-
          if isIdentIterVal
            -- If the reference is an iteration variable, we can skip the cycle detection.
            then return NoCycleDetected
            else watch identAddr tarAddr addr
        vM <- copyConcrete tarAddr addr tarV
        return $ DerefResult{targetValue = vM, targetAddr = Just tarAddr, cycleDetection = cd, isIdentIterVal}

{- | Watch the target address from the reference environment.

TODO: update the notification graph with the new dependency, not always insert.

Also check if any of the dependent of the current ref forms a cycle with the target address.
-}
watch :: ValAddr -> ValAddr -> ValAddr -> RM CycleDetection
watch tarIdentAddr tarAddr refAddr = do
  when (isNothing $ addrIsRfbAddr tarAddr) $
    throwFatal $
      printf "watch: target addr %s is not suffix-referable" (show tarAddr)
  ctx <- getRMContext
  let
    tarAddrR = trimAddrToRfb tarAddr
    newG = addNewDepToNG refAddr (trimAddrToRfb tarIdentAddr, tarAddrR) (depGraph ctx)
    -- Check if the refAddr's SuffixIrreducible form is in a cyclic scc.
    -- We have to trim the refAddr to its suffix irreducible form because the reference could be mutable argument.
    -- For example, {a: b + 1, b: a - 1}. We are interested in whether b forms a cycle, not /b/fa0.
    refGrpAddrM = lookupGrpAddr (trimAddrToSufIrred refAddr) newG
  putRMContext $ ctx{depGraph = newG}

  cd <- case refGrpAddrM of
    Nothing -> throwFatal $ printf "watch: refAddr %s is not in the notification graph" (show refAddr)
    Just refGrpAddr ->
      if snd $ getGrpAddr refGrpAddr
        then return RCDetected
        else return NoCycleDetected

  debugInstStr
    "watch"
    refAddr
    ( const $ do
        tarAddrStr <- tshow tarAddrR
        refAddrStr <- tshow refAddr
        return $
          printf
            "tried to detect if tar: %s forms a cycle with %s's dependents. result: %s"
            (show tarAddrStr)
            (show refAddrStr)
            (show cd)
    )
  return cd

data CycleDetection
  = RCDetected
  | NoCycleDetected
  deriving (Show, Eq)

instance ShowWTIndexer CycleDetection where
  tshow NoCycleDetected = return "NoCycle"
  tshow RCDetected = return "RCDetected"

instance ToJSON CycleDetection where
  toJSON _ = object []

instance ToJSONWTIndexer CycleDetection where
  ttoJSON NoCycleDetected = return $ toJSON $ show NoCycleDetected
  ttoJSON RCDetected = return $ toJSON $ show RCDetected

{- | Copy the concrete value from the target cursor if the target value has already been reduced.

The tree cursor is the target cursor without the copied raw value.
-}
copyConcrete :: ValAddr -> ValAddr -> Val -> RM (Maybe Val)
copyConcrete tarAddr addr tarV = do
  v <- copyVal tarAddr addr tarV
  -- We store the last dereferenced value for the reference with the suffix irreducible address.
  storeLastDerefedVal (trimAddrToSufIrred addr) (trimAddrToRfb tarAddr) v

  -- We need to make the target immutable before returning it.
  -- 1. If the target is a mutable, then we should not return the mutable because the dependent can receive the new value
  -- if the mutable is updated.
  -- 2. If the target is a block, then we need the actual struct that it produces. However, we need to preserve the
  -- original references so that if they point to an inner scope, the values of them can be invalidated and further
  -- resolved to new fields. So there is no need to recursively make the block immutable.
  let immutTarget = setValImmutable v
  r <- checkRefDef tarAddr (fetchAtomFromAC immutTarget)
  debugInstStr
    "copyConcrete"
    addr
    ( const $ do
        rep <- valToFullRepString r
        return $ printf "target concrete is %s" rep
    )
  case r of
    IsNoVal -> return Nothing
    _ -> return $ Just r
 where
  fetchAtomFromAC x = case x of
    IsAtomCnstr c -> mkAtomVal c.value
    _ -> x

storeLastDerefedVal :: SuffixIrredAddr -> ReferableAddr -> Val -> RM ()
storeLastDerefedVal addr depAddr v = do
  m <- lastDerefs <$> getRMContext
  let depMap = Map.findWithDefault Map.empty addr m
      newDepMap = Map.insert depAddr v depMap
      newM = Map.insert addr newDepMap m
  debugInstStr
    "storeLastDerefedVal"
    (sufIrredToAddr addr)
    ( const $ do
        addrT <- tshow addr
        depAddrT <- tshow depAddr
        vT <- tshow v
        return $ printf "store last derefed val for addr: %s, depAddr: %s, val: %s" addrT depAddrT vT
    )
  modifyRMContext $ \ctx -> ctx{lastDerefs = newM}

checkRefDef :: ValAddr -> Val -> RM Val
checkRefDef tarAddr val = do
  -- Check if the referenced value has recurClose.
  let recurClose = isRecurClosed val
  hasDef <- addrHasDef tarAddr
  if hasDef || recurClose
    then return $ markRecurClosed tarAddr val
    else return val

markRecurClosed :: ValAddr -> Val -> Val
markRecurClosed = pretravsVal mark
 where
  -- Create a tree cursor based on the value.
  mark _ v =
    ( v
        { isRecurClosed = True
        , valNode = case valNode v of
            VNStruct s -> VNStruct $ s{stcClosed = True}
            _ -> valNode v
        }
    )

notFoundMsg :: TextIndex -> Maybe Location -> RM String
notFoundMsg ident locM = do
  idStr <- tshow ident
  case locM of
    Nothing -> return $ printf "reference %s is not found" (show idStr)
    Just loc -> do return $ printf "reference %s is not found:\n\t%s" (show idStr) (show loc)

data LocateParams
  = -- | The first is the ident, and the second is the selectors.
    LocateParams
    { identAddr :: ValAddr
    , selectors :: Selectors
    , isIdentIterVal :: Bool
    }
  deriving (Show)

data LocateRefResult
  = LRIdentNotFound Val
  | -- | The ident and all the rest of the segments are matched.
    -- The second address indicates whether the ident is an iteration variable.
    LRRefFound ValAddr Bool Val
  | -- | The ident is a bottom but the selectors are not empty.
    LRIdentIsBottom ValAddr Val
  | -- | The ident and some of the rest of the segments are matched, but not all.
    -- It records the last matched tree cursor and the potential target address.
    LRPartialFound ValAddr
  | -- | The target node and the reference forms a cycle, which has already been detected by the notification graph.
    -- We do not need to detect the cycle again.
    LRRefCycle ValAddr Val
  deriving (Show)

{- | Locate the node in the lowest ancestor tree by given reference path.

The path must start with a locatable ident.
-}
locateRef :: LocateParams -> ValAddr -> RM LocateRefResult
locateRef (LocateParams identAddr sels isIdentIterVal) refAddr = do
  identV <- fetchValMust "locateRef" identAddr
  -- The ref is non-empty, so the rest must be a valid addr.
  let
    (matchedAddr, _, unmatchedSels) = descend identAddr identV (getSelectors sels)
    targetAddr =
      if null unmatchedSels
        then matchedAddr
        else appendValAddr matchedAddr (fieldPathToAddr (Selectors unmatchedSels))

  debugInstStr
    "locateRef"
    refAddr
    ( const $ do
        matchedAddrT <- tshow matchedAddr
        identVT <- valDebugRep identAddr identV
        selsT <- mapM tshow (getSelectors sels)
        return $
          printf "before fetch, fieldPath: %s, matchedAddr: %s, sel: %s, identV: %s" (show sels) matchedAddrT (show selsT) identVT
    )

  targetValM <- fetchValFromStore "locateRef" targetAddr
  let matchedV = fromMaybe identV targetValM

  fetchRes <- fetch targetAddr matchedV
  case fetchRes of
    Just lr -> return lr
    Nothing -> do
      return $
        if null unmatchedSels
          then LRRefFound targetAddr isIdentIterVal matchedV
          else case identV of
            IsBottom _ -> LRIdentIsBottom targetAddr identV
            _ -> LRPartialFound targetAddr
 where
  fetch targetAddr matchedV = case addrIsSufIrred targetAddr of
    Just dep -> do
      RCResolver{stack, doneRCAddrs, resolving} <- getRCResolver
      if not resolving
        then return Nothing
        else do
          let
            -- If the dep is a sub-field of any node in the current stack, then it forms a cycle.
            depOnStack = any (\x -> isPrefix (sufIrredToAddr x) (sufIrredToAddr dep)) stack
            depIsDone = any (\x -> isPrefix (sufIrredToAddr x) (sufIrredToAddr dep)) doneRCAddrs
          if
            -- OnStack must precede fetch since at the same time all cycle nodes are dirty, which would
            -- incorrectly raise error.
            | depOnStack, Just _ <- rtrAtom matchedV -> return $ Just $ LRRefFound targetAddr False matchedV
            | depOnStack ->
                -- If the target is found on the RC stack, the target value is a Fix.
                return $
                  Just $ -- We return the ref cycle as a cycle unified with a top.
                    LRRefCycle
                      targetAddr
                      (mkNewVal (VNFix (Fix{val = VNTop, conjs = [FixSelect targetAddr], unknownExists = True})))
            -- DoneRCAddrs are still marked as dirty in the dirtSet, we have to return RsNormal to let
            -- locateRef fetch the latest value.
            | depIsDone -> return Nothing
            | otherwise ->
                do
                  debugInstStr "locateRef" refAddr (const $ return $ printf "dep %s is dirty" (show dep))
                  mapRCResolver (\rs -> rs{stack = dep : stack})
                  return $ Just $ LRRefCycle targetAddr (mkNewVal VNNoVal)
    Nothing -> return Nothing

descend :: ValAddr -> Val -> [Selector] -> (ValAddr, Val, [Selector])
descend p x [] = (p, x, [])
descend p x (sel : rs) =
  let f = selToTASeg sel
      r = getSubVal f x
   in case r of
        Nothing -> case x of
          -- If no sub val can be found, but the current value is a disjunction, we can try to find the sub val in the
          -- default disjuncts.
          IsDisj d
            | Just dft <- rtrDisjDefVal d ->
                let djF = mkDisjFeature (head d.dsjDefIndexes) in descend (appendSeg p djF) dft (sel : rs)
          _ -> (p, x, sel : rs)
        Just subX -> descend (appendSeg p f) subX rs

addrHasDef :: ValAddr -> RM Bool
addrHasDef p = do
  xs <-
    mapM
      ( \f -> case f of
          FeatureType StringLabelType -> do
            t <- tshow f
            return $ fromMaybe False $ do
              typ <- getFieldType (T.unpack t)
              return $ typ == SFTDefinition
          _ -> return False
      )
      (addrToList p)
  return $ or xs

selToIdent :: Selector -> RM TextIndex
selToIdent (StringSel s) = return s
selToIdent _ = throwFatal "invalid selector"
