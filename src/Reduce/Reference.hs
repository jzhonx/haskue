{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Reference where

import Control.Monad (when)
import Data.Aeson (ToJSON, object, toJSON)
import Data.Foldable (toList)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe, isNothing, listToMaybe)
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
import Reduce.Store (copyVTermNode, fetchComprehBindingVal, fetchValFromStore, storeLastDerefedVal)
import Reduce.TraceSpan (
  debugInstStr,
  emptySpanValue,
  traceSpanArgsTM,
  traceSpanTM,
 )
import StringIndex (ShowWTIndexer (..), TextIndex, ToJSONWTIndexer (..))
import Syntax.Token (Location (..))
import Text.Printf (printf)
import Value
import Value.Export.Debug (termsRepToJSONWithAddr, toTermsRepWithAddr, vnToFullStringTermsRep)
import Value.Instances (getSubVN, getSubVNByAddr, pretravsVT)

{- | VSelect the tree with the segments.

VSelect has the form of either "a" or "a.b.c" or "{}.b".

If the index operand is a tree node, the vc is used as the environment to evaluate the tree node.

The return value will not be another reference.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
deref :: ValAddr -> Reference -> RM DerefResult
deref addr ref = traceSpanArgsTM
  "deref"
  addr
  (termsRepToJSONWithAddr addr (Ref ref))
  ( do
      identT <- tshow ref.ident
      return $ T.unpack identT
  )
  $ do
    m <- concreteRefSels ref
    case m of
      Nothing -> return selsNotReady
      Just sels -> do
        if ref.resolvedIdentType == ITIterBinding
          then do
            vn <- fetchComprehBindingVal (fromJust ref.resolvedComprehClauseIdx) ref.ident
            let (_, tar, _) = descend fileTopValAddr vn (getSelectors sels)
            return $ mkIterVarDR tar
          else do
            let
              lparams = LocateParams{identFeat = ref.identFeat, resolvedIdentAddr = ref.resolvedIdentAddr, selectors = sels}
            getDstVal lparams addr

-- | TODO: the value indexed should not be another reference. It should always be resolved.
select :: ValueSelect -> ValAddr -> RM Val
-- in-place expression, like ({}).a, or regular functions. Notice the selector must exist.
select vsel addr = traceSpanTM "select" addr emptySpanValue $ do
  vsFieldPathM <- concreteVSelSels vsel
  let
    tarVM = do
      reducedBase <- rtrValue $ value vsel.base
      case reducedBase of
        -- If the operand evaluates to a bottom, we should return the bottom.
        VBottom _ -> return reducedBase
        _ -> do
          idxFieldPath <- vsFieldPathM
          value <$> getSubVNByAddr (fieldPathToAddr idxFieldPath) (mkValVN reducedBase)

  maybe (return VUnknown) return tarVM

data DerefResult = DerefResult
  { targetValue :: Maybe VNode
  , targetAddr :: Maybe ValAddr
  , isIdentIterVal :: Bool
  , resolvedIdentAddr :: Maybe ValAddr
  , isRefCycle :: !Bool
  }
  deriving (Show)

instance ShowWTIndexer DerefResult where
  tshow DerefResult{targetValue, targetAddr, isIdentIterVal, isRefCycle} = do
    vStr <- tshow targetValue
    addrStr <- tshow targetAddr
    ibStr <- tshow isIdentIterVal
    ircStr <- tshow isRefCycle
    return $ T.pack $ printf "DR(%s, %s, %s, %s)" vStr addrStr ibStr ircStr

instance ToJSON DerefResult where
  toJSON _ = object []

instance ToJSONWTIndexer DerefResult where
  ttoJSON r = do
    vJ <- ttoJSON r.targetValue
    addrJ <- ttoJSON r.targetAddr
    ibJ <- ttoJSON r.isIdentIterVal
    ircJ <- ttoJSON r.isRefCycle
    return $
      object
        [ ("value", vJ)
        , ("target_addr", addrJ)
        , ("isIdentIterVal", ibJ)
        , ("isRefCycle", ircJ)
        ]

selsNotReady :: DerefResult
selsNotReady =
  DerefResult
    { targetValue = Nothing
    , targetAddr = Nothing
    , resolvedIdentAddr = Nothing
    , isIdentIterVal = False
    , isRefCycle = False
    }

mkRegDR :: ValAddr -> ValAddr -> VNode -> DerefResult
mkRegDR identAddr addr v =
  DerefResult
    { targetValue = Just v
    , targetAddr = Just addr
    , resolvedIdentAddr = Just identAddr
    , isIdentIterVal = False
    , isRefCycle = False
    }

mkPartialFound :: ValAddr -> ValAddr -> DerefResult
mkPartialFound identAddr addr =
  DerefResult
    { targetValue = Nothing
    , targetAddr = Just addr
    , resolvedIdentAddr = Just identAddr
    , isIdentIterVal = False
    , isRefCycle = False
    }

mkRefCycleDR :: ValAddr -> ValAddr -> Maybe VNode -> DerefResult
mkRefCycleDR identAddr addr v =
  DerefResult
    { targetValue = v
    , targetAddr = Just addr
    , resolvedIdentAddr = Just identAddr
    , isIdentIterVal = False
    , isRefCycle = True
    }

mkIterVarDR :: VNode -> DerefResult
mkIterVarDR v =
  DerefResult
    { targetValue = Just v
    , targetAddr = Nothing
    , resolvedIdentAddr = Nothing
    , isIdentIterVal = True
    , isRefCycle = False
    }

-- | Get the concrete selectors from the reference.
concreteRefSels :: Reference -> RM (Maybe Selectors)
concreteRefSels (Reference{selectors}) = do
  restM <- mapM vnToSel (toList selectors)
  return $ do
    rest <- sequence restM
    return $ Selectors rest

concreteVSelSels :: ValueSelect -> RM (Maybe Selectors)
concreteVSelSels vs = do
  m <- mapM vnToSel (toList $ iSelectors vs)
  return $ Selectors <$> sequence m

{- | Get the value pointed by the value path and the original addresses.

The env is to provide the context for the dereferencing the reference.
-}
getDstVal :: LocateParams -> ValAddr -> RM DerefResult
getDstVal lp addr = traceSpanTM "getDstVal" addr emptySpanValue $ do
  dr <- locateRef lp addr
  case dr of
    DerefResult{targetValue = Just tarV, targetAddr = Just tarAddr} -> do
      v <- copyConcrete tarAddr addr tarV
      return $ dr{targetValue = Just v}
    _ -> return dr

data LocateParams
  = LocateParams
  { identFeat :: Feature
  , resolvedIdentAddr :: ResolvedIdentAddr
  , selectors :: Selectors
  }
  deriving (Show)

{- | Locate the node in the lowest ancestor tree by given reference path.

The path must start with a locatable ident.
-}
locateRef :: LocateParams -> ValAddr -> RM DerefResult
locateRef (LocateParams identFeat resolvedIdentAddr sels) refAddr = do
  let identAddr = case resolvedIdentAddr of
        ResolvedIdentFromTop addr -> addr
        ToTargetScopeDiff diff -> assembleIdentCanonical diff identFeat refAddr
  debugInstStr
    "locateRef"
    refAddr
    ( do
        identAddrT <- tshow identAddr
        diffT <- tshow resolvedIdentAddr
        selsT <- mapM tshow (getSelectors sels)
        return $
          printf
            "locating ref. Assembled identAddr: %s, resolvedIdentAddr: %s, selectors: %s"
            (show identAddrT)
            (show diffT)
            (show selsT)
    )
  case headSeg identAddr of
    Just seg | seg == packageFeature -> do
      let pkgFuncAddr = appendValAddr identAddr (fieldPathToAddr sels)
      resM <- fetchValFromStore "locateRef" pkgFuncAddr
      case resM of
        Just resV -> return $ mkRegDR identAddr pkgFuncAddr resV
        Nothing ->
          throwFatal $
            printf
              "locateRef: cannot find value for addr %s in package %s"
              (show pkgFuncAddr)
              (show identAddr)
    _ -> do
      identVM <- fetchValFromStore "locateRef" identAddr
      case identVM of
        Nothing -> do
          let potentialTarAddr = appendValAddr identAddr (fieldPathToAddr sels)
          rcRes <- handleRefSelforSub identAddr potentialTarAddr (mkValVN VUnknown)
          case rcRes of
            Just r -> return r
            Nothing -> do
              watch potentialTarAddr refAddr
              return $ mkPartialFound identAddr potentialTarAddr
        Just identV -> do
          -- The ref is non-empty, so the rest must be a valid addr.
          let (matchedAddr, matchedV, unmatchedSels) = descend identAddr identV (getSelectors sels)
          debugInstStr
            "locateRef"
            refAddr
            ( do
                matchedAddrT <- tshow matchedAddr
                identVT <- show <$> toTermsRepWithAddr identAddr identV
                selsT <- mapM tshow (getSelectors sels)
                unmatchedSelsT <- mapM tshow unmatchedSels
                return $
                  printf
                    "before fetch, fieldPath: %s, matchedAddr: %s, sel: %s, identV: %s, unmatchedSels: %s"
                    (show sels)
                    matchedAddrT
                    (show selsT)
                    identVT
                    (show unmatchedSelsT)
            )

          if not (null unmatchedSels)
            then do
              let potentialTarAddr = appendValAddr matchedAddr (fieldPathToAddr (Selectors unmatchedSels))
              rcRes <- handleRefSelforSub identAddr potentialTarAddr (mkValVN VUnknown)
              case rcRes of
                Just r -> return r
                Nothing -> do
                  watch potentialTarAddr refAddr
                  return case identV of
                    IsBottom _ -> mkRegDR identAddr potentialTarAddr identV
                    _ -> mkPartialFound identAddr potentialTarAddr
            else do
              rcRes <- handleRefSelforSub identAddr matchedAddr matchedV
              resolveRCRes <- resolveRCValue identAddr matchedAddr matchedV
              debugInstStr
                "locateRef"
                refAddr
                ( do
                    resolveRCResT <- tshow resolveRCRes
                    return $ printf "after handleRefSelforSub and resolveRCValue, resolveRes: %s" resolveRCResT
                )
              -- We first check if the target is self or a sub field of the self. Then handle the RC case.
              -- Notice the order matters.
              case listToMaybe $ catMaybes [rcRes, resolveRCRes] of
                -- No need to watch since the target is self or a sub field of self, or the target value is RC-resolvable
                -- which we have already watched before.
                Just lr -> return lr
                -- The target value is not RC-resolvable, we can return it directly.
                _ -> do
                  watch matchedAddr refAddr
                  return $ mkRegDR identAddr matchedAddr matchedV
 where
  handleRefSelforSub identAddr targetAddr targetV = do
    let
      -- We could be in a field, dynamic field, constraint. So we need to trim the addresses to their corresponding
      -- suffix forms to do the prefix check.
      refCanAddr = trimCanonicalToVertex $ collapseToCanonical refAddr
      targetRfbAddr = trimCanonicalToRfb $ collapseToCanonical targetAddr
      -- If the ref is a conjunct argument or a sole value of a referable feature, we can treat it as a cycle.
      refIsAConjunct = case lastSeg refAddr of
        Just seg | isFeatureConstraint seg -> True
        Just seg | isFeatureReferable seg -> True
        _ -> False

      res =
        if isPrefix (vertexToAddr refCanAddr) (rfbAddrToAddr targetRfbAddr)
          then
            let rcVal =
                  -- If we are referencing ourself as a conjunct, we can directly treat it a top.
                  -- It also handles the case like a: a & v1 | v2, where a is a conjunct in a disjunction.
                  if vertexToAddr refCanAddr == rfbAddrToAddr targetRfbAddr && refIsAConjunct
                    then case targetV of
                      -- If the target value is already an atom, we can return it. This addresses the atom constraint
                      -- case.
                      IsAtom _ -> Just targetV
                      IsBottom _ -> Just targetV
                      _ -> Just (mkValVN VTop)
                    else case targetV of
                      IsUnknown -> Nothing
                      _ -> Just targetV
             in Just $ mkRefCycleDR identAddr targetAddr rcVal
          else Nothing
    debugInstStr
      "locateRef"
      refAddr
      ( do
          refCanAddrT <- tshow refCanAddr
          targetRfbAddrT <- tshow targetRfbAddr
          targetVT <- tshow targetV
          resT <- tshow res
          return $
            printf
              "checking if target is a sub field of ref. refCanAddr: %s, targetRfbAddr: %s, refIsAConjunct: %s, targetV: %s, res: %s"
              (show refCanAddrT)
              (show targetRfbAddrT)
              (show refIsAConjunct)
              targetVT
              resT
      )
    return res

  resolveRCValue identAddr targetAddr matchedV = case addrIsVertex targetAddr of
    Just dep -> do
      RCResolver{stack, doneRCAddrs, resolving} <- getRCResolver
      if not resolving
        then return Nothing
        else do
          let
            -- If the dep is a sub-field of any node in the current stack, then it forms a cycle.
            depOnStack = any (\x -> isPrefix (vertexToAddr x) (vertexToAddr dep)) stack
            depIsDone = any (\x -> isPrefix (vertexToAddr x) (vertexToAddr dep)) doneRCAddrs
          if
            -- OnStack must precede fetch since at the same time all cycle nodes are dirty, which would
            -- incorrectly raise error.
            | depOnStack, Just _ <- rtrAtom (value matchedV) -> return $ Just $ mkRegDR identAddr targetAddr matchedV
            -- If the target is found on the RC stack, the target value is a top.
            | depOnStack -> return $ Just $ mkRefCycleDR identAddr targetAddr (Just $ mkValVN VTop)
            -- If the dep is done, we can return the value directly without watching since the value won't change anymore.
            -- DoneRCAddrs are still marked as dirty in the dirtSet, we have to return RsNormal to let
            -- locateRef fetch the latest value.
            | depIsDone -> return Nothing
            | otherwise ->
                do
                  debugInstStr "locateRef" refAddr (return $ printf "dep %s is dirty" (show dep))
                  mapRCResolver (\rs -> rs{stack = dep : stack})
                  return $ Just $ mkPartialFound identAddr targetAddr
    Nothing -> return Nothing

descend :: ValAddr -> VNode -> [Selector] -> (ValAddr, VNode, [Selector])
descend p x [] = (p, x, [])
descend p x (sel : rs) =
  let f = selToTASeg sel
      r = getSubVN f x
   in case r of
        Nothing -> case x of
          -- If no sub val can be found, but the current value is a disjunction, we can try to find the sub val in the
          -- default disjuncts.
          IsDisj d
            | Just dft <- rtrDisjDefVal d ->
                let djF = mkDisjFeature (head d.dsjDefIndexes) in descend (appendSeg p djF) (mkValVN dft) (sel : rs)
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

{- | Watch the target address from the reference environment.

TODO: update the notification graph with the new dependency, not always insert.

Also check if any of the dependent of the current ref forms a cycle with the target address.
-}
watch :: ValAddr -> ValAddr -> RM ()
watch tarAddr refAddr = do
  when (isNothing $ addrIsRfbAddr tarAddr) $
    throwFatal $
      printf "watch: target addr %s is not suffix-referable" (show tarAddr)
  let
    tarRfbAddr = trimCanonicalToRfb $ collapseToCanonical tarAddr

  ctx <- getRMContext
  let
    newG = addNewDepToNG refAddr tarRfbAddr (depGraph ctx)
    -- Check if the refAddr's SuffixIrreducible form is in a cyclic scc.
    -- We have to trim the refAddr to its canonical form because the reference could be mutable argument.
    -- For example, {a: b + 1, b: a - 1}. We are interested in whether b forms a cycle, not /b/fa0.
    refGrpAddrM = lookupGrpAddr (trimCanonicalToVertex $ collapseToCanonical refAddr) newG
  putRMContext $ ctx{depGraph = newG}

  cd <- case refGrpAddrM of
    Nothing -> throwFatal $ printf "watch: refAddr %s is not in the notification graph" (show refAddr)
    Just refGrpAddr -> return $ snd $ getGrpAddr refGrpAddr

  debugInstStr
    "watch"
    refAddr
    ( do
        tarAddrStr <- tshow tarRfbAddr
        refAddrStr <- tshow refAddr
        return $
          printf
            "tried to detect if tar: %s forms a cycle with %s's dependents. is Cyclic: %s"
            (show tarAddrStr)
            (show refAddrStr)
            (show cd)
    )

{- | Copy the concrete value from the target cursor if the target value has already been reduced.

The tree cursor is the target cursor without the copied raw value.
-}
copyConcrete :: ValAddr -> ValAddr -> VNode -> RM VNode
copyConcrete tarAddr addr tarV = do
  let vt = copyVTermNode tarAddr addr (VTVNode tarV)
  let v = vtVNodeOr id tarV vt
  -- We store the last dereferenced value for the reference with the canonical address.
  storeLastDerefedVal
    (trimCanonicalToVertex $ collapseToCanonical addr)
    (trimCanonicalToRfb $ collapseToCanonical tarAddr)
    v

  -- We need to make the target immutable before returning it.
  -- 1. If the target is a mutable, then we should not return the mutable because the dependent can receive the new value
  -- if the mutable is updated.
  -- 2. If the target is a block, then we need the actual struct that it produces. However, we need to preserve the
  -- original references so that if they point to an inner scope, the values of them can be invalidated and further
  -- resolved to new fields. So there is no need to recursively make the block immutable.
  let immutTarget = removeConstraints v
  r <- checkRefDef tarAddr immutTarget
  debugInstStr
    "copyConcrete"
    addr
    ( do
        rep <- vnToFullStringTermsRep r
        return $ printf "target concrete is %s" rep
    )
  return r

checkRefDef :: ValAddr -> VNode -> RM VNode
checkRefDef tarAddr val = do
  -- Check if the referenced value has recurClose.
  -- let recurClose = isRecurClosed val
  hasDef <- addrHasDef tarAddr
  if hasDef
    then return $ markRecurClosed tarAddr val
    else return val

markRecurClosed :: ValAddr -> VNode -> VNode
markRecurClosed topAddr topV = vtVNodeOr id topV (pretravsVT mark topAddr (VTVNode topV))
 where
  -- Create a tree cursor based on the value.
  mark _ (VTVal vn) =
    VTVal
      ( case vn of
          VStruct s -> VStruct $ s{stcClosed = True}
          _ -> vn
      )
  mark _ a = a

notFoundMsg :: TextIndex -> Maybe Location -> RM String
notFoundMsg ident locM = do
  idStr <- tshow ident
  case locM of
    Nothing -> return $ printf "reference %s is not found" (show idStr)
    Just loc -> do return $ printf "reference %s is not found:\n\t%s" (show idStr) (show loc)