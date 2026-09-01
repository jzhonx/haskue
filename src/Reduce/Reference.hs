{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Reference where

import Control.Monad (when)
import Data.Aeson (ToJSON, object, toJSON)
import Data.Foldable (toList)
import Data.Maybe (catMaybes, fromJust, fromMaybe, isNothing, listToMaybe)
import qualified Data.Text as T
import DepGraph
import EvalAddr
import Reduce.Monad (
  Context (..),
  RCResolver (..),
  RM,
  depGraph,
  getRCResolver,
  getRMContext,
  mapRCResolver,
  putRMContext,
  throwFatal,
 )
import Reduce.Store (copyVTermNode, fetchComprehBindingVal, fetchValFromStore, storeLastDerefedVersion)
import Reduce.TraceSpan (
  debugInst,
  debugInstStr,
  mkTracePreDataWithOnlyVal,
  tpvArgs,
  traceSpanNoPreRM,
  traceSpanRM,
 )
import StringIndex (ShowWTIndexer (..), TextIndex, ToJSONWTIndexer (..))
import Syntax.Token (Location (..))
import Text.Printf (printf)
import Value
import Value.Export.Debug (toTermTreeForAddr, toTermTreeJSONForAddr, vnToRecursiveTermTreeString)
import Value.Instances (getSubVN, getSubVNByAddr, pretravsVT)

{- | VSelect the tree with the segments.

VSelect has the form of either "a" or "a.b.c" or "{}.b".

If the index operand is a tree node, the vc is used as the environment to evaluate the tree node.

The return value will not be another reference.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
deref :: EvalAddr -> Reference -> RM DerefResult
deref addr ref = traceSpanRM
  "deref"
  addr
  ( do
      beforeVal <- toTermTreeJSONForAddr addr (Ref ref)
      identT <- tshow ref.ident
      return $ (mkTracePreDataWithOnlyVal beforeVal){tpvArgs = Just $ T.unpack identT}
  )
  $ do
    m <- concreteRefSels ref
    case m of
      Nothing -> return selsNotReady
      Just sels -> do
        if ref.resolvedIdentType == ITIterBinding
          then do
            vn <- fetchComprehBindingVal (fromJust ref.resolvedComprehClauseIdx) ref.ident
            (_, tarM) <- descend fileTopEvalAddr vn sels
            return $ mkIterVarDR tarM
          else do
            let
              lparams = LocateParams{identFeat = ref.identFeat, identLocator = ref.identLocator, selectors = sels}
            getDstVal lparams addr

-- | TODO: the value indexed should not be another reference. It should always be resolved.
select :: ValueSelect -> EvalAddr -> RM Val
-- in-place expression, like ({}).a, or regular functions. Notice the selector must exist.
select vsel addr = traceSpanNoPreRM "select" addr $ do
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
  , targetAddr :: Maybe EvalAddr
  , isIdentIterVal :: Bool
  , resolvedIdentAddr :: Maybe EvalAddr
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

mkRegDR :: EvalAddr -> EvalAddr -> VNode -> DerefResult
mkRegDR identAddr addr v =
  DerefResult
    { targetValue = Just v
    , targetAddr = Just addr
    , resolvedIdentAddr = Just identAddr
    , isIdentIterVal = False
    , isRefCycle = False
    }

mkPartialFound :: EvalAddr -> EvalAddr -> DerefResult
mkPartialFound identAddr addr =
  DerefResult
    { targetValue = Nothing
    , targetAddr = Just addr
    , resolvedIdentAddr = Just identAddr
    , isIdentIterVal = False
    , isRefCycle = False
    }

mkRefCycleDR :: EvalAddr -> EvalAddr -> Maybe VNode -> DerefResult
mkRefCycleDR identAddr addr v =
  DerefResult
    { targetValue = v
    , targetAddr = Just addr
    , resolvedIdentAddr = Just identAddr
    , isIdentIterVal = False
    , isRefCycle = True
    }

mkIterVarDR :: Maybe VNode -> DerefResult
mkIterVarDR v =
  DerefResult
    { targetValue = v
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
getDstVal :: LocateParams -> EvalAddr -> RM DerefResult
getDstVal lp addr = traceSpanNoPreRM "getDstVal" addr $ do
  dr <- locateRef lp addr
  case dr of
    DerefResult{targetValue = Just tarV, targetAddr = Just physicalTarAddr, resolvedIdentAddr = Just identAddr} -> do
      let logicalTarAddr = appendEvalAddr identAddr (fieldPathToAddr lp.selectors)
      v <- copyConcrete physicalTarAddr logicalTarAddr addr tarV
      return $ dr{targetValue = Just v}
    _ -> return dr

data LocateParams
  = LocateParams
  { identFeat :: Feature
  , identLocator :: IdentLocator
  , selectors :: Selectors
  }
  deriving (Show)

{- | Locate the node in the lowest ancestor tree by given reference path.

The path must start with a locatable ident.
-}
locateRef :: LocateParams -> EvalAddr -> RM DerefResult
locateRef (LocateParams identFeat identLocator sels) refAddr = do
  let identAddr = case identLocator of
        AbsoluteIdentAddr addr -> addr
        -- Comprehension-generated scopes do not have stable absolute
        -- addresses during translation. Resolve their lexical relocation now
        -- that the reference has an actual evaluator address.
        LexicalIdent (ScopeDiff diff) -> assembleIdentReduced diff identFeat refAddr
  debugInstStr "locateRef" refAddr (debugAssemble identAddr identLocator sels)
  case headSeg identAddr of
    Just seg | seg == rootToAddrSegment packageRoot -> locatePkgFunc identAddr sels
    _ -> locateRefInTree identAddr sels refAddr

-- | Locate a reference into a package-level value (head segment is the package root).
locatePkgFunc :: EvalAddr -> Selectors -> RM DerefResult
locatePkgFunc identAddr sels = do
  let pkgFuncAddr = appendEvalAddr identAddr (fieldPathToAddr sels)
  resM <- fetchValFromStore "locateRef" pkgFuncAddr
  case resM of
    Just resV -> return $ mkRegDR identAddr pkgFuncAddr resV
    Nothing -> do
      pkgFuncAddrT <- tshow pkgFuncAddr
      identAddrT <- tshow identAddr
      throwFatal $
        printf
          "locateRef: cannot find value for addr %s in package %s"
          (show pkgFuncAddrT)
          (show identAddrT)

-- | Locate the ident and the remaining selectors in a non-package tree.
locateRefInTree :: EvalAddr -> Selectors -> EvalAddr -> RM DerefResult
locateRefInTree identAddr sels refAddr = do
  rcResM <- isSelRefOrSub identAddr sels refAddr
  case rcResM of
    Just rcRes -> return rcRes
    Nothing -> do
      identVM <- fetchValFromStore "locateRef" identAddr
      case identVM of
        Nothing -> do
          -- The ident is not resolved yet
          let logicalTarAddr = appendEvalAddr identAddr (fieldPathToAddr sels)
          watch logicalTarAddr refAddr
          return (mkPartialFound identAddr logicalTarAddr)
        Just identV -> locateIdentResolved identAddr identV sels refAddr

-- | The ident is resolved; descend along the selectors against its value.
locateIdentResolved :: EvalAddr -> VNode -> Selectors -> EvalAddr -> RM DerefResult
locateIdentResolved identAddr identV sels refAddr = do
  (physicalTarAddr, matchedVM) <- descend identAddr identV sels
  case matchedVM of
    Nothing -> do
      -- Some selectors cannot be matched, we can watch the target addr and return a partial result.
      let logicalTarAddr = appendEvalAddr identAddr (fieldPathToAddr sels)
      watch logicalTarAddr refAddr
      return (mkPartialFound identAddr physicalTarAddr)
    Just matchedV -> do
      resolveRCRes <- resolveRCValue identAddr physicalTarAddr matchedV refAddr
      debugInstStr "locateRef" refAddr (debugResolve resolveRCRes)
      case resolveRCRes of
        -- No need to watch since the target is self or a sub field of self, or the target value is RC-resolvable
        -- which we have already watched before.
        Just lr -> return lr
        -- The target value is not RC-resolvable, we can return it directly.
        _ -> do
          let logicalTarAddr = appendEvalAddr identAddr (fieldPathToAddr sels)
          watch logicalTarAddr refAddr
          return $ mkRegDR identAddr physicalTarAddr matchedV

{- | If the ref references itself or a sub field of itself, treat it as a reference cycle.

We could be in a field, dynamic field, or constraint, so we trim the addresses to their
corresponding suffix forms before doing the prefix check.
-}
isSelRefOrSub :: EvalAddr -> Selectors -> EvalAddr -> RM (Maybe DerefResult)
isSelRefOrSub identAddr selectors refAddr = do
  -- We should filter out constraint segments since cycle detection should be based on dependency segments only.
  let refVertexAddr = trimReducedToVertex $ toReducedAddr refAddr
  (res, restSelsM) <- case descendSels identAddr refVertexAddr selectors of
    Just (targetAddr, selfRef, restSels) -> do
      debugInst
        "isSelRefOrSub"
        refAddr
        ( do
            store <- vStore <$> getRMContext
            ttoJSON store
        )
      let
        refNormAddr = vertexToAddr refVertexAddr
        -- If the ident is a sub field of the ref, we should start from the identAddr instead of the refAddr.
        startAddr = if isPrefix refNormAddr identAddr then identAddr else refNormAddr
        derefResCons = mkRefCycleDR identAddr targetAddr
      startVM <- fetchValFromStore "isSelRefOrSub" startAddr
      -- If the target is a self reference, no need to descend the value.
      if selfRef
        then
          let rcVal = case startVM of
                -- If the target value is already an atom, we can return it. This addresses the atom constraint
                -- case.
                Just (IsAtom _) -> startVM
                Just (IsBottom _) -> startVM
                _ -> Just (mkValVN VTop)
           in return (Just $ derefResCons rcVal, Just restSels)
        else case startVM of
          Nothing -> return (Just $ derefResCons Nothing, Just restSels)
          Just startV -> do
            (_, targetVM) <- descend startAddr startV restSels
            let rcVal = case targetVM of
                  Just IsUnknown -> Nothing
                  Just targetV -> Just targetV
                  _ -> Nothing
            return (Just $ derefResCons rcVal, Just restSels)
    _ -> return (Nothing, Nothing)

  debugInstStr
    "locateRef"
    refAddr
    ( do
        identAddrT <- tshow identAddr
        refVertexAddrT <- tshow refVertexAddr
        restSelsT <- mapM tshow restSelsM
        resT <- tshow res
        return $
          printf
            ( "checking if target is a sub field of ref."
                ++ " identAddr: %s, refVertexAddr: %s, restSels: %s, res: %s"
            )
            (show identAddrT)
            (show refVertexAddrT)
            (show restSelsT)
            resT
    )
  return res

{- | descendSels is like descend, but it operates on the segments of the address instead of the value.

The first argument is the diff between the identAddr and the refAddr.
It returns Nothing if the selectors cannot be fully matched against the segments.
It returns (the matched segments plus the remaining selectors,
              whether the target is a self reference, and the remaining selectors).
-}
descendSels :: EvalAddr -> VertexAddr -> Selectors -> Maybe (EvalAddr, Bool, Selectors)
descendSels identAddr refVertexAddr selectors
  | isPrefix identAddr refAddr = case go (addrToList (trimPrefixAddr identAddr refAddr)) (getSelectors selectors) [] of
      Just (segs, rs) -> Just (appendEvalAddr identAddr (addrFromList segs), null rs, Selectors rs)
      Nothing -> Nothing
  -- If the identAddr is a sub field of the refAddr, it is a sub-field reference.
  -- For example, a: {b: true, if b {}}
  | isPrefix (vertexToAddr refVertexAddr) identAddr =
      Just (appendEvalAddr identAddr (fieldPathToAddr selectors), False, selectors)
  | otherwise = Nothing
 where
  refAddr = vertexToAddr refVertexAddr
  -- The first argument is the diff between the identAddr and the refAddr.
  -- It returns Nothing if the selectors cannot be fully matched against the segments.
  -- It returns the matched segments plus the remaining selectors.
  go :: [AddrSegment] -> [Selector] -> [AddrSegment] -> Maybe ([AddrSegment], [Selector])
  go [] sels revAcc = Just (reverse revAcc ++ selectorsToAddrSegments (Selectors sels), sels)
  go (seg : rs) sels revAcc
    -- If the segment is a disjunction, we can treat it as a match since we can assume that the we are reducing the
    -- disjunct
    | addrSegmentTag seg == DisjTag = go rs sels revAcc
    | Just _ <- addrSegmentToFeature seg, null sels = Nothing
    | Just feature <- addrSegmentToFeature seg
    , sel : ss <- sels
    , feature == selectorToFeature sel =
        go rs ss (seg : revAcc)
    | otherwise = Nothing

{- | Check whether the target is currently being resolved by the reference-cycle resolver.

If the target forms a cycle with a node currently on the RC stack, return a cycle (or
already-reduced) result; if it has already been fully resolved, return Nothing so the caller
fetches the latest value.
-}
resolveRCValue :: EvalAddr -> EvalAddr -> VNode -> EvalAddr -> RM (Maybe DerefResult)
resolveRCValue identAddr physicalTarAddr matchedV refAddr = case addrIsVertex physicalTarAddr of
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
          | depOnStack, Just _ <- rtrAtom (value matchedV) -> return $ Just $ mkRegDR identAddr physicalTarAddr matchedV
          -- If the target is found on the RC stack, the target value is a top.
          | depOnStack -> return $ Just $ mkRefCycleDR identAddr physicalTarAddr (Just $ mkValVN VTop)
          -- If the dep is done, we can return the value directly without watching since the value won't change anymore.
          -- DoneRCAddrs are still marked as dirty in the dirtSet, we have to return RsNormal to let
          -- locateRef fetch the latest value.
          | depIsDone -> return Nothing
          | otherwise ->
              do
                debugInstStr "locateRef" refAddr (return $ printf "dep %s is dirty" (show dep))
                mapRCResolver (\rs -> rs{stack = dep : stack})
                return $ Just $ mkPartialFound identAddr physicalTarAddr
  Nothing -> return Nothing

-- | Trace message for the initial address assembly.
debugAssemble :: EvalAddr -> IdentLocator -> Selectors -> RM String
debugAssemble identAddr identLocator sels = do
  identAddrT <- tshow identAddr
  locatorT <- tshow identLocator
  selsT <- mapM tshow (getSelectors sels)
  return $
    printf
      "locating ref. Assembled identAddr: %s, identLocator: %s, selectors: %s"
      (show identAddrT)
      (show locatorT)
      (show selsT)

-- | Trace message after descending the selectors.
debugDescend :: EvalAddr -> EvalAddr -> VNode -> Selectors -> [Selector] -> RM String
debugDescend startAddr matchedAddr startV sels unmatchedSels = do
  matchedAddrT <- tshow matchedAddr
  startVT <- show <$> toTermTreeForAddr startAddr startV
  selsT <- mapM tshow (getSelectors sels)
  unmatchedSelsT <- mapM tshow unmatchedSels
  return $
    printf
      "before fetch, fieldPath: %s, matchedAddr: %s, sel: %s, startV: %s, unmatchedSels: %s"
      (show sels)
      matchedAddrT
      (show selsT)
      startVT
      (show unmatchedSelsT)

-- | Trace message after the RC checks.
debugResolve :: Maybe DerefResult -> RM String
debugResolve resolveRCRes = do
  resolveRCResT <- tshow resolveRCRes
  return $ printf "after isSelRefOrSub and resolveRCValue, resolveRes: %s" resolveRCResT

descend :: EvalAddr -> VNode -> Selectors -> RM (EvalAddr, Maybe VNode)
descend startAddr start selectors = do
  let (matchedAddr, matchedV, unmatchedSels) = go startAddr start (getSelectors selectors)
  debugInstStr "descend" startAddr (debugDescend startAddr matchedAddr start selectors unmatchedSels)
  if null unmatchedSels
    then return (matchedAddr, Just matchedV)
    else return (appendEvalAddr matchedAddr (fieldPathToAddr (Selectors unmatchedSels)), Nothing)
 where
  go :: EvalAddr -> VNode -> [Selector] -> (EvalAddr, VNode, [Selector])
  go p x [] = (p, x, [])
  go p x (sel : rs) =
    let feature = selectorToFeature sel
        r = getSubVN (featureToAddrSegment feature) x
     in case r of
          Nothing -> case x of
            -- If no sub val can be found, but the current value is a disjunction, we can try to find the sub val in the
            -- default disjuncts.
            IsDisj d
              | Just dft <- rtrDisjDefVal d ->
                  let djStep = mkDisjTermStep (head d.dsjDefIndexes)
                   in go (appendTermStep p djStep) (mkValVN dft) (sel : rs)
            _ -> (p, x, sel : rs)
          Just subX -> go (appendFeature p feature) subX rs

addrHasDef :: EvalAddr -> RM Bool
addrHasDef p = do
  xs <-
    mapM
      ( \seg -> case addrSegmentToFeature seg of
          Just feature | featureTag feature == StringTag -> do
            t <- tshow feature
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
watch :: EvalAddr -> EvalAddr -> RM ()
watch tarAddr refAddr = do
  when (isNothing $ addrIsDependency tarAddr) $
    throwFatal $
      printf "watch: target addr %s is not a dependency address" (show tarAddr)
  let
    targetDependencyAddr = trimReducedToDependency $ toReducedAddr tarAddr
    refVertexAddr = trimReducedToVertex $ toReducedAddr refAddr

  when (isPrefix (vertexToAddr refVertexAddr) (dependencyToAddr targetDependencyAddr)) $ do
    refVertexAddrT <- tshow refVertexAddr
    targetDependencyAddrT <- tshow targetDependencyAddr
    throwFatal $
      printf
        "watch: target addr %s is a sub field of ref addr %s, should not watch to avoid a self-dependency"
        targetDependencyAddrT
        refVertexAddrT

  ctx <- getRMContext
  let
    newG = addNewDepToNG refAddr targetDependencyAddr (depGraph ctx)
    -- Check if the refAddr's SuffixIrreducible form is in a cyclic scc.
    -- We have to convert refAddr to its reduced form because the reference could be a mutable argument.
    -- For example, {a: b + 1, b: a - 1}. We are interested in whether b forms a cycle, not /b/fa0.
    refGroupM = lookupDepGroup (trimReducedToVertex $ toReducedAddr refAddr) newG
  putRMContext $ ctx{depGraph = newG}

  cd <- case refGroupM of
    Nothing -> throwFatal $ printf "watch: refAddr %s is not in the notification graph" (show refAddr)
    Just refGroup -> return refGroup.depGroupIsCyclic

  debugInstStr
    "watch"
    refAddr
    ( do
        tarAddrStr <- tshow targetDependencyAddr
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
copyConcrete :: EvalAddr -> EvalAddr -> EvalAddr -> VNode -> RM VNode
copyConcrete physicalTarAddr logicalTarAddr addr tarV = do
  let vt = copyVTermNode physicalTarAddr addr (VTVNode tarV)
  let v = vtVNodeOr id tarV vt
  -- Dependency edges use the logical address assembled from the resolved
  -- identifier and selectors, so version bookkeeping must use the same key.
  -- The physical target may contain internal disjunction steps that are not
  -- present in that dependency address.
  storeLastDerefedVersion
    (trimReducedToVertex $ toReducedAddr addr)
    (trimReducedToDependency $ toReducedAddr logicalTarAddr)
    v

  -- We need to make the target immutable before returning it.
  -- 1. If the target is a mutable, then we should not return the mutable because the dependent can receive the new value
  -- if the mutable is updated.
  -- 2. If the target is a block, then we need the actual struct that it produces. However, we need to preserve the
  -- original references so that if they point to an inner scope, the values of them can be invalidated and further
  -- resolved to new fields. So there is no need to recursively make the block immutable.
  let immutTarget = removeConstraints v
  r <- checkRefDef physicalTarAddr immutTarget
  debugInstStr
    "copyConcrete"
    addr
    ( do
        rep <- vnToRecursiveTermTreeString r
        return $ printf "target concrete is %s" rep
    )
  return r

checkRefDef :: EvalAddr -> VNode -> RM VNode
checkRefDef tarAddr val = do
  -- Check if the referenced value has recurClose.
  -- let recurClose = isRecurClosed val
  hasDef <- addrHasDef tarAddr
  if hasDef
    then return $ markRecurClosed tarAddr val
    else return val

markRecurClosed :: EvalAddr -> VNode -> VNode
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
