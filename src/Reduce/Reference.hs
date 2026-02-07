{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Reference where

import Control.Monad (when)
import Control.Monad.Reader (asks)
import Cursor
import Data.Aeson (ToJSON, object, toJSON)
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import DepGraph
import Feature
import Reduce.Monad (
  RM,
  RecalcRCResult (..),
  depGraph,
  fetch,
  getRMContext,
  liftEitherRM,
  params,
  preVisitValSimple,
  putRMContext,
  throwDirty,
  throwFatal,
 )
import Reduce.TraceSpan (
  debugInstantRM,
  traceSpanRMTC,
 )
import StringIndex (ShowWTIndexer (..), TextIndex, ToJSONWTIndexer (..))
import Syntax.AST (getNodeLoc)
import Syntax.Token (Location (..))
import Text.Printf (printf)
import Value
import Value.Export.Debug (treeToFullRepString)

data DerefResult = DerefResult
  { targetValue :: Maybe Val
  , targetAddr :: Maybe ValAddr
  , cycleDetection :: CycleDetection
  , isTarBinding :: Bool
  -- ^ Whether the dereferenced value is part of a let binding.
  }
  deriving (Show)

instance ShowWTIndexer DerefResult where
  tshow DerefResult{targetValue, targetAddr, cycleDetection, isTarBinding} = do
    vStr <- tshow targetValue
    addrStr <- tshow targetAddr
    cdStr <- tshow cycleDetection
    ibStr <- tshow isTarBinding
    return $ T.pack $ printf "DR(%s, %s, %s, %s)" vStr addrStr cdStr ibStr

instance ToJSON DerefResult where
  toJSON _ = object []

instance ToJSONWTIndexer DerefResult where
  ttoJSON r = do
    vJ <- ttoJSON r.targetValue
    addrJ <- ttoJSON r.targetAddr
    cdJ <- ttoJSON r.cycleDetection
    ibJ <- ttoJSON r.isTarBinding
    return $
      object
        [ ("value", vJ)
        , ("target_addr", addrJ)
        , ("cycle_detection", cdJ)
        , ("is_in_binding", ibJ)
        ]

notFound :: DerefResult
notFound = DerefResult Nothing Nothing NoCycleDetected False

derefResFromTrCur :: VCur -> DerefResult
derefResFromTrCur vc = DerefResult (Just (focus vc)) (Just (vcAddr vc)) NoCycleDetected False

-- | Resolve the reference value.
resolveRefOrIndex :: VCur -> RM DerefResult
resolveRefOrIndex vc = case vc of
  VCFocus (IsRef _ ref) -> deref ref vc
  VCFocus (IsIndex _ indx) -> index indx vc
  _ -> return $ derefResFromTrCur vc

{- | Index the tree with the segments.

Index has the form of either "a" or "a.b.c" or "{}.b".

If the index operand is a tree node, the vc is used as the environment to evaluate the tree node.

The return value will not be another reference.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
deref :: Reference -> VCur -> RM DerefResult
deref ref vc = do
  identStr <- tshow ref.ident
  traceSpanRMTC (printf "deref: ident: %s" identStr) vc $ do
    lbM <- searchTCIdent ref.ident vc
    case lbM of
      -- Let value is an index. For example, let x = ({a:1}).a
      Just (VCFocus (IsIndex mut (InplaceIndex indexSels)), typ) | typ /= ITField -> do
        let newIndex = InplaceIndex (indexSels Seq.>< ref.selectors)
            -- build the new reference tree.
            refTC = setVCFocusMut (setOpInSOp (Index newIndex) mut) vc
        resolveRefOrIndex refTC
      Just (VCFocus lb, typ) | typ /= ITField -> do
        -- If the let value is not a reference, but a regular expression.
        -- For example, let x = {}, let x = 1 + 2
        let
          newIndex = InplaceIndex (lb Seq.<| ref.selectors)
          -- build the new reference tree.
          refTC = setVCFocusMut (withEmptyOpFrame (Index newIndex)) vc
        resolveRefOrIndex refTC

      -- Rest of the cases. For cases such as { let x = a.b, a: b: {}, c: x } where let value is a refernece, it can be
      -- handled.
      _ -> do
        lparamsM <- lparamsFromRef ref
        maybe (return notFound) (`getDstTC` vc) lparamsM

-- | TODO: the value indexed should not be another reference. It should always be resolved.
index :: InplaceIndex -> VCur -> RM DerefResult
-- in-place expression, like ({}).a, or regular functions. Notice the selector must exist.
index indx vc = traceSpanRMTC "index" vc $ do
  operandTC <- liftEitherRM $ goDownVCSegMust (mkMutArgFeature 0 False) vc
  idxFieldPathM <- concreteIndexSels indx
  let
    tarTCM = do
      reducedOperand <- rtrVal (focus operandTC)
      -- Use the vc as the environment for the reduced operand.
      let reducedTC = reducedOperand `setVCFocus` vc
      case valNode reducedOperand of
        -- If the operand evaluates to a bottom, we should return the bottom.
        VNBottom _ -> return reducedTC
        _ -> do
          idxFieldPath <- idxFieldPathM
          goDownVCAddr (fieldPathToAddr idxFieldPath) reducedTC

  maybe (return notFound) resolveRefOrIndex tarTCM

-- | Resolve the reference value path using the tree cursor and replace the focus with the resolved value.
lparamsFromRef :: Reference -> RM (Maybe LocateParams)
lparamsFromRef ref@Reference{ident} = do
  m <- concreteRefSels ref
  case m of
    Just sels -> return $ Just (LocateParams ident sels)
    Nothing -> return Nothing

-- | Get the concrete selectors from the reference.
concreteRefSels :: Reference -> RM (Maybe Selectors)
concreteRefSels (Reference{selectors}) = do
  restM <- mapM valToSel (toList selectors)
  return $ do
    rest <- sequence restM
    return $ Selectors rest

concreteIndexSels :: InplaceIndex -> RM (Maybe Selectors)
concreteIndexSels (InplaceIndex (_ Seq.:<| rest)) = do
  m <- mapM valToSel (toList rest)
  return $ Selectors <$> sequence m
concreteIndexSels _ = return Nothing

{- | Get the value pointed by the value path and the original addresses.

The env is to provide the context for the dereferencing the reference.
-}
getDstTC :: LocateParams -> VCur -> RM DerefResult
getDstTC lp env = do
  -- Make deref see the latest tree, even with unreduced nodes.
  traceSpanRMTC "getDstTC" env $ do
    lr <- locateRef lp env
    case lr of
      LRIdentNotFound err -> return (DerefResult (Just err) Nothing NoCycleDetected False)
      LRPartialFound tarIdentTC potentialTarAddr -> do
        cd <- watch (vcAddr tarIdentTC) potentialTarAddr env
        return (DerefResult Nothing (Just potentialTarAddr) cd False)
      LRRefCycle tarTC ->
        return (DerefResult (Just $ focus tarTC) (Just (vcAddr tarTC)) RCDetected False)
      LRRefFound tarIdentAddr tarTC -> do
        cd <- watch tarIdentAddr (vcAddr tarTC) env
        vM <- copyConcrete tarTC
        return $ DerefResult vM (Just (vcAddr tarTC)) cd False

{- | Watch the target address from the reference environment.

TODO: update the notification graph with the new dependency, not always insert.

Also check if any of the dependent of the current ref forms a cycle with the target address.
-}
watch :: ValAddr -> ValAddr -> VCur -> RM CycleDetection
watch tarIdentAddr tarAddr refEnv = do
  when (isNothing $ addrIsRfbAddr tarAddr) $
    throwFatal $
      printf "watch: target addr %s is not suffix-referable" (show tarAddr)
  ctx <- getRMContext
  let
    refAddr = vcAddr refEnv
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

  debugInstantRM
    "watch"
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
    refEnv
  return cd

{- | The result of getting the destination value.

The result is either an error, or the target tree cursor.
-}
type DstTC = Either Val (Maybe VCur)

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
copyConcrete :: VCur -> RM (Maybe Val)
copyConcrete tarTC = do
  -- We need to make the target immutable before returning it.
  -- 1. If the target is a mutable, then we should not return the mutable because the dependent can receive the new value
  -- if the mutable is updated.
  -- 2. If the target is a block, then we need the actual struct that it produces. However, we need to preserve the
  -- original references so that if they point to an inner scope, the values of them can be invalidated and further
  -- resolved to new fields. So there is no need to recursively make the block immutable.
  let immutTarget = setValImmutable (focus tarTC)
  r <- checkRefDef (vcAddr tarTC) (fetchAtomFromAC immutTarget)
  debugInstantRM
    "copyConcrete"
    ( const $ do
        rep <- treeToFullRepString r
        return $ printf "target concrete is %s" rep
    )
    tarTC
  case r of
    IsNoVal -> return Nothing
    _ -> return $ Just r
 where
  fetchAtomFromAC x = case x of
    IsAtomCnstr c -> mkAtomVal c.value
    _ -> x

checkRefDef :: ValAddr -> Val -> RM Val
checkRefDef tarAddr val = do
  -- Check if the referenced value has recurClose.
  let recurClose = isRecurClosed val
  hasDef <- addrHasDef tarAddr
  if hasDef || recurClose
    then markRecurClosed val
    else return val

markRecurClosed :: Val -> RM Val
markRecurClosed val = do
  utc <- preVisitValSimple (subNodes True) mark valTC
  return $ focus utc
 where
  -- Create a tree cursor based on the value.
  valTC = VCur val [(rootFeature, mkNewVal VNTop)]

  mark vc = do
    return $
      mapVCFocus
        ( \focus ->
            focus
              { isRecurClosed = True
              , valNode = case valNode focus of
                  VNStruct s -> VNStruct $ s{stcClosed = True}
                  _ -> valNode focus
              }
        )
        vc

notFoundMsg :: TextIndex -> Maybe Location -> RM String
notFoundMsg ident locM = do
  idStr <- tshow ident
  case locM of
    Nothing -> return $ printf "reference %s is not found" (show idStr)
    Just loc -> do return $ printf "reference %s is not found:\n\t%s" (show idStr) (show loc)

data LocateParams
  = -- | The first is the ident, and the second is the selectors.
    LocateParams TextIndex Selectors
  deriving (Show)

data LocateRefResult
  = LRIdentNotFound Val
  | -- | The ident and all the rest of the segments are matched.
    -- The first is the ident address.
    LRRefFound ValAddr VCur
  | -- | The ident and some of the rest of the segments are matched, but not all.
    -- It records the last matched tree cursor and the potential target address.
    LRPartialFound VCur ValAddr
  | -- | The target node and the reference forms a cycle, which has already been detected by the notification graph.
    LRRefCycle VCur
  deriving (Show)

{- | Locate the node in the lowest ancestor tree by given reference path.

The path must start with a locatable ident.
-}
locateRef :: LocateParams -> VCur -> RM LocateRefResult
locateRef (LocateParams ident sels) vc = do
  searchTCIdent ident vc >>= \case
    Nothing -> do
      errMsg <- notFoundMsg ident (getNodeLoc <$> origExpr (focus vc))
      return . LRIdentNotFound $ mkBottomVal errMsg
    Just (identTC, _) -> do
      -- The ref is non-empty, so the rest must be a valid addr.
      let
        (matchedTC, unmatchedSels) = go identTC (getSelectors sels)
        targetAddr =
          if null unmatchedSels
            then vcAddr matchedTC
            else appendValAddr (vcAddr matchedTC) (fieldPathToAddr (Selectors unmatchedSels))

      debugInstantRM "locateRef" (const $ return $ printf "fieldPath: %s, before fetch" (show sels)) vc

      -- Check if the target address is dirty.
      fetch <- asks (fetch . params)
      case addrIsSufIrred targetAddr of
        Just tSIAddr
          | RsDirty <- fetch tSIAddr -> do
              debugInstantRM
                "locateRef"
                (const $ return $ printf "target addr %s is dirty, throwDirty" (show targetAddr))
                vc
              throwDirty tSIAddr
          | RsCyclic <- fetch tSIAddr
          , -- If the target is atom, even if it is cyclic, we can still return the value.
            -- Consider {a: 1 & a}
            Just _ <- rtrAtom matchedTC.focus ->
              return $ LRRefFound (vcAddr identTC) matchedTC
          -- If the target is cyclic, we should return the ref cycle result.
          | RsCyclic <- fetch tSIAddr ->
              -- We return the ref cycle as a cycle unified with a top.
              return $
                LRRefCycle
                  ( mkNewVal (VNFix (Fix VNTop [FixSelect targetAddr] True))
                      `setVCFocus` matchedTC
                  )
        _ ->
          return $
            if null unmatchedSels
              then LRRefFound (vcAddr identTC) matchedTC
              else LRPartialFound matchedTC targetAddr
 where
  go x [] = (x, [])
  go x selectors@(sel : rs) =
    maybe
      (x, selectors)
      (`go` rs)
      (goDownVCSeg (selToTASeg sel) x)

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

data IdentType
  = ITField
  | ITLetBinding
  | ITIterBinding
  deriving (Show, Eq)

{- | Search in the tree for the first identifier that can match the name.

Searching identifiers only searches for the identifiers declared in the block, not for the identifiers added by
unification with embeddings.

Return a pair. The first is address of the identifier, the second is whether the identifier is a let binding (not
including an iteration binding).

The child value will not be propagated to the parent block. Propagation is not needed because all static fields should
already exist.

The tree cursor must at least have the root segment.
-}
searchTCIdent :: TextIndex -> VCur -> RM (Maybe (VCur, IdentType))
searchTCIdent ident = go
 where
  go :: VCur -> RM (Maybe (VCur, IdentType))
  go vc = do
    tarM <- findIdent ident vc
    debugInstantRM
      "searchTCIdent"
      ( const $ do
          identStr <- tshow ident
          addrT <- tshow (vcAddr vc)
          return $
            printf
              "searching %s, at: %s, val type: %s, found: %s"
              identStr
              (T.unpack addrT)
              (showValSymbol vc.focus)
              (show $ isJust tarM)
      )
      vc
    maybe
      ( up vc >>= \case
          Nothing -> return Nothing
          Just next -> go next
      )
      (\(identTC, typ) -> return $ Just (identTC, typ))
      tarM

  up :: VCur -> RM (Maybe VCur)
  up (VCur _ [(FeatureType RootLabelType, _)]) = return Nothing -- stop at the root.
  up utc = do
    ptc <- liftEitherRM (propUpVC utc)
    return $ Just ptc

findIdent :: TextIndex -> VCur -> RM (Maybe (VCur, IdentType))
findIdent ident vc = do
  case focus vc of
    IsStruct struct -> do
      -- If the block reduces to non-struct, then the fields are not searchable in the block. The fields have
      -- behaved like mutable argument.
      -- For example, { x: {a:1, c:d, e}, e: {a: int} | {b: int}, d:1 }
      -- - merge -> {x: {a:1, c:d} | {a:1, c:d, b:int}, d:1, e: {..}}
      -- Then when we reduce the merged value, at /x/dj0/c, it finds d in the top /.
      lf <- mkLetFeature ident Nothing
      let
        m =
          catMaybes
            [ do
                let f = mkStringFeature ident
                field <- lookupStructField ident struct
                if field.ssfAttr.lbAttrIsIdent
                  then do
                    subTC <- goDownVCSeg f vc
                    return (subTC, ITField)
                  else
                    Nothing
            , do
                subTC <- goDownVCSeg lf vc
                binding <- Map.lookup ident struct.stcBindings
                let typ = if binding.isIterVar then ITIterBinding else ITLetBinding
                return (subTC, typ)
            ]
      case m of
        [] -> return Nothing
        [x] -> return $ Just x
        (fstTC, _) : _ ->
          return $
            Just
              ( mkBottomVal (printf "multiple fields found for %s" (show ident)) `setVCFocus` fstTC
              , ITField
              )
    IsValMutable (Op (Compreh c)) -> do
      debugInstantRM
        "findIdent"
        (const $ return $ printf "search in the compreh, bindings: %s" (show c.iterBindings))
        vc
      return $ do
        v <- Map.lookup ident c.iterBindings
        return (v `setVCFocus` vc, ITIterBinding)
    _ -> return Nothing
