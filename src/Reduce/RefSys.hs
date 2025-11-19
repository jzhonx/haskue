{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RefSys where

import qualified AST
import Control.Monad (when)
import Control.Monad.Reader (asks)
import Cursor
import Data.Aeson (ToJSON, object, toJSON)
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, isNothing)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Feature
import PropGraph
import Reduce.RMonad (
  RM,
  RecalcRCResult (..),
  ctxPropGraph,
  debugInstantRM,
  fetch,
  getRMContext,
  liftEitherRM,
  markRMLetReferred,
  params,
  preVisitTreeSimple,
  putRMContext,
  throwDirty,
  throwFatal,
  traceSpanRMTC,
 )
import StringIndex (ShowWTIndexer (..), TextIndex, TextIndexerMonad, ToJSONWTIndexer (..))
import Text.Printf (printf)
import Value
import Value.Util.TreeRep (treeToFullRepString)

data DerefResult = DerefResult
  { drValue :: Maybe Tree
  , drTargetAddr :: Maybe TreeAddr
  , drCycleDetection :: CycleDetection
  , drIsInBinding :: Bool
  -- ^ Whether the dereferenced value is part of a let binding.
  }
  deriving (Show)

instance ShowWTIndexer DerefResult where
  tshow DerefResult{drValue, drTargetAddr, drCycleDetection, drIsInBinding} = do
    vStr <- tshow drValue
    addrStr <- tshow drTargetAddr
    cdStr <- tshow drCycleDetection
    ibStr <- tshow drIsInBinding
    return $ T.pack $ printf "DR(%s, %s, %s, %s)" vStr addrStr cdStr ibStr

instance ToJSON DerefResult where
  toJSON _ = object []

instance ToJSONWTIndexer DerefResult where
  ttoJSON r = do
    vJ <- ttoJSON r.drValue
    addrJ <- ttoJSON r.drTargetAddr
    cdJ <- ttoJSON r.drCycleDetection
    ibJ <- ttoJSON r.drIsInBinding
    return $
      object
        [ ("value", vJ)
        , ("target_addr", addrJ)
        , ("cycle_detection", cdJ)
        , ("is_in_binding", ibJ)
        ]

notFound :: DerefResult
notFound = DerefResult Nothing Nothing NoCycleDetected False

derefResFromTrCur :: TrCur -> DerefResult
derefResFromTrCur tc = DerefResult (Just (tcFocus tc)) (Just (tcAddr tc)) NoCycleDetected False

-- | Resolve the reference value.
resolveTCIfRef :: TrCur -> RM DerefResult
resolveTCIfRef tc = case tc of
  TCFocus (IsRef _ _) -> index tc
  _ -> return $ derefResFromTrCur tc

{- | Index the tree with the segments.

Index has the form of either "a" or "a.b.c" or "{}.b".

If the index operand is a tree node, the tc is used as the environment to evaluate the tree node.

The return value will not be another reference.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
index :: TrCur -> RM DerefResult
index tc@(TCFocus (IsRef _ argRef@Reference{refArg = (RefPath ident sels)})) = do
  identStr <- tshow ident
  traceSpanRMTC (printf "index: ident: %s" identStr) tc $ do
    lbM <- searchTCIdent False ident tc
    case lbM of
      Just (TCFocus (IsRef mut rf), typ)
        -- Let value is an index. For example, let x = ({a:1}).a
        | Just segs <- getIndexSegs rf
        , typ /= ITField -> do
            let newRef = mkIndexRef (segs Seq.>< sels)
                -- build the new reference tree.
                refTC = setTCFocusMut (setOpInSOp (Ref newRef) mut) tc
            resolveTCIfRef refTC
      Just (TCFocus lb, typ) | typ /= ITField -> do
        -- If the let value is not a reference, but a regular expression.
        -- For example, let x = {}, let x = 1 + 2
        let
          newRef = mkIndexRef (lb Seq.<| sels)
          -- build the new reference tree.
          refTC = setTCFocusMut (withEmptyOpFrame (Ref newRef)) tc
        resolveTCIfRef refTC

      -- Rest of the cases. For cases such as { let x = a.b, a: b: {}, c: x } where let value is a refernece, it can be
      -- handled.
      _ -> do
        refTCM <- refTCFromRef argRef tc
        maybe
          (return notFound)
          ( \(refTC, newRefFieldPath) -> getDstTC newRefFieldPath refTC
          )
          refTCM

-- in-place expression, like ({}).a, or regular functions. Notice the selector must exist.
index tc@(TCFocus (IsRef _ Reference{refArg = arg@(RefIndex _)})) = traceSpanRMTC "index" tc $ do
  operandTC <- liftEitherRM $ goDownTCSegMust (mkMutArgFeature 0 False) tc
  idxFieldPathM <- convertRefArgTreesToSels arg
  let
    reducedOperandM = rtrVal (tcFocus operandTC)
    tarTCM = do
      idxFieldPath <- idxFieldPathM
      reducedOperand <- reducedOperandM
      -- Use the tc as the environment for the reduced operand.
      let reducedTC = reducedOperand `setTCFocus` tc
      case treeNode reducedOperand of
        -- If the operand evaluates to a bottom, we should return the bottom.
        TNBottom _ -> return reducedTC
        _ -> goDownTCAddr (fieldPathToAddr idxFieldPath) reducedTC

  maybe (return notFound) resolveTCIfRef tarTCM
index tc = throwFatal $ printf "index: invalid tree cursor %s" (show tc)

-- | Resolve the reference value path using the tree cursor and replace the focus with the resolved value.
refTCFromRef :: Reference -> TrCur -> RM (Maybe (TrCur, FieldPath))
refTCFromRef Reference{refArg = arg@(RefPath ident _)} tc = do
  m <- convertRefArgTreesToSels arg
  maybe
    (return Nothing)
    ( \fp@(FieldPath reducedSels) -> do
        newRef <- mkRefFromFieldPath mkAtomTree ident (FieldPath (tail reducedSels))
        -- build the new reference tree.
        let refTC = setTCFocusMut (withEmptyOpFrame (Ref newRef)) tc
        return $ Just (refTC, fp)
    )
    m
refTCFromRef _ _ = throwFatal "refTCFromRef: invalid reference"

mkRefFromFieldPath :: (TextIndexerMonad s m) => (Atom -> Tree) -> TextIndex -> FieldPath -> m Reference
mkRefFromFieldPath aToTree ident (FieldPath xs) = do
  ys <-
    mapM
      ( \y -> case y of
          StringSel s -> do
            str <- tshow s
            return $ aToTree (String str)
          IntSel i -> return $ aToTree (Int $ fromIntegral i)
      )
      xs
  return $
    Reference
      { refArg = RefPath ident (Seq.fromList ys)
      }

{- | Convert the reference argument trees to selectors.

Notice that even if the selector tree is concrete, it might not be valid selector. It could be a disjunction.
-}
convertRefArgTreesToSels :: RefArg -> RM (Maybe FieldPath)
convertRefArgTreesToSels arg = case arg of
  (RefPath ident sels) -> do
    restM <- mapM treeToSel (toList sels)
    return $ do
      let h = StringSel ident
      rest <- sequence restM
      return $ FieldPath (h : rest)
  (RefIndex (_ Seq.:<| rest)) -> do
    m <- mapM treeToSel (toList rest)
    return $ FieldPath <$> sequence m
  _ -> return Nothing

{- | Get the value pointed by the value path and the original addresses.

The env is to provide the context for the dereferencing the reference.
-}
getDstTC :: FieldPath -> TrCur -> RM DerefResult
getDstTC fieldPath env = do
  -- Make deref see the latest tree, even with unreduced nodes.
  traceSpanRMTC "getDstTC" env $ do
    lr <- locateRef fieldPath env
    case lr of
      LRIdentNotFound err -> return (DerefResult (Just err) Nothing NoCycleDetected False)
      LRPartialFound tarIdentTC potentialTarAddr -> do
        cd <- watch (tcAddr tarIdentTC) potentialTarAddr env
        return (DerefResult Nothing (Just potentialTarAddr) cd False)
      LRRefCycle tarTC ->
        return (DerefResult (Just $ tcFocus tarTC) (Just (tcAddr tarTC)) RCDetected False)
      LRRefFound tarIdentAddr tarTC -> do
        cd <- watch tarIdentAddr (tcAddr tarTC) env
        vM <- copyConcrete tarTC
        return $ DerefResult vM (Just (tcAddr tarTC)) cd False

{- | Watch the target address from the reference environment.

TODO: update the notification graph with the new dependency, not always insert.

Also check if any of the dependent of the current ref forms a cycle with the target address.
-}
watch :: TreeAddr -> TreeAddr -> TrCur -> RM CycleDetection
watch tarIdentAddr tarAddr refEnv = do
  when (isNothing $ addrIsRfbAddr tarAddr) $
    throwFatal $
      printf "watch: target addr %s is not suffix-referable" (show tarAddr)
  ctx <- getRMContext
  let
    refAddr = tcAddr refEnv
    tarAddrR = trimAddrToRfb tarAddr
    newG = addNewDepToNG refAddr (trimAddrToRfb tarIdentAddr, tarAddrR) (ctxPropGraph ctx)
    -- Check if the refAddr's SuffixIrreducible form is in a cyclic scc.
    -- We have to trim the refAddr to its suffix irreducible form because the reference could be mutable argument.
    -- For example, {a: b + 1, b: a - 1}. We are interested in whether b forms a cycle, not /b/fa0.
    refGrpAddrM = lookupGrpAddr (trimAddrToSufIrred refAddr) newG
  putRMContext $ ctx{ctxPropGraph = newG}

  cd <- case refGrpAddrM of
    Nothing -> throwFatal $ printf "watch: refAddr %s is not in the notification graph" (show refAddr)
    Just refGrpAddr ->
      if snd $ getGrpAddr refGrpAddr
        then return RCDetected
        else return NoCycleDetected

  tarAddrStr <- tshow tarAddrR
  refAddrStr <- tshow refAddr
  debugInstantRM
    "watch"
    ( printf
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
type DstTC = Either Tree (Maybe TrCur)

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

{- | Mark the value and all its descendants as cyclic.

We have to mark all descendants as cyclic here instead of just marking the focus because if the value is a struct and
it is immediately unified with a non-cyclic value, the descendants of the merged value, which does not have the
cyclic attribute, would lose the cyclic attribute.
-}
markCyclic :: Tree -> RM Tree
markCyclic val = do
  utc <- preVisitTreeSimple (subNodes False) mark valTC
  return $ tcFocus utc
 where
  -- Create a tree cursor based on the value.
  valTC = TrCur val [(rootFeature, mkNewTree TNTop)]

  mark :: TrCur -> RM TrCur
  mark tc = do
    let focus = tcFocus tc
    return $ focus{isSCyclic = True} `setTCFocus` tc

{- | Copy the concrete value from the target cursor if the target value has already been reduced.

The tree cursor is the target cursor without the copied raw value.
-}
copyConcrete :: TrCur -> RM (Maybe Tree)
copyConcrete tarTC = do
  -- We need to make the target immutable before returning it.
  -- 1. If the target is a mutable, then we should not return the mutable because the dependent can receive the new value
  -- if the mutable is updated.
  -- 2. If the target is a block, then we need the actual struct that it produces. However, we need to preserve the
  -- original references so that if they point to an inner scope, the values of them can be invalidated and further
  -- resolved to new fields. So there is no need to recursively make the block immutable.
  let immutTarget = setTreeImmutable (tcFocus tarTC)
  r <- checkRefDef (tcAddr tarTC) (fetchAtomFromAC immutTarget)
  rep <- treeToFullRepString r
  debugInstantRM "copyConcrete" (printf "target concrete is %s" rep) tarTC
  case r of
    IsNoVal -> return Nothing
    _ -> return $ Just r
 where
  fetchAtomFromAC x = case x of
    IsAtomCnstr c -> mkAtomTree c.value
    _ -> x

checkRefDef :: TreeAddr -> Tree -> RM Tree
checkRefDef tarAddr val = do
  -- Check if the referenced value has recurClose.
  let recurClose = isRecurClosed val
  hasDef <- addrHasDef tarAddr
  if hasDef || recurClose
    then markRecurClosed val
    else return val

markRecurClosed :: Tree -> RM Tree
markRecurClosed val = do
  utc <- preVisitTreeSimple (subNodes True) mark valTC
  return $ tcFocus utc
 where
  -- Create a tree cursor based on the value.
  valTC = TrCur val [(rootFeature, mkNewTree TNTop)]

  mark tc = do
    let focus = tcFocus tc
    return $
      focus
        { isRecurClosed = True
        , treeNode = case treeNode focus of
            TNStruct s -> TNStruct $ s{stcClosed = True}
            _ -> treeNode focus
        }
        `setTCFocus` tc

notFoundMsg :: TextIndex -> Maybe AST.Position -> RM String
notFoundMsg ident (Just AST.Position{AST.posStart = pos, AST.posFile = fM}) = do
  idStr <- tshow ident
  return $
    printf
      "reference %s is not found:\n\t%s:%s:%s"
      (show idStr)
      (fromMaybe "-" fM)
      (show $ AST.posLine pos)
      (show $ AST.posColumn pos)
notFoundMsg ident pinfo = throwFatal $ printf "position %s is not enough for identifier %s" (show pinfo) (show ident)

data LocateRefResult
  = LRIdentNotFound Tree
  | -- | The ident and all the rest of the segments are matched.
    -- The first is the ident address.
    LRRefFound TreeAddr TrCur
  | -- | The ident and some of the rest of the segments are matched, but not all.
    -- It records the last matched tree cursor and the potential target address.
    LRPartialFound TrCur TreeAddr
  | -- | The target node and the reference forms a cycle, which has already been detected by the notification graph.
    LRRefCycle TrCur
  deriving (Show)

{- | Locate the node in the lowest ancestor tree by given reference path.

The path must start with a locatable ident.
-}
locateRef :: FieldPath -> TrCur -> RM LocateRefResult
locateRef fieldPath tc = do
  when (isFieldPathEmpty fieldPath) $ throwFatal "empty fieldPath"
  let fstSel = fromJust $ headSel fieldPath
  ident <- selToIdent fstSel
  searchTCIdent False ident tc >>= \case
    Nothing -> do
      errMsg <- notFoundMsg ident (treeExpr (tcFocus tc) >>= AST.anPos)
      return . LRIdentNotFound $ mkBottomTree errMsg
    Just (identTC, _) -> do
      -- The ref is non-empty, so the rest must be a valid addr.
      let rest = fromJust $ tailFieldPath fieldPath
          (matchedTC, unmatchedSels) = go identTC (getRefSels rest)
          targetAddr =
            if null unmatchedSels
              then tcAddr matchedTC
              else appendTreeAddr (tcAddr matchedTC) (fieldPathToAddr (FieldPath unmatchedSels))

      debugInstantRM "locateRef" (printf "fieldPath: %s, before fetch" (show fieldPath)) tc

      -- Check if the target address is dirty.
      fetch <- asks (fetch . params)
      case addrIsSufIrred targetAddr of
        Just tSIAddr
          | RsDirty <- fetch tSIAddr -> do
              debugInstantRM "locateRef" (printf "target addr %s is dirty, throwDirty" (show targetAddr)) tc
              throwDirty tSIAddr
          | RsCyclic <- fetch tSIAddr
          , -- If the target is atom, even if it is cyclic, we can still return the value.
            -- Consider {a: 1 & a}
            Just _ <- rtrAtom matchedTC.tcFocus ->
              return $ LRRefFound (tcAddr identTC) matchedTC
          -- If the target is cyclic, we should return the ref cycle result.
          | RsCyclic <- fetch tSIAddr ->
              -- We return the ref cycle as a cycle unified with a top.
              return $
                LRRefCycle
                  ( mkNewTree (TNFix (Fix TNTop [FixSelect targetAddr] True))
                      `setTCFocus` matchedTC
                  )
        _ ->
          return $
            if null unmatchedSels
              then LRRefFound (tcAddr identTC) matchedTC
              else LRPartialFound matchedTC targetAddr
 where
  go x [] = (x, [])
  go x sels@(sel : rs) =
    maybe
      (x, sels)
      (`go` rs)
      (goDownTCSeg (selToTASeg sel) x)

addrHasDef :: TreeAddr -> RM Bool
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
searchTCIdent :: Bool -> TextIndex -> TrCur -> RM (Maybe (TrCur, IdentType))
searchTCIdent inEnclosing ident = go
 where
  go :: TrCur -> RM (Maybe (TrCur, IdentType))
  go tc = do
    identStr <- tshow ident
    tarM <- findIdent ident tc
    debugInstantRM "searchTCIdent" (printf "searching %s, found: %s" identStr (show $ isJust tarM)) tc
    maybe
      ( upOrLeft inEnclosing tc >>= \case
          Nothing -> return Nothing
          Just next -> go next
      )
      ( \(identTC, typ) -> do
          -- Mark the ident as referred if it is a let binding.
          when (typ == ITLetBinding) $ markRMLetReferred (tcAddr identTC)
          return $ Just (identTC, typ)
      )
      tarM

upOrLeft :: Bool -> TrCur -> RM (Maybe TrCur)
upOrLeft _ (TrCur _ [(FeatureType RootLabelType, _)]) = return Nothing -- stop at the root.
-- If the current node is an embedding, we should go to the parent block which by convention is the first mutable
-- argument.
upOrLeft True utc@(TrCur t ((f, IsEmbedUnifyOp sop) : _))
  | fetchIndex f > 0
  , ETEmbedded sid <- t.embType = do
      let jM =
            do
              (j, s) <- case getSOpArgs sop of
                s Seq.:<| _ -> return s
                _ -> Nothing
              struct <- rtrStruct s
              if struct.stcID == sid then Just j else Nothing
      case jM of
        Nothing -> throwFatal $ printf "upOrLeft: embedding %s's parent does not have the embedding struct" (show sid)
        Just j -> do
          debugInstantRM "upOrLeft" (printf "going up from embedding to parent block arg %s" (show j)) utc
          structTC <- liftEitherRM (propUpTC utc >>= goDownTCSegMust j)
          return $ Just structTC
upOrLeft _ utc = do
  ptc <- liftEitherRM (propUpTC utc)
  return $ Just ptc

findIdent :: TextIndex -> TrCur -> RM (Maybe (TrCur, IdentType))
findIdent ident tc = do
  case tcFocus tc of
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
                    subTC <- goDownTCSeg f tc
                    return (subTC, ITField)
                  else
                    Nothing
            , do
                subTC <- goDownTCSeg lf tc
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
              ( mkBottomTree (printf "multiple fields found for %s" (show ident)) `setTCFocus` fstTC
              , ITField
              )
    IsTreeMutable (Op (Compreh c)) -> do
      debugInstantRM "findIdent" (printf "search in the compreh, bindings: %s" (show c.iterBindings)) tc
      return $ do
        v <- Map.lookup ident c.iterBindings
        return (v `setTCFocus` tc, ITIterBinding)
    _ -> return Nothing
