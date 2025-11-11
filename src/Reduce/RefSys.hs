{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RefSys where

import qualified AST
import Control.Monad (unless, when)
import Control.Monad.Reader (asks)
import Cursor
import Data.Aeson (toJSON)
import Data.Aeson.Types (Value)
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, isNothing)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Feature
import NotifGraph
import Reduce.RMonad (
  ErrM,
  FetchResult (..),
  HasReduceParams (..),
  ResolveMonad,
  TrCurStErrM,
  ctxNotifGraph,
  debugInstantRM,
  descendTM,
  fetch,
  getRMContext,
  getTMAbsAddr,
  getTMCursor,
  liftFatal,
  markRMLetReferred,
  preVisitTreeSimple,
  propUpTMUntilSeg,
  putRMContext,
  throwDirty,
  throwFatal,
  traceSpanAdaptRM,
 )
import StringIndex (ShowWithTextIndexer (..), TextIndex, TextIndexerMonad)
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

adaptDRFetch :: DerefResult -> Maybe Tree
adaptDRFetch = const Nothing

adaptDRRep :: DerefResult -> Value
-- adaptDRRep dr = toJSON (treeToRepString <$> drValue dr, drTargetAddr dr, show $ drCycleDetection dr, drIsInBinding dr)
adaptDRRep dr = toJSON ()

notFound :: DerefResult
notFound = DerefResult Nothing Nothing NoCycleDetected False

derefResFromTrCur :: TrCur -> DerefResult
derefResFromTrCur tc = DerefResult (Just (tcFocus tc)) (Just (tcAddr tc)) NoCycleDetected False

-- | Resolve the reference value.
resolveTCIfRef :: (ResolveMonad r s m) => TrCur -> m DerefResult
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
index :: (ResolveMonad r s m) => TrCur -> m DerefResult
index tc@(TCFocus (IsRef _ argRef@Reference{refArg = (RefPath ident sels)})) = do
  identStr <- tshow ident
  traceSpanAdaptRM (printf "index: ident: %s" identStr) adaptDRFetch (return . adaptDRRep) tc $ do
    lbM <- searchTCIdent ident tc
    case lbM of
      Just (TCFocus (IsRef mut rf), typ)
        -- Let value is an index. For example, let x = ({a:1}).a
        | Just segs <- getIndexSegs rf
        , typ /= ITField -> do
            let newRef = mkIndexRef (segs Seq.>< sels)
                -- build the new reference tree.
                refTC = setTCFocusMut (setMutOp (Ref newRef) mut) tc
            resolveTCIfRef refTC
      Just (TCFocus lb, typ) | typ /= ITField -> do
        -- If the let value is not a reference, but a regular expression.
        -- For example, let x = {}, let x = 1 + 2
        let
          newRef = mkIndexRef (lb Seq.<| sels)
          -- build the new reference tree.
          refTC = setTCFocusMut (withEmptyMutFrame (Ref newRef)) tc
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
index tc@(TCFocus (IsRef _ Reference{refArg = arg@(RefIndex _)})) = traceSpanAdaptRM "index" adaptDRFetch (return . adaptDRRep) tc $ do
  operandTC <- liftFatal $ goDownTCSegMust (mkMutArgFeature 0) tc
  idxFieldPathM <- convertRefArgTreesToSels arg
  let
    reducedOperandM = rtrNonMut (tcFocus operandTC)
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
refTCFromRef :: (ResolveMonad r s m) => Reference -> TrCur -> m (Maybe (TrCur, FieldPath))
refTCFromRef Reference{refArg = arg@(RefPath ident _)} tc = do
  m <- convertRefArgTreesToSels arg
  maybe
    (return Nothing)
    ( \fp@(FieldPath reducedSels) -> do
        newRef <- liftFatal $ mkRefFromFieldPath mkAtomTree ident (FieldPath (tail reducedSels))
        -- build the new reference tree.
        let refTC = setTCFocusMut (withEmptyMutFrame (Ref newRef)) tc
        return $ Just (refTC, fp)
    )
    m
refTCFromRef _ _ = throwFatal "refTCFromRef: invalid reference"

{- | Convert the reference argument trees to selectors.

Notice that even if the selector tree is concrete, it might not be valid selector. It could be a disjunction.
-}
convertRefArgTreesToSels :: (TextIndexerMonad s m) => RefArg -> m (Maybe FieldPath)
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
getDstTC :: (ResolveMonad r s m) => FieldPath -> TrCur -> m DerefResult
getDstTC fieldPath env = do
  -- Make deref see the latest tree, even with unreduced nodes.
  traceSpanAdaptRM "getDstTC" adaptDRFetch (return . adaptDRRep) env $ do
    lr <- locateRef fieldPath env
    case lr of
      LRIdentNotFound err -> return (DerefResult (Just err) Nothing NoCycleDetected False)
      LRPartialFound _ potentialTarAddr -> do
        cd <- watch potentialTarAddr env
        return (DerefResult Nothing (Just potentialTarAddr) cd False)
      LRRefFound tarTC -> do
        cd <- watch (tcAddr tarTC) env
        vM <- copyConcrete tarTC
        return $ DerefResult vM (Just (tcAddr tarTC)) cd False

-- whenNoCD :: (ResolveMonad r s m) => m CycleDetection -> CycleDetection -> m CycleDetection
-- whenNoCD m NoCycleDetected = m
-- whenNoCD _ cd = return cd

{- | Watch the target address from the reference environment.

TODO: update the notification graph with the new dependency, not always insert.

Also check if any of the dependent of the current ref forms a cycle with the target address.
-}
watch :: (ResolveMonad r s m) => TreeAddr -> TrCur -> m CycleDetection
watch tarAddr refEnv = do
  when (isNothing $ addrIsSufRef tarAddr) $
    throwFatal $
      printf "watch: target addr %s is not suffix-referable" (show tarAddr)
  ctx <- getRMContext
  let
    refAddr = tcAddr refEnv
    tarAddrR = fromJust $ addrIsSufRef tarAddr
    newG = addNewDepToNG (refAddr, tarAddrR) (ctxNotifGraph ctx)
    -- Check if the refAddr's SuffixIrreducible form is in a cyclic scc.
    -- We have to trim the refAddr to its suffix irreducible form because the reference could be mutable argument.
    -- For example, {a: b + 1, b: a - 1}. We are interested in whether b forms a cycle, not /b/fa0.
    refGrpAddrM = lookupGrpAddr (trimAddrToSufIrred refAddr) newG
  putRMContext $ ctx{ctxNotifGraph = newG}

  cd <- case refGrpAddrM of
    Nothing -> throwFatal $ printf "watch: refAddr %s is not in the notification graph" (show refAddr)
    Just refGrpAddr ->
      if snd $ getGrpAddr refGrpAddr
        then return $ RCDetected (map sufIrredToAddr $ getElemAddrInGrp refGrpAddr newG)
        else return NoCycleDetected

  tarAddrStr <- tshow tarAddr
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
  = RCDetected [TreeAddr]
  | NoCycleDetected
  deriving (Show, Eq)

{- | Mark the value and all its descendants as cyclic.

We have to mark all descendants as cyclic here instead of just marking the focus because if the value is a struct and
it is immediately unified with a non-cyclic value, the descendants of the merged value, which does not have the
cyclic attribute, would lose the cyclic attribute.
-}
markCyclic :: (ErrM m) => Tree -> m Tree
markCyclic val = do
  utc <- preVisitTreeSimple (subNodes False) mark valTC
  return $ tcFocus utc
 where
  -- Create a tree cursor based on the value.
  valTC = TrCur val [(rootFeature, mkNewTree TNTop)]

  mark :: (ErrM m) => TrCur -> m TrCur
  mark tc = do
    let focus = tcFocus tc
    return $ focus{isSCyclic = True} `setTCFocus` tc

{- | Copy the concrete value from the target cursor if the target value has already been reduced.

The tree cursor is the target cursor without the copied raw value.
-}
copyConcrete :: (ResolveMonad r s m) => TrCur -> m (Maybe Tree)
copyConcrete tarTC = do
  -- We need to make the target immutable before returning it.
  -- 1. If the target is a mutable, then we should not return the mutable because the dependent can receive the new value
  -- if the mutable is updated.
  -- 2. If the target is a block, then we need the actual struct that it produces. However, we need to preserve the
  -- original references so that if they point to an inner scope, the values of them can be invalidated and further
  -- resolved to new fields. So there is no need to recursively make the block immutable.
  let immutTarget = makeTreeImmutable (tcFocus tarTC)
  r <- checkRefDef (tcAddr tarTC) (fetchAtomFromAC immutTarget)
  debugInstantRM "copyConcrete" (printf "target concrete is %s" (treeToFullRepString r)) tarTC
  case r of
    IsNoVal -> return Nothing
    _ -> return $ Just r
 where
  fetchAtomFromAC x = case x of
    IsAtomCnstr c -> mkAtomTree c.value
    _ -> x

checkRefDef :: (ResolveMonad r s m) => TreeAddr -> Tree -> m Tree
checkRefDef tarAddr val = do
  -- Check if the referenced value has recurClose.
  let recurClose = isRecurClosed val
  hasDef <- addrHasDef tarAddr
  if hasDef || recurClose
    then markRecurClosed val
    else return val

-- | Check if the reference is an inner reference.
isInnerScope :: (ResolveMonad r s m) => FieldPath -> TreeAddr -> TreeAddr -> TrCur -> m Bool
isInnerScope fieldPath originAddr tAddr tc = do
  tarIdentAddrM <- searchIdent fieldPath tc
  isInner <-
    maybe
      (return False)
      (\tarIdentAddr -> return $ isPrefix tAddr tarIdentAddr && tAddr /= tarIdentAddr)
      tarIdentAddrM
  debugInstantRM
    "isInnerScope"
    ( printf
        "fieldPath: %s, originAddr: %s, tAddr: %s, tarIdentAddrM: %s, isInner: %s"
        (show fieldPath)
        (show originAddr)
        (show tAddr)
        (show tarIdentAddrM)
        (show isInner)
    )
    tc
  return isInner
 where
  -- Search the first identifier of the reference and convert it to absolute tree addr if it exists.
  searchIdent :: (ResolveMonad r s m) => FieldPath -> TrCur -> m (Maybe TreeAddr)
  searchIdent ref xtc = do
    let fstSel = fromJust $ headSel ref
    ident <- selToIdent fstSel
    resM <- searchTCIdent ident xtc
    return $ tcAddr . fst <$> resM

markRecurClosed :: (ErrM m) => Tree -> m Tree
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

{- | Get the first identifier of the reference to absolute tree addr.

If the identifier is not found, it returns Nothing.

It does not follow the reference.
-}
getRefIdentAddr :: (ResolveMonad r s m) => FieldPath -> Maybe TreeAddr -> TrCur -> m (Maybe TreeAddr)
getRefIdentAddr fieldPath origAddrsM tc = do
  let fstSel = fromJust $ headSel fieldPath
  ident <- selToIdent fstSel
  let f x = searchTCIdent ident x >>= (\r -> return $ tcAddr . fst <$> r)

  -- Search the address of the first identifier, whether from the current env or the original env.
  maybe
    (f tc)
    ( \origValAddr ->
        -- original value must be accessible if such value exists.
        inAbsAddrTCMust origValAddr tc f
    )
    origAddrsM

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrTCMust :: (ErrM m, TextIndexerMonad s m) => TreeAddr -> TrCur -> (TrCur -> m a) -> m a
inAbsAddrTCMust p tc f = do
  tarM <- liftFatal (goTCAbsAddr p tc)
  maybe (throwFatal $ printf "%s is not found" (show p)) f tarM

notFoundMsg :: (ErrM m, TextIndexerMonad s m) => TextIndex -> Maybe AST.Position -> m String
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
  | LRRefFound TrCur
  | -- | The ident and some of the rest of the segments are matched, but not all.
    -- It records the last matched tree cursor and the potential target address.
    LRPartialFound TrCur TreeAddr
  deriving (Show)

{- | Locate the node in the lowest ancestor tree by given reference path.

The path must start with a locatable ident.
-}
locateRef :: (ResolveMonad r s m) => FieldPath -> TrCur -> m LocateRefResult
locateRef fieldPath tc = do
  when (isFieldPathEmpty fieldPath) $ throwFatal "empty fieldPath"
  let fstSel = fromJust $ headSel fieldPath
  ident <- selToIdent fstSel
  searchTCIdent ident tc >>= \case
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
      fetch <- asks (fetch . getReduceParams)
      case addrIsSufIrred targetAddr of
        Just tSIAddr
          | FRDirty <- fetch tSIAddr -> throwDirty tSIAddr
          | FRCyclic <- fetch tSIAddr
          , -- If the target is atom, even if it is cyclic, we can still return the value.
            -- Consider {a: 1 & a}
            Just _ <- rtrAtom matchedTC.tcFocus ->
              return $ LRRefFound matchedTC
          | FRCyclic <- fetch tSIAddr -> return $ LRRefFound (mkNewTree TNRefCycle `setTCFocus` matchedTC)
          | FRSCyclic <- fetch tSIAddr ->
              return $ LRRefFound $ (tcFocus matchedTC){isSCyclic = True} `setTCFocus` matchedTC
        _ ->
          return $
            if null unmatchedSels
              then LRRefFound matchedTC
              else LRPartialFound matchedTC targetAddr
 where
  go x [] = (x, [])
  go x sels@(sel : rs) =
    maybe
      (x, sels)
      (`go` rs)
      (goDownTCSeg (selToTASeg sel) x)

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrRM :: (TrCurStErrM s m) => TreeAddr -> m a -> m (Maybe a)
inAbsAddrRM p f = do
  origAbsAddr <- getTMAbsAddr

  tarM <- whenM (goRMAbsAddr p) f
  backOk <- goRMAbsAddr origAbsAddr
  unless backOk $ do
    throwFatal $
      printf
        "failed to go back to the original addr %s, dest: %s"
        (show origAbsAddr)
        (show p)
  return tarM
 where
  whenM :: (Monad m) => m Bool -> m a -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then Just <$> g else return Nothing

-- | Go to the absolute addr in the tree.
goRMAbsAddr :: (TrCurStErrM s m) => TreeAddr -> m Bool
goRMAbsAddr dst = do
  when (headSeg dst /= Just rootFeature) $
    throwFatal (printf "the addr %s should start with the root segment" (show dst))
  propUpTMUntilSeg rootFeature
  let dstNoRoot = fromJust $ tailTreeAddr dst
  descendTM dstNoRoot

goRMAbsAddrMust :: (TrCurStErrM s m) => TreeAddr -> m ()
goRMAbsAddrMust dst = do
  from <- getTMAbsAddr
  ok <- goRMAbsAddr dst
  unless ok $ do
    tc <- getTMCursor
    case treeNode (tcFocus tc) of
      -- If the focus of the cursor is a bottom, it is not a problem.
      TNBottom _ -> return ()
      _ -> throwFatal $ printf "failed to go to the addr %s, from: %s, tc: %s" (show dst) (show from) (show tc)

addrHasDef :: (TextIndexerMonad s m) => TreeAddr -> m Bool
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

selToIdent :: (ErrM m) => Selector -> m TextIndex
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
searchTCIdent :: (ResolveMonad r s m) => TextIndex -> TrCur -> m (Maybe (TrCur, IdentType))
searchTCIdent ident tc = do
  subM <- findIdent ident tc
  maybe
    (goUpOrLeft tc)
    ( \(identTC, typ) -> do
        -- Mark the ident as referred if it is a let binding.
        when (typ == ITLetBinding) $ markRMLetReferred (tcAddr identTC)
        return $ Just (identTC, typ)
    )
    subM
 where
  goUpOrLeft :: (ResolveMonad r s m) => TrCur -> m (Maybe (TrCur, IdentType))
  goUpOrLeft (TrCur _ [(FeatureType RootLabelType, _)]) = return Nothing -- stop at the root.
  -- If the current node is an embedding, we should go to the parent block which by convention is the first mutable
  -- argument.
  goUpOrLeft utc@(TrCur t ((f@(FeatureType MutArgLabelType), _) : _))
    | fetchIndex f > 0
    , ETEmbedded sid <- t.embType = do
        ptc <- liftFatal (propUpTC utc)
        args <- case ptc of
          TCFocus (IsTGenOp mut) -> return $ getMutArgs mut
          _ -> throwFatal $ printf "searchTCIdent: parent of embedding is not a mutable: %s" (show ptc)
        let jM =
              foldr
                ( \(j, x) acc ->
                    if isJust acc
                      then acc
                      else do
                        struct <- rtrStruct x
                        if struct.stcID == sid then Just j else Nothing
                )
                Nothing
                (zip [0 ..] $ toList args)
        case jM of
          Nothing -> throwFatal $ printf "searchTCIdent: embedding %s's parent does not have the embedding struct" (show sid)
          Just j -> do
            debugInstantRM "searchTCIdent" (printf "going up from embedding to parent block arg %s" (show j)) utc
            structTC <- liftFatal (goDownTCSegMust (mkMutArgFeature j) ptc)
            searchTCIdent ident structTC
  goUpOrLeft utc = do
    ptc <- liftFatal (propUpTC utc)
    searchTCIdent ident ptc

findIdent :: (ResolveMonad r s m) => TextIndex -> TrCur -> m (Maybe (TrCur, IdentType))
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
    IsTGenOp (MutOp (Compreh c)) -> do
      debugInstantRM "searchTCIdent" (printf "search in the compreh, bindings: %s" (show c.iterBindings)) tc
      return $ do
        -- name <- case ident of RefIdent name -> Just name; _ -> Nothing
        v <- Map.lookup ident c.iterBindings
        return (v `setTCFocus` tc, ITIterBinding)
    _ -> return Nothing
