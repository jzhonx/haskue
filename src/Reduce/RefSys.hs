{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RefSys where

import qualified AST
import qualified Common
import Control.Monad (foldM, unless, when)
import Cursor
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import NotifGraph
import Path
import Reduce.RMonad (
  ReduceMonad,
  ResolveMonad,
  debugInstantRM,
  debugSpanRM,
  descendTM,
  getRMContext,
  getTMAbsAddr,
  getTMCursor,
  markRMLetReferred,
  propUpTMUntilSeg,
  putRMContext,
 )
import Text.Printf (printf)
import Value

data DerefResult = DerefResult
  { drValue :: Maybe Tree
  , drTargetAddr :: Maybe TreeAddr
  , drCycleDetection :: CycleDetection
  , drIsInBinding :: Bool
  -- ^ Whether the dereferenced value is part of a let binding.
  }
  deriving (Show)

notFound :: DerefResult
notFound = DerefResult Nothing Nothing NoCycleDetected False

derefResFromTrCur :: TrCur -> DerefResult
derefResFromTrCur tc = DerefResult (Just (tcFocus tc)) (Just (tcCanAddr tc)) NoCycleDetected False

-- | Resolve the reference value.
resolveTCIfRef :: (ResolveMonad s r m) => TrCur -> m DerefResult
resolveTCIfRef tc = case tc of
  TCFocus (IsRef _ ref) -> index ref tc
  _ -> return $ derefResFromTrCur tc

{- | Index the tree with the segments.

Index has the form of either "a" or "a.b.c" or "{}.b".

If the index operand is a tree node, the tc is used as the environment to evaluate the tree node.

The return value will not be another reference.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
index :: (ResolveMonad s r m) => Reference -> TrCur -> m DerefResult
index argRef@Reference{refArg = (RefPath var sels)} tc =
  debugSpanRM (printf "index: var: %s" var) drValue tc $ do
    lbM <- searchTCIdent var tc
    case lbM of
      Just (TCFocus (IsRef mut rf), True)
        -- Let value is an index. For example, let x = ({a:1}).a
        | Just segs <- getIndexSegs rf -> do
            let newRef = mkIndexRef (segs Seq.>< sels)
                -- build the new reference tree.
                refTC = setTCFocusTN (TNMutable $ setMutOp (Ref newRef) mut) tc
            resolveTCIfRef refTC
      Just (TCFocus lb, True) -> do
        -- If the let value is not a reference, but a regular expression.
        -- For example, let x = {}, let x = 1 + 2
        let
          newRef = mkIndexRef (lb Seq.<| sels)
          -- build the new reference tree.
          refTC = setTCFocusTN (TNMutable $ withEmptyMutFrame (Ref newRef)) tc
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
index Reference{refArg = arg@(RefIndex _)} tc = debugSpanRM "index" drValue tc $ do
  operandTC <- goDownTCSegMust (MutArgTASeg 0) tc
  let
    reducedOperandM = rtrNonMut (tcFocus operandTC)
    idxFieldPathM = convertRefArgTreesToSels arg
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

-- | Resolve the reference value path using the tree cursor and replace the focus with the resolved value.
refTCFromRef :: (ResolveMonad s r m) => Reference -> TrCur -> m (Maybe (TrCur, FieldPath))
refTCFromRef Reference{refArg = arg@(RefPath var _)} tc = do
  maybe
    (return Nothing)
    ( \fp@(FieldPath reducedSels) -> do
        newRef <- mkRefFromFieldPath mkAtomTree var (FieldPath (tail reducedSels))
        let
          -- build the new reference tree.
          refTC = setTCFocusTN (TNMutable $ withEmptyMutFrame (Ref newRef)) tc
        return $ Just (refTC, fp)
    )
    (convertRefArgTreesToSels arg)
refTCFromRef _ _ = throwErrSt "refTCFromRef: invalid reference"

{- | Convert the reference argument trees to selectors.

Notice that even if the selector tree is concrete, it might not be valid selector. It could be a disjunction.
-}
convertRefArgTreesToSels :: RefArg -> Maybe FieldPath
convertRefArgTreesToSels arg = case arg of
  (RefPath var sels) -> do
    let h = StringSel (TE.encodeUtf8 var)
    rest <- mapM treeToSel (toList sels)
    return $ FieldPath (h : rest)
  (RefIndex (_ Seq.:<| rest)) -> FieldPath <$> mapM treeToSel (toList rest)
  _ -> Nothing

{- | Get the value pointed by the value path and the original addresses.

The env is to provide the context for the dereferencing the reference.
-}
getDstTC :: (ResolveMonad s r m) => FieldPath -> TrCur -> m DerefResult
getDstTC fieldPath _env = do
  -- Make deref see the latest tree, even with unreduced nodes.
  env <- syncTC _env
  debugSpanRM "getDstTC" (const Nothing) env $ do
    lr <- locateRef fieldPath env
    case lr of
      LRIdentNotFound err -> return (DerefResult (Just err) Nothing NoCycleDetected False)
      LRPartialFound _ potentialTarAddr -> undefined
      LRRefFound tarTC -> do
        cd <- watchFound tarTC env
        vM <- copyConcrete tarTC
        return $ DerefResult vM (Just (tcCanAddr tarTC)) cd False

whenNoCD :: (ResolveMonad s r m) => m CycleDetection -> CycleDetection -> m CycleDetection
whenNoCD m NoCycleDetected = m
whenNoCD _ cd = return cd

{- | Watch the target address from the reference environment.

Also check if any of the dependent of the current ref forms a cycle with the target address.
-}
watchFound :: (ResolveMonad s r m) => TrCur -> TrCur -> m CycleDetection
watchFound tarTC refEnv = do
  let
    refAddr = tcCanAddr refEnv
    rfbRefAddr = trimToReferable refAddr
    tarAddr = tcCanAddr tarTC

  ctx <- getRMContext
  let
    newG = addNewDepToNG (refAddr, tarAddr) (Common.ctxNotifGraph ctx)
    refSCCAddrM = lookupSCCAddr refAddr newG
  putRMContext $ ctx{Common.ctxNotifGraph = newG}
  cd <- case refSCCAddrM of
    Nothing -> throwErrSt $ printf "watchFound: refAddr %s is not in the notification graph" (show refAddr)
    Just refSCCAddr -> case refSCCAddr of
      ACyclicSCCAddr _ -> return NoCycleDetected
      CyclicSCCAddr _ -> return $ RCDetected (getSCCAddrs refSCCAddr newG)
      SCyclicSCCAddr _ _ -> return undefined
  debugInstantRM
    "watchFound"
    ( printf
        "tried to detect if tar: %s forms a cycle with %s's dependents. graph: %s, result: %s"
        (show tarAddr)
        (show rfbRefAddr)
        (show newG)
        (show cd)
    )
    refEnv
  return cd

{- | Watch the target address from the reference environment when the target is not found.

TODO: should we detect sub field cycles here?
-}
watchNotFound :: (ResolveMonad s r m) => TreeAddr -> TrCur -> m CycleDetection
watchNotFound tarAddr refEnv = do
  let
    refAddr = tcCanAddr refEnv

  -- ctx <- getRMContext
  debugInstantRM
    "watchNotFound"
    ( printf
        "tried to detect if tar: %s forms a cycle with %s's dependents: %s"
        (show tarAddr)
        (show refAddr)
        (show NoCycleDetected)
    )
    refEnv
  -- putRMContext $ Common.addCtxNotifPair ctx (tarAddr, refAddr)
  debugInstantRM
    "watchNotFound"
    ( printf
        "added notification pair: %s -> %s"
        (show tarAddr)
        (show refAddr)
    )
    refEnv
  return NoCycleDetected

{- | The result of getting the destination value.

The result is either an error, or the target tree cursor.
-}
type DstTC = Either Tree (Maybe TrCur)

data CycleDetection
  = RCDetected [TreeAddr]
  | SCDetected Tree
  | NoCycleDetected
  deriving (Show, Eq)

{- | Mark the value and all its descendants as cyclic.

We have to mark all descendants as cyclic here instead of just marking the focus because if the value is a struct and
it is immediately unified with a non-cyclic value, the descendants of the merged value, which does not have the
cyclic attribute, would lose the cyclic attribute.
-}
markCyclic :: (Common.Env r s m) => Tree -> m Tree
markCyclic val = do
  utc <- traverseTCSimple subNodes mark valTC
  return $ tcFocus utc
 where
  -- Create a tree cursor based on the value.
  valTC = TrCur val [(RootTASeg, mkNewTree TNTop)]

  mark :: (Common.Env r s m) => TrCur -> m Tree
  mark tc = do
    let focus = tcFocus tc
    return $ focus{treeIsCyclic = True}

{- | Copy the concrete value from the target cursor if the target value has already been reduced.

The tree cursor is the target cursor without the copied raw value.
-}
copyConcrete :: (ResolveMonad s r m) => TrCur -> m (Maybe Tree)
copyConcrete tarTC@(TCFocus (Tree{treeVersion = 0})) = do
  debugInstantRM "copyConcrete" "target tree is not reduced" tarTC
  return Nothing
copyConcrete tarTC = do
  let raw = case treeNode (tcFocus tarTC) of
        TNAtomCnstr c -> mkAtomTree $ cnsAtom c
        _ -> tcFocus tarTC
  r <- checkRefDef raw
  let concrete = rtrNonMut r
  debugInstantRM "copyConcrete" (printf "target concrete is %s" (show concrete)) tarTC
  return concrete
 where
  checkRefDef val = do
    -- Check if the referenced value has recurClose.
    let
      recurClose = treeRecurClosed (tcFocus tarTC)
      shouldClose = addrHasDef (tcCanAddr tarTC)
    if shouldClose || recurClose
      then markRecurClosed val
      else return val

-- | Check if the reference is an inner reference.
isInnerScope :: (ResolveMonad s r m) => FieldPath -> TreeAddr -> TreeAddr -> TrCur -> m Bool
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
  searchIdent :: (ResolveMonad s r m) => FieldPath -> TrCur -> m (Maybe TreeAddr)
  searchIdent ref xtc = do
    let fstSel = fromJust $ headSel ref
    ident <- selToIdent fstSel
    resM <- searchTCIdent ident xtc
    return $ tcCanAddr . fst <$> resM

markRecurClosed :: (Common.Env r s m) => Tree -> m Tree
markRecurClosed val = do
  utc <- traverseTCSimple subNodes mark valTC
  return $ tcFocus utc
 where
  -- Create a tree cursor based on the value.
  valTC = TrCur val [(RootTASeg, mkNewTree TNTop)]
  mark :: (Common.Env r s m) => TrCur -> m Tree
  mark tc = do
    let focus = tcFocus tc
    return $
      focus
        { treeRecurClosed = True
        , treeNode = case treeNode focus of
            TNBlock block -> TNBlock $ modifyBlockStruct (\s -> s{stcClosed = True}) block
            _ -> treeNode focus
        }

{- | Get the first identifier of the reference to absolute tree addr.

If the identifier is not found, it returns Nothing.

It does not follow the reference.
-}
getRefIdentAddr :: (ResolveMonad s r m) => FieldPath -> Maybe TreeAddr -> TrCur -> m (Maybe TreeAddr)
getRefIdentAddr fieldPath origAddrsM tc = do
  let fstSel = fromJust $ headSel fieldPath
  ident <- selToIdent fstSel
  let f x = searchTCIdent ident x >>= (\r -> return $ tcCanAddr . fst <$> r)

  -- Search the address of the first identifier, whether from the current env or the original env.
  maybe
    (f tc)
    ( \origValAddr ->
        -- original value must be accessible if such value exists.
        inAbsAddrTCMust origValAddr tc f
    )
    origAddrsM

notFoundMsg :: (Common.Env r s m) => T.Text -> Maybe AST.Position -> m String
notFoundMsg ident (Just AST.Position{AST.posStart = pos, AST.posFile = fM}) =
  return $
    printf
      "reference %s is not found:\n\t%s:%s:%s"
      (show ident)
      (fromMaybe "-" fM)
      (show $ AST.posLine pos)
      (show $ AST.posColumn pos)
notFoundMsg ident pinfo = throwErrSt $ printf "position %s is not enough for identifier %s" (show pinfo) (show ident)

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
locateRef :: (ResolveMonad s r m) => FieldPath -> TrCur -> m LocateRefResult
locateRef fieldPath tc = do
  when (isFieldPathEmpty fieldPath) $ throwErrSt "empty fieldPath"
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
      return $
        if null unmatchedSels
          then LRRefFound matchedTC
          else LRPartialFound matchedTC (appendTreeAddr (tcCanAddr matchedTC) (fieldPathToAddr (FieldPath unmatchedSels)))
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
inAbsAddrRM :: (ReduceMonad s r m) => TreeAddr -> m a -> m (Maybe a)
inAbsAddrRM p f = do
  origAbsAddr <- getTMAbsAddr

  tarM <- whenM (goRMAbsAddr p) f
  backOk <- goRMAbsAddr origAbsAddr
  unless backOk $ do
    throwErrSt $
      printf
        "failed to go back to the original addr %s, dest: %s"
        (show origAbsAddr)
        (show p)
  return tarM
 where
  whenM :: (ReduceMonad s r m) => m Bool -> m a -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then Just <$> g else return Nothing

-- | Go to the absolute addr in the tree.
goRMAbsAddr :: (ReduceMonad s r m) => TreeAddr -> m Bool
goRMAbsAddr dst = do
  when (headSeg dst /= Just RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  propUpTMUntilSeg RootTASeg
  let dstNoRoot = fromJust $ tailTreeAddr dst
  descendTM dstNoRoot

goRMAbsAddrMust :: (ReduceMonad s r m) => TreeAddr -> m ()
goRMAbsAddrMust dst = do
  from <- getTMAbsAddr
  ok <- goRMAbsAddr dst
  unless ok $ do
    tc <- getTMCursor
    case treeNode (tcFocus tc) of
      -- If the focus of the cursor is a bottom, it is not a problem.
      TNBottom _ -> return ()
      _ -> throwErrSt $ printf "failed to go to the addr %s, from: %s, tc: %s" (show dst) (show from) (show tc)

addrHasDef :: TreeAddr -> Bool
addrHasDef p =
  any
    ( \case
        BlockTASeg (StringTASeg s) -> fromMaybe False $ do
          typ <- getFieldType (T.unpack $ TE.decodeUtf8 s)
          return $ typ == SFTDefinition
        _ -> False
    )
    $ addrToList p

selToIdent :: (Common.Env r s m) => Selector -> m T.Text
selToIdent (StringSel s) = return $ TE.decodeUtf8 s
selToIdent _ = throwErrSt "invalid selector"

{- | Search in the parent scope for the first identifier that can match the segment.

Also return if the identifier is a let binding.
-}
searchTCIdentInPar :: (ResolveMonad s r m) => T.Text -> TrCur -> m (Maybe (TreeAddr, Bool))
searchTCIdentInPar name tc = do
  ptc <- parentTCMust tc
  if isTCTop ptc
    then return Nothing
    else do
      m <- searchTCIdent name ptc
      return $ maybe Nothing (\(x, y) -> Just (tcCanAddr x, y)) m

{- | Search in the tree for the first identifier that can match the name.

Searching identifiers only searches for the identifiers declared in the block, not for the identifiers added by
unification with embeddings.

Return a pair. The first is address of the identifier, the second is whether the identifier is a let binding.

The child value will not be propagated to the parent block. Propagation is not needed because all static fields should
already exist.

The tree cursor must at least have the root segment.
-}
searchTCIdent :: (ResolveMonad s r m) => T.Text -> TrCur -> m (Maybe (TrCur, Bool))
searchTCIdent name tc = do
  subM <- findIdent name tc
  maybe
    (goUp tc)
    ( \(identTC, isLB) -> do
        when isLB $ do
          -- Mark the ident as referred if it is a let binding.
          markRMLetReferred (tcCanAddr identTC)
        -- unrefLets <- getRMUnreferredLets
        -- debugInstantRM
        --   "searchTCIdent"
        --   (printf "ident: %s, unrefLets: %s" (show $ tcCanAddr identTC) (show unrefLets))
        --   tc
        return $ Just (identTC, isLB)
    )
    subM
 where
  mkSeg isLB = let nt = TE.encodeUtf8 name in BlockTASeg $ if isLB then LetTASeg nt else StringTASeg nt

  goUp :: (ResolveMonad s r m) => TrCur -> m (Maybe (TrCur, Bool))
  goUp (TrCur _ [(RootTASeg, _)]) = return Nothing -- stop at the root.
  goUp utc = do
    ptc <- maybe (throwErrSt "already on the top") return $ parentTC utc
    searchTCIdent name ptc

  -- TODO: findIdent for default disjunct?
  findIdent :: (Common.Env r s m) => T.Text -> TrCur -> m (Maybe (TrCur, Bool))
  findIdent ident blockTC = do
    case treeNode (tcFocus blockTC) of
      TNBlock blk@(IsBlockStruct struct) -> do
        -- If the block reduces to non-struct, then the fields are not searchable in the block. The fields have
        -- behaved like mutable argument.
        -- For example, { x: {a:1, c:d, e}, e: {a: int} | {b: int}, d:1 }
        -- - merge -> {x: {a:1, c:d} | {a:1, c:d, b:int}, d:1, e: {..}}
        -- Then when we reduce the merged value, at /x/dj0/c, it finds d in the top /.
        let
          m =
            catMaybes
              [ do
                  sf <- lookupStructIdentField ident struct
                  return (mkSubTC (mkSeg False) (ssfValue sf) blockTC, False)
              , do
                  lb <- lookupBlockLet ident blk
                  return (mkSubTC (mkSeg True) (lbValue lb) blockTC, True)
              ]
        case m of
          [] -> do
            -- debugInstantRM
            --   "findIdent"
            --   (printf "ident %s not found in block, tc: %s" (show ident) (showCursor blockTC))
            --   blockTC
            return Nothing
          [x] -> return $ Just x
          (fstTC, _) : _ ->
            return $
              Just
                ( mkBottomTree (printf "multiple fields found for %s" ident) `setTCFocus` fstTC
                , False
                )
      TNMutable (MutOp (Compreh c)) -> do
        case Map.lookup ident (cphIterBindings c) of
          Just v -> return $ Just (mkSubTC (mkSeg True) v blockTC, False)
          Nothing -> return Nothing
      _ -> do
        -- debugInstantRM
        --   "findIdent"
        --   (printf "ident %s not found in value, tc: %s" (show ident) (showCursor blockTC))
        --   blockTC
        return Nothing

{- | Go to the absolute addr in the tree. No propagation is involved.

The tree must have all the latest changes.
-}
goTCAbsAddr :: (Common.Env r s m) => TreeAddr -> TrCur -> m (Maybe TrCur)
goTCAbsAddr dst tc = do
  when (headSeg dst /= Just RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  top <- topTC tc
  let dstNoRoot = fromJust $ tailTreeAddr dst
  return $ goDownTCAddr dstNoRoot top

goTCAbsAddrMust :: (Common.Env r s m) => TreeAddr -> TrCur -> m TrCur
goTCAbsAddrMust dst tc = do
  tarM <- goTCAbsAddr dst tc
  maybe (throwErrSt $ printf "failed to go to the addr %s" (show dst)) return tarM

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrTCMust :: (Common.Env r s m) => TreeAddr -> TrCur -> (TrCur -> m a) -> m a
inAbsAddrTCMust p tc f = do
  tarM <- goTCAbsAddr p tc
  maybe (throwErrSt $ printf "%s is not found" (show p)) f tarM

{- | Populate the references that are part of the reference cycles with either RefCycle or the actual value.

We are visiting the tree in a DFS manner.
-}
populateRCRefs :: (ResolveMonad s r m) => [TreeAddr] -> [TreeAddr] -> TrCur -> m TrCur
populateRCRefs rcAddrs populatingRCs = traverseTCSimple (\x -> subNodes x ++ rawNodes x) go
 where
  go tc = case tcFocus tc of
    IsRef mut ref@(Reference{refArg = ra@(RefPath{})}) -> do
      debugInstantRM "populateRCRefs" (printf "visiting ref %s" (show ref)) tc
      let fpM = convertRefArgTreesToSels ra
      case fpM of
        Nothing -> return $ tcFocus tc
        Just fp -> do
          r <- locateRef fp tc
          case r of
            LRIdentNotFound _ -> throwErrSt $ printf "populateRCRefs: ident not found for ref %s" (show ref)
            LRPartialFound _ _ -> throwErrSt $ printf "populateRCRefs: partial found for ref %s" (show ref)
            LRRefFound tarTC -> do
              let tarAddr = tcCanAddr tarTC
              if
                -- If the reference is not a reference cycle, do not populate.
                | not (tarAddr `elem` rcAddrs) -> return $ tcFocus tc
                -- If the reference is pointing to a RC reference that is being populated, create a RC node.
                | tarAddr `elem` populatingRCs -> do
                    let newMut = setMutVal (Just (mkNewTree TNRefCycle)) mut
                    return $ setTN (tcFocus tc) (TNMutable newMut)
                -- It is a RC reference that has not been populated yet. Populate it recursively.
                | otherwise -> do
                    rTC <- populateRCRefs rcAddrs (tarAddr : populatingRCs) tarTC
                    -- If the population result is still a reference, we should fetch the non-mutable part of the
                    -- reference to avoid nested references.
                    let rM = case tcFocus rTC of
                          IsRef{} -> rtrNonMut (tcFocus rTC)
                          _ -> Just $ tcFocus rTC
                        newMut = setMutVal rM mut
                    return $ setTN (tcFocus tc) (TNMutable newMut)
    -- Invalidate the mutable so that later reduce can re-reduce it.
    IsMutable mut -> do
      let newMut = setMutVal Nothing mut
          newTree = setTN (tcFocus tc) (TNMutable newMut)
      return newTree
    _ -> return $ tcFocus tc

-- | Populate the references that are part of the reference cycles with either RefCycle or the actual value.
populateRCRefsWithTop :: (ResolveMonad s r m) => TrCur -> m TrCur
populateRCRefsWithTop = traverseTCSimple (\x -> subNodes x ++ rawNodes x) go
 where
  go tc = case tcFocus tc of
    IsRef mut ref@(Reference{refArg = RefPath{}})
      | Just IsRefCycle <- getMutVal mut -> do
          debugInstantRM "populateRCRefs" (printf "visiting ref %s" (show ref)) tc
          let newMut = setMutVal (Just (mkNewTree TNTop)) mut
          return $ setTN (tcFocus tc) (TNMutable newMut)
    _ -> return $ tcFocus tc
