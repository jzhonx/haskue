{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RefSys where

import Common (BuildASTExpr (buildASTExpr), Env, TreeOp (isTreeBottom), addCtxNotifPair)
import Control.Monad (unless, when)
import qualified Cursor
import Data.Maybe (catMaybes, fromJust, fromMaybe, isNothing)
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified Path
import qualified Reduce.RMonad as RM
import TCursorOps (goDownTCAddr, topTC)
import qualified TCursorOps
import Text.Printf (printf)
import Util (debugInstant, debugSpan, logDebugStr)
import qualified Value.Tree as VT

{- | Dereference the reference.

It keeps dereferencing until the target node is not a reference node or a cycle is
detected.

If the target is found, a copy of the target value is put to the tree. The target address is also returned.
Otherwise, a stub is put to the tree.
-}
deref ::
  (RM.ReduceMonad s r m) =>
  -- | the reference addr
  Path.Reference ->
  Maybe (Path.TreeAddr, Path.TreeAddr) ->
  m (Maybe Path.TreeAddr)
deref ref origAddrsM = RM.withAddrAndFocus $ \addr _ ->
  RM.debugSpanRM (printf "deref: origAddrsM: %s, ref: %s" (show origAddrsM) (show ref)) $ do
    -- Propagate the changes to the root and get back to the addr. This makes sure the tree cursor sess the latest
    -- changes.
    do
      tc <- RM.getRMCursor
      -- We should not propagate the current node's state to the parent because its value has just been made to stub,
      -- which will disrupt the parent if the parent is a struct.
      refTC <- TCursorOps.propUpTC tc
      let refAddr = Cursor.tcTreeAddr refTC
      -- Notice the deref is in the /par_addr/ref_addr/sv, we need to move up to the /par_addr without any propagation
      -- from ref_addr to par_addr.
      parTC <- maybe (throwErrSt "already on the top") return (Cursor.parentTC refTC)
      RM.putRMCursor parTC
      RM.propUpRMUntilSeg Path.RootTASeg
      -- First go back to the ref_addr and replace stale value of the ref_addr with the preserved value.
      goRMAbsAddrMust refAddr
      RM.putRMTree (Cursor.tcFocus refTC)
      -- Go to the sv.
      ok <- RM.descendRMSeg Path.SubValTASeg
      unless ok $ throwErrSt $ printf "failed to go to the sv addr of %s" (show refAddr)

    -- Add the notifier anyway.
    watchRefRM ref origAddrsM

    let
      selfAddr = Path.noSubValAddr addr
      trail = Set.fromList [selfAddr]
    tc <- RM.getRMCursor
    getDstVal ref origAddrsM trail tc

{- | Monitor the absoluate address of the reference searched from the original environment by adding a notifier pair
from the current environment address to the searched address.

If the reference is not found, the function does nothing.

Duplicate cases are handled by the addCtxNotifPair.
-}
watchRefRM :: (RM.ReduceMonad s r m) => Path.Reference -> Maybe (Path.TreeAddr, Path.TreeAddr) -> m ()
watchRefRM ref origAddrsM = do
  tc <- RM.getRMCursor
  srcAddrM <-
    refToPotentialAddr ref origAddrsM tc >>= \xM -> return $ do
      x <- xM
      Path.referableAddr x
  -- Since we are in the /sv environment, we need to get the referable addr.
  recvAddr <- Path.noSubValAddr <$> RM.getRMAbsAddr

  maybe
    (logDebugStr $ printf "watchRefRM: ref %s is not found" (show ref))
    ( \srcAddr -> do
        ctx <- RM.getRMContext
        RM.putRMContext $ addCtxNotifPair ctx (srcAddr, recvAddr)
        logDebugStr $ printf "watchRefRM: (%s -> %s)" (show srcAddr) (show recvAddr)
    )
    srcAddrM

{- | Get the value of the reference.

If the reference value is another reference, it will follow the reference.

The environment is the current reference environment. The reference value will be put to the current environment.
-}
getDstVal ::
  (RM.ReduceMonad s r m) =>
  Path.Reference ->
  Maybe (Path.TreeAddr, Path.TreeAddr) ->
  Set.Set Path.TreeAddr ->
  Cursor.TreeCursor VT.Tree ->
  m (Maybe Path.TreeAddr)
getDstVal ref origAddrsM trail tc = RM.debugSpanArgsRM
  (printf "getDstVal: ref: %s" (show ref))
  (printf "trail: %s" (show trail))
  $ do
    RM.debugInstantRM "getDstVal" (printf "tc: %s" (show tc))

    rE <- getDstTC ref origAddrsM trail tc
    case rE of
      Left err -> RM.putRMTree err >> return Nothing
      Right Nothing -> return Nothing
      Right (Just tarTC) -> do
        raw <- copyRefVal (Cursor.tcFocus tarTC)
        newVal <- processCopiedRaw trail tarTC raw
        RM.putRMTree newVal
        RM.debugInstantRM
          "getDstVal"
          ( printf
              "ref: %s, dstVal: %s, raw: %s, newVal: %s"
              (show ref)
              (show $ Cursor.tcFocus tarTC)
              (show raw)
              (show newVal)
          )
        tryFollow (newVal `Cursor.setTCFocus` tarTC)
 where
  -- Try to follow the reference if the new value is a reference.
  tryFollow utarTC = case ( do
                              rf <- VT.getMutableFromTree (Cursor.tcFocus utarTC) >>= VT.getRefFromMutable
                              newRef <-
                                VT.refFromRefArg
                                  (\x -> Path.StringSel <$> VT.getStringFromTree x)
                                  (VT.refArg rf)
                              return (newRef, VT.refOrigAddrs rf)
                          ) of
    -- follow the reference.
    Just (rf, rfOirgAddrs) -> do
      let dstAddr = Cursor.tcTreeAddr utarTC
      RM.withAddrAndFocus $ \addr _ ->
        logDebugStr $
          printf
            "deref_getDstVal: addr: %s, dstAddr: %s, follow the new reference: %s"
            (show addr)
            (show dstAddr)
            (show rf)
      getDstVal rf rfOirgAddrs (Set.insert dstAddr trail) utarTC
    _ -> return (Just $ Cursor.tcTreeAddr utarTC)

{- | The result of getting the destination value.

The result is either an error, such as a bottom or a structural cycle, or a valid value.
-}
type DstTC = Either VT.Tree (Maybe (Cursor.TreeCursor VT.Tree))

{- | Get the processed tree cursor pointed by the reference.

If the reference addr is self or visited, then return the tuple of the absolute addr of the start of the cycle and
the cycle tail relative addr.
-}
getDstTC ::
  (Env r s m) =>
  Path.Reference ->
  -- | The original addresses of the reference.
  Maybe (Path.TreeAddr, Path.TreeAddr) ->
  -- | keeps track of the followed *referable* addresses.
  Set.Set Path.TreeAddr ->
  -- | The cursor should be the reference.
  Cursor.TreeCursor VT.Tree ->
  m DstTC
getDstTC ref origAddrsM trail refTC =
  debugSpan
    "deref_getDstTC"
    (show $ Cursor.tcTreeAddr refTC)
    (Just $ printf "ref: %s, origAddrsM: %s, trail: %s" (show ref) (show origAddrsM) (show $ Set.toList trail))
    (Cursor.tcFocus refTC)
    $ traceAdapt
    $ do
      let
        srcAddr = Cursor.tcTreeAddr refTC
        f x = locateRefAndRun ref x (_detectCycle ref srcAddr trail)

      maybe
        (f refTC)
        -- If the ref is an outer reference, we should first go to the original value address.
        ( \(origSubTAddr, origValAddr) -> inAbsAddrTCMust origSubTAddr refTC $ \tarTC -> do
            -- If the ref is an outer reference inside the referenced value, we should check if the ref leads to
            -- infinite structure (structural cycle).
            -- For example, { x: a, y: 1, a: {b: y} }, where /a is the address of the subt value.
            -- The "y" in the struct {b: y} is an outer reference.
            -- We should first go to the original value address, which is /a/b.
            -- infE <- locateRefAndRun ref tarTC (_checkInf ref srcAddr origValAddr)
            rE <- f tarTC
            -- return $ infE >> rE
            return rE
        )
        origAddrsM
 where
  traceAdapt f = do
    r <- f
    let after = case r of
          Left err -> err
          Right m -> maybe (VT.mkBottomTree "Healthy Not found") Cursor.tcFocus m
    return (r, after)

{- | Detect if the reference leads to a cycle.

If it does, modify the cursor to be the related cycle node.
-}
_detectCycle ::
  (Env r s m) =>
  Path.Reference ->
  Path.TreeAddr ->
  Set.Set Path.TreeAddr ->
  Cursor.TreeCursor VT.Tree ->
  m (Either a (Maybe (Cursor.TreeCursor VT.Tree)))
_detectCycle ref srcAddr trail tc = do
  let dstAddr = Cursor.tcTreeAddr tc
  logDebugStr $
    printf "deref_getDstVal ref: %s, ref is found, src: %s, dst: %s" (show ref) (show srcAddr) (show dstAddr)
  let
    canSrcAddr = Path.canonicalizeAddr srcAddr
    canDstAddr = Path.canonicalizeAddr dstAddr
    tar = Cursor.tcFocus tc
  val <-
    if
      -- The bottom must return early so that the identifier not found error would not be replaced with the cycle error.
      | isTreeBottom tar -> return tar
      -- This handles the case when following the chain of references leads to a cycle.
      -- For example, { a: b, b: a, d: a } and we are at d.
      -- The values of d would be: 1. a -> b, 2. b -> a, 3. a (seen) -> RC.
      -- The returned RC would be a self-reference cycle, which has empty addr because the cycle is formed by all
      -- references.
      -- dstAddr is already in the referable form.
      | Set.member dstAddr trail -> do
          logDebugStr $
            printf
              "deref_getDstVal: horizontal reference cycle detected: %s, dst: %s, trail: %s"
              (show ref)
              (show dstAddr)
              (show $ Set.toList trail)
          return (VT.setTN tar $ VT.TNRefCycle (VT.RefCycleHori (dstAddr, srcAddr)))
      -- This handles the case when the reference in a sub structure refers to itself.
      -- For example, { a: a + 1 } or { a: !a }.
      -- The tree representation of the latter is,
      -- { }
      --  | - a
      -- (!)
      --  | - unary_op
      -- ref_a
      -- Notice that for self-cycle, the srcTreeAddr could be /addr/sv, and the dstTreeAddr could be /addr. They
      -- are the same in the refNode form.
      | Just canDstAddr == Path.referableAddr canSrcAddr && srcAddr /= dstAddr -> do
          logDebugStr $
            printf
              "deref_getDstVal: vertical reference cycle tail detected: %s == %s."
              (show dstAddr)
              (show srcAddr)
          return (VT.setTN tar $ VT.TNRefCycle (VT.RefCycleVertMerger (dstAddr, srcAddr)))
      | Path.isPrefix canDstAddr canSrcAddr && canSrcAddr /= canDstAddr ->
          return $ VT.mkBottomTree "structural cycle"
      | otherwise -> return tar
  return . Right $ Just (val `Cursor.setTCFocus` tc)

{- | Check if the reference leads to a structural cycle.

If it does, return the cycle with the start address being the srcAddr, which is the current ref's addr.

The origValAddr is the original value address. See the comment of the caller.
-}
_checkInf ::
  (Env r s m) =>
  Path.Reference ->
  Path.TreeAddr ->
  Path.TreeAddr ->
  Cursor.TreeCursor VT.Tree ->
  m (Either VT.Tree (Maybe (Path.TreeAddr, VT.Tree)))
_checkInf ref srcAddr origValAddr dstTC = do
  -- dstAddr is the destination address of the reference.
  let
    dstAddr = Cursor.tcTreeAddr dstTC
    canSrcAddr = Path.canonicalizeAddr origValAddr
    canDstAddr = Path.canonicalizeAddr dstAddr

  let
    t = Cursor.tcFocus dstTC
    r :: Either VT.Tree (Maybe (Path.TreeAddr, VT.Tree))
    r =
      -- Pointing to ancestor generates a structural cycle.
      if Path.isPrefix canDstAddr canSrcAddr && canSrcAddr /= canDstAddr
        then Left (VT.mkBottomTree "structural cycle")
        else Right Nothing

  logDebugStr $
    printf
      "deref_getDstVal checkInf, ref: %s, origValAddr: %s, dst: %s, result: %s"
      (show ref)
      (show origValAddr)
      (show dstAddr)
      (show r)

  return r

{- | Copy the value of the reference.

The arg trail is used to decide whether to close the deref'd value.

The ReduceMonad is only used to run the evalExpr.

From the spec:
The value of a reference is a copy of the expression associated with the field that it is bound to, with
any references within that expression bound to the respective copies of the fields they were originally
bound to.
-}
copyRefVal :: (RM.ReduceMonad s r m) => VT.Tree -> m VT.Tree
copyRefVal tar = do
  case VT.treeNode tar of
    VT.TNAtom _ -> return tar
    VT.TNBottom _ -> return tar
    VT.TNRefCycle _ -> return tar
    VT.TNAtomCnstr c -> return (VT.mkAtomVTree $ VT.cnsAtom c)
    _ -> do
      e <- maybe (buildASTExpr False tar) return (VT.treeExpr tar)
      RM.evalExprRM e

{- | Process the copied raw value.

The tree cursor is the target cursor without the copied raw value.
-}
processCopiedRaw :: (Env r s m) => Set.Set Path.TreeAddr -> Cursor.TreeCursor VT.Tree -> VT.Tree -> m VT.Tree
processCopiedRaw trail tarTC raw = do
  let dstAddr = Cursor.tcTreeAddr tarTC
  -- evaluate the original expression.
  marked <- markOuterIdents (raw `Cursor.setTCFocus` tarTC)
  let visited = Set.insert dstAddr trail
  val <- checkRefDef marked visited

  logDebugStr $
    printf
      "deref: deref's copy is: %s, visited: %s, raw: %s"
      (show val)
      (show $ Set.toList visited)
      (show raw)
  return val
 where
  checkRefDef val visited = do
    -- Check if the referenced value has recurClose.
    let
      recurClose = VT.treeRecurClosed (Cursor.tcFocus tarTC)
      shouldClose = any addrHasDef visited
    if shouldClose || recurClose
      then do
        logDebugStr $
          printf
            "deref: visitedRefs: %s, has definition or recurClose: %s is set, recursively close the value. %s"
            (show $ Set.toList visited)
            (show recurClose)
            (show val)
        markRecurClosed val
      else return val

{- | Mark all outer references inside a block with original value address.

The outer references are the nodes inside (not equal to) a block pointing to the out of block identifiers. This is
needed because after copying the value, the original scope has been lost.

For example, given the following tree:

y: a.s
a: {
	s: {j1: i2}
	i2: 2
}

The block is {j1: i2}. We need to mark the i2 so that its value can be looked up in /y.
-}
markOuterIdents ::
  (Env r s m) =>
  -- | The current tree cursor.
  Cursor.TreeCursor VT.Tree ->
  m VT.Tree
markOuterIdents ptc = do
  let subtAddr = Cursor.tcTreeAddr ptc
  utc <- TCursorOps.traverseTCSimple VT.subNodes (mark subtAddr) ptc
  debugInstant
    "markOuterRefs"
    (show subtAddr)
    ( Just $
        printf
          "scope: %s, val: %s, result: %s"
          (show subtAddr)
          (show $ Cursor.tcFocus ptc)
          (VT.treeFullStr 0 $ Cursor.tcFocus utc)
    )
  return $ Cursor.tcFocus utc
 where
  -- Mark the outer references with the original value address.
  mark :: (Env r s m) => Path.TreeAddr -> Cursor.TreeCursor VT.Tree -> m VT.Tree
  mark subtAddr tc = do
    let focus = Cursor.tcFocus tc
    rM <- case VT.getMutableFromTree focus of
      Just (VT.Ref rf) -> return $ do
        newPRef <- VT.refFromRefArg (\x -> Path.StringSel <$> VT.getStringFromTree x) (VT.refArg rf)
        return (newPRef, \as -> VT.setTN focus $ VT.TNMutable . VT.Ref $ rf{VT.refOrigAddrs = Just as})
      _ -> return Nothing
    maybe
      (return focus)
      ( \(rf, f) -> do
          isOuter <- isOuterScope subtAddr tc rf
          if isOuter
            then return $ f (subtAddr, Cursor.tcTreeAddr tc)
            else return focus
      )
      rM

  -- Check if the reference is an outer reference.
  isOuterScope ::
    (Env r s m) =>
    -- The block node address.
    Path.TreeAddr ->
    Cursor.TreeCursor VT.Tree ->
    Path.Reference ->
    m Bool
  isOuterScope subtAddr tc rf = do
    tarIdentAddrM <- searchIdent rf tc
    isOuter <-
      maybe
        (return False)
        ( \tarIdentAddr -> do
            let tarIdentInScope = Path.isPrefix subtAddr tarIdentAddr && tarIdentAddr /= subtAddr
            return $ not tarIdentInScope
        )
        tarIdentAddrM
    logDebugStr $
      printf
        "markOuterRefs: ref to mark: %s, cursor_addr: %s, subtAddr: %s, tarIdentAddrM: %s, isOuterScope: %s"
        (show rf)
        (show $ Cursor.tcTreeAddr tc)
        (show subtAddr)
        (show tarIdentAddrM)
        (show isOuter)
    return isOuter

  -- Search the first identifier of the reference and convert it to absolute tree addr if it exists.
  searchIdent :: (Env r s m) => Path.Reference -> Cursor.TreeCursor VT.Tree -> m (Maybe Path.TreeAddr)
  searchIdent ref tc = do
    let fstSel = fromJust $ Path.headSel ref
    ident <- selToIdent fstSel
    resM <- searchTCIdent ident tc
    return $ fst <$> resM

markRecurClosed :: (Env r s m) => VT.Tree -> m VT.Tree
markRecurClosed val = do
  utc <- TCursorOps.traverseTCSimple VT.subNodes mark valTC
  return $ Cursor.tcFocus utc
 where
  -- Create a tree cursor based on the value.
  valTC = Cursor.TreeCursor val [(Path.RootTASeg, VT.mkNewTree VT.TNTop)]
  mark :: (Env r s m) => Cursor.TreeCursor VT.Tree -> m VT.Tree
  mark tc = do
    let focus = Cursor.tcFocus tc
    return $
      focus
        { VT.treeRecurClosed = True
        , VT.treeNode = case VT.treeNode focus of
            VT.TNStruct struct -> VT.TNStruct $ struct{VT.stcClosed = True}
            _ -> VT.treeNode focus
        }

{- | Convert the first identifier of the reference to absolute tree addr.

It does not follow the reference.
-}
refToPotentialAddr ::
  (Env r s m) =>
  Path.Reference ->
  Maybe (Path.TreeAddr, Path.TreeAddr) ->
  Cursor.TreeCursor VT.Tree ->
  m (Maybe Path.TreeAddr)
refToPotentialAddr ref origAddrsM tc = do
  let fstSel = fromJust $ Path.headSel ref
  ident <- selToIdent fstSel
  let f x = searchTCIdent ident x >>= (\r -> return $ fst <$> r)

  -- Search the address of the first identifier, whether from the current env or the original env.
  maybe
    (f tc)
    ( \(origSubTAddr, _) -> inAbsAddrTCMust origSubTAddr tc f
    )
    origAddrsM

-- | Locate the reference and if the reference is found, run the action.
locateRefAndRun ::
  (Env r s m) =>
  Path.Reference ->
  Cursor.TreeCursor VT.Tree ->
  (Cursor.TreeCursor VT.Tree -> m (Either VT.Tree (Maybe a))) ->
  m (Either VT.Tree (Maybe a))
locateRefAndRun ref tc f = do
  tarE <- goTCLAAddr ref tc
  case tarE of
    Left err -> return $ Left err
    Right Nothing -> return $ Right Nothing
    Right (Just tarTC) -> f tarTC

-- | Locate the node in the lowest ancestor tree by given reference path. The path must start with a locatable ident.
goTCLAAddr ::
  (Env r s m) => Path.Reference -> Cursor.TreeCursor VT.Tree -> m (Either VT.Tree (Maybe (Cursor.TreeCursor VT.Tree)))
goTCLAAddr ref tc = do
  when (Path.isRefEmpty ref) $ throwErrSt "empty reference"
  let fstSel = fromJust $ Path.headSel ref
  ident <- selToIdent fstSel
  searchTCIdent ident tc >>= \case
    Nothing -> return . Left $ VT.mkBottomTree $ printf "identifier %s is not found" (show fstSel)
    Just (identAddr, _) -> do
      identTCM <- goTCAbsAddr identAddr tc
      maybe
        (throwErrSt $ printf "failed to go to the ident addr %s" (show identAddr))
        ( \identTC -> do
            -- The ref is non-empty, so the rest must be a valid addr.
            let rest = fromJust $ Path.tailRef ref
                r = goDownTCAddr (Path.refToAddr rest) identTC
            return $ Right r
        )
        identTCM

-- | TODO: do we need this?
searchRMLetBindValue :: (RM.ReduceMonad s r m) => String -> m (Maybe VT.Tree)
searchRMLetBindValue ident = do
  m <- searchRMIdent ident
  case m of
    Just (addr, True) -> do
      r <- inAbsAddrRMMust addr $ do
        identTC <- RM.getRMCursor
        -- ident must be found. Mark the ident as referred if it is a let binding.
        RM.putRMCursor $ _markTCFocusReferred identTC
        RM.getRMTree
      return $ Just r
    _ -> return Nothing

inAbsAddrRMMust :: (RM.ReduceMonad s r m, Show a) => Path.TreeAddr -> m a -> m a
inAbsAddrRMMust dst f = RM.debugSpanRM (printf "inAbsAddrRMMust: dst: %s" (show dst)) $ do
  addr <- RM.getRMAbsAddr
  m <- inAbsAddrRM dst f
  case m of
    Just r -> return r
    Nothing -> throwErrSt $ printf "failed to go to the dst %s, from: %s" (show dst) (show addr)

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrRM :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m a -> m (Maybe a)
inAbsAddrRM p f = do
  origAbsAddr <- RM.getRMAbsAddr

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
  whenM :: (RM.ReduceMonad s r m) => m Bool -> m a -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then Just <$> g else return Nothing

-- | Go to the absolute addr in the tree.
goRMAbsAddr :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m Bool
goRMAbsAddr dst = do
  when (Path.headSeg dst /= Just Path.RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  RM.propUpRMUntilSeg Path.RootTASeg
  let dstNoRoot = fromJust $ Path.tailTreeAddr dst
  RM.descendRM dstNoRoot

goRMAbsAddrMust :: (RM.ReduceMonad s r m) => Path.TreeAddr -> m ()
goRMAbsAddrMust dst = do
  from <- RM.getRMAbsAddr
  ok <- goRMAbsAddr dst
  unless ok $ do
    tc <- RM.getRMCursor
    case VT.treeNode (Cursor.tcFocus tc) of
      -- If the focus of the cursor is a bottom, it is not a problem.
      VT.TNBottom _ -> return ()
      _ -> throwErrSt $ printf "failed to go to the addr %s, from: %s, tc: %s" (show dst) (show from) (show tc)

addrHasDef :: Path.TreeAddr -> Bool
addrHasDef p =
  any
    ( \case
        Path.StructTASeg (Path.StringTASeg s) -> fromMaybe False $ do
          typ <- VT.getFieldType s
          return $ typ == VT.SFTDefinition
        _ -> False
    )
    $ Path.addrToNormOrdList p

-- | Mark the let binding specified by the its name selector as referred if the focus of the cursor is a let binding.
_markTCFocusReferred :: Cursor.TreeCursor VT.Tree -> Cursor.TreeCursor VT.Tree
_markTCFocusReferred tc@(Cursor.TreeCursor sub ((seg@(Path.StructTASeg (Path.LetTASeg name)), par) : cs)) =
  maybe
    tc
    ( \struct ->
        let newPar = VT.setTN par (VT.TNStruct $ VT.markLetBindReferred name struct)
         in -- sub is not changed.
            Cursor.TreeCursor sub ((seg, newPar) : cs)
    )
    (VT.getStructFromTree par)
_markTCFocusReferred tc = tc

selToIdent :: (Env r s m) => Path.Selector -> m String
selToIdent (Path.StringSel s) = return s
selToIdent _ = throwErrSt "invalid selector"

{- | Search in the tree for the first identifier that can match the name.

Return if the identifier address and whether it is a let binding.
-}
searchRMIdent :: (RM.ReduceMonad s r m) => String -> m (Maybe (Path.TreeAddr, Bool))
searchRMIdent name = do
  tc <- RM.getRMCursor
  searchTCIdent name tc

{- | Search in the parent scope for the first identifier that can match the segment. Also return if the identifier is a
 let binding.
-}
searchRMIdentInPar :: (RM.ReduceMonad s r m) => String -> m (Maybe (Path.TreeAddr, Bool))
searchRMIdentInPar name = do
  ptc <- do
    tc <- RM.getRMCursor
    maybe (throwErrSt "already on the top") return $ Cursor.parentTC tc
  if Cursor.isTCTop ptc
    then return Nothing
    else searchTCIdent name ptc

{- | Search in the tree for the first identifier that can match the name.

Searching identifiers only searches for the identifiers declared in the block, not for the identifiers added by
unification with embeddings.

Return a pair. The first is address of the identifier, the second is the identifier is a let binding.

The child value will not be propagated to the parent block. Propagation is not needed because all static fields should
already exist.

The tree cursor must at least have the root segment.
-}
searchTCIdent :: (Env r s m) => String -> Cursor.TreeCursor VT.Tree -> m (Maybe (Path.TreeAddr, Bool))
searchTCIdent name tc = do
  subM <- findSubInBlock name $ Cursor.tcFocus tc
  r <-
    maybe
      (goUp tc)
      ( \(sub, isLB) ->
          let
            -- The ident address is the address of the value, with the updated segment paired with the it.
            newTC = Cursor.mkSubTC (mkSeg isLB) sub tc
           in
            return $ Just (Cursor.tcTreeAddr newTC, isLB)
      )
      subM

  logDebugStr $ printf "searchTCIdent: name: %s, cur_path: %s, result: %s" name (show $ Cursor.tcTreeAddr tc) (show r)
  return r
 where
  mkSeg isLB = Path.StructTASeg $ if isLB then Path.LetTASeg name else Path.StringTASeg name

  goUp :: (Env r s m) => Cursor.TreeCursor VT.Tree -> m (Maybe (Path.TreeAddr, Bool))
  goUp (Cursor.TreeCursor _ [(Path.RootTASeg, _)]) = return Nothing -- stop at the root.
  goUp utc = do
    ptc <- maybe (throwErrSt "already on the top") return $ Cursor.parentTC utc
    searchTCIdent name ptc

  -- TODO: findSub for default disjunct
  findSubInBlock :: (Env r s m) => String -> VT.Tree -> m (Maybe (VT.Tree, Bool))
  findSubInBlock ident t = case VT.treeNode t of
    VT.TNStruct struct -> do
      let
        inBlock = ident `Set.member` VT.stcBlockIdents struct
        m =
          catMaybes
            [ do
                sf <- VT.lookupStructIdentField ident struct
                return (VT.ssfValue sf, False)
            , do
                lb <- VT.lookupStructLet ident struct
                return (VT.lbValue lb, True)
            ]
      if inBlock
        then case m of
          [] -> return Nothing
          [x] -> return $ Just x
          _ -> return $ Just (VT.mkBottomTree $ printf "multiple fields found for %s" ident, False)
        else return Nothing
    VT.TNMutable (VT.Compreh c) -> return Nothing
    _ -> return Nothing

{- | Go to the absolute addr in the tree. No propagation is involved.

The tree must have all the latest changes.
-}
goTCAbsAddr :: (Env r s m) => Path.TreeAddr -> Cursor.TreeCursor VT.Tree -> m (Maybe (Cursor.TreeCursor VT.Tree))
goTCAbsAddr dst tc = do
  when (Path.headSeg dst /= Just Path.RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  top <- topTC tc
  let dstNoRoot = fromJust $ Path.tailTreeAddr dst
  return $ goDownTCAddr dstNoRoot top

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrTCMust ::
  (Env r s m) =>
  Path.TreeAddr ->
  Cursor.TreeCursor VT.Tree ->
  (Cursor.TreeCursor VT.Tree -> m a) ->
  m a
inAbsAddrTCMust p tc f = do
  tarM <- goTCAbsAddr p tc
  maybe (throwErrSt $ printf "%s is not found" (show p)) f tarM

mustReferableAddr :: (Env r s m) => Path.TreeAddr -> m Path.TreeAddr
mustReferableAddr addr = do
  let r = Path.referableAddr addr
  when (isNothing r) $ throwErrSt $ printf "the addr %s is not referable" (show addr)
  return $ fromJust r