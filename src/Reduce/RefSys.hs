{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RefSys where

import qualified Common
import Control.Monad (unless, when)
import qualified Cursor
import Data.Maybe (catMaybes, fromJust, fromMaybe, isNothing)
import qualified Data.Set as Set
import Exception (throwErrSt)
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import TCOps (goDownTCAddr, topTC)
import qualified TCOps
import Text.Printf (printf)
import Util (debugInstant, debugSpan, logDebugStr)
import qualified Value.Tree as VT

{- | Index the tree with the segments.

It returns a non-ref tree if there is tree.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
index ::
  (RM.ReduceMonad s r m) =>
  Maybe Path.TreeAddr ->
  VT.RefArg VT.Tree ->
  TCOps.TrCur ->
  m (Maybe VT.Tree)
index origAddrsM arg@(VT.RefPath var _) tc = RM.debugSpanRM (printf "index: var: %s" var) tc $ do
  refRestPathM <- resolveRefValPath arg tc
  logDebugStr $ printf "index: refRestPathM is reduced to %s" (show refRestPathM)
  case refRestPathM of
    -- Incompleteness
    Nothing -> return Nothing
    Just refRestPath@(Path.ValPath sels) -> do
      lbM <- searchLetBindValue var tc
      case lbM of
        Just lb -> do
          logDebugStr $ printf "index: let %s bind value is %s" var (show lb)
          case sels of
            -- If there are no selectors, it is a simple reference to the let value. We treat it like pending value.
            [] -> return $ Just lb
            _ -> do
              let selTs = map selToTree sels
              case VT.treeNode lb of
                -- If the let value is a reference, we append the selectors to the reference.
                VT.TNMutable m
                  | Just ref <- VT.getRefFromMutable m -> do
                      let newRefTree =
                            VT.mkMutableTree $
                              VT.Ref $
                                ref
                                  { VT.refArg = VT.appendRefArgs selTs (VT.refArg ref)
                                  , VT.refOrigAddrs = origAddrsM
                                  }
                          refTC = newRefTree `Cursor.setTCFocus` tc
                      rTC <- resolveTC refTC
                      return $ Cursor.tcFocus <$> rTC
                _ -> do
                  let
                    newRef = (VT.mkIndexRef (lb : selTs)){VT.refOrigAddrs = origAddrsM}
                    refTC = TCOps.setTCFocusTN (VT.TNMutable $ VT.Ref newRef) tc
                  index origAddrsM (VT.refArg newRef) refTC
        _ -> do
          -- Use the index's original addrs since it is the referable node
          newRef <- VT.mkRefFromValPath VT.mkAtomTree var refRestPath
          let
            refMut = VT.TNMutable $ VT.Ref (newRef{VT.refOrigAddrs = origAddrsM})
            -- We have to keep the tree's attributes because resolveTC might find the new tree and build expression from
            -- the tree if the ref is a structural cycle.
            refTC = TCOps.setTCFocusTN refMut tc
          rTC <- resolveTC refTC
          return $ Cursor.tcFocus <$> rTC

-- in-place expression, like ({}).a, or regular functions. Notice the selector must exist.
index _ arg@(VT.RefIndex _) tc = RM.debugSpanRM "index" tc $ do
  idxValPathM <- resolveRefValPath arg tc
  logDebugStr $ printf "index: idxValPathM is reduced to %s" (show idxValPathM)

  operandTC <- TCOps.goDownTCSegMust (Path.MutableArgTASeg 0) tc
  reducedOperandM <- Mutate.reduceToConcrete operandTC
  let
    tarTCM = do
      idxValPath <- idxValPathM
      reducedOperand <- reducedOperandM
      -- Use the tc as the environment for the reduced operand.
      let reducedTC = reducedOperand `Cursor.setTCFocus` tc
      case VT.treeNode reducedOperand of
        -- If the operand evaluates to a bottom, we should return the bottom.
        VT.TNBottom _ -> return reducedTC
        _ -> TCOps.goDownTCAddr (Path.valPathToAddr idxValPath) reducedTC

  maybe
    (return Nothing)
    ( \tarTC -> do
        rTC <- resolveTC tarTC
        return $ Cursor.tcFocus <$> rTC
    )
    tarTCM

resolveRefValPath :: (RM.ReduceMonad s r m) => VT.RefArg VT.Tree -> TCOps.TrCur -> m (Maybe Path.ValPath)
resolveRefValPath arg tc = do
  l <- case arg of
    (VT.RefPath _ sels) -> return $ zip [0 ..] sels
    (VT.RefIndex (_ : rest)) -> return $ zip [1 ..] rest
    _ -> throwErrSt "invalid index"
  m <-
    mapM
      ( \(i, _) -> do
          argTC <- TCOps.goDownTCSegMust (Path.MutableArgTASeg i) tc
          Mutate.reduceToConcrete argTC
      )
      l
  return $ VT.treesToValPath . Data.Maybe.catMaybes $ m

selToTree :: Path.Selector -> VT.Tree
selToTree (Path.StringSel s) = VT.mkAtomTree $ VT.String s
selToTree (Path.IntSel i) = VT.mkAtomTree $ VT.Int (fromIntegral i)

{- | Resolve the focus of the tree cursor.

If the focus of the tree cursor is not a reference, then returns the tree cursor.
If the focus is a reference, it dereferences the reference.
-}
resolveTC :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m (Maybe TCOps.TrCur)
resolveTC _tc = do
  -- Make deref see the latest tree, even with unreduced nodes.
  tc <- TCOps.syncTC _tc
  RM.debugSpanArgsRM "resolveTC" (show tc) tc $ do
    let focus = Cursor.tcFocus tc
    case VT.treeNode focus of
      VT.TNMutable (VT.Ref ref)
        -- If the valPath is not ready, return not found.
        | Nothing <- VT.valPathFromRef VT.getAtomFromTree ref -> return Nothing
        | Just valPath <- VT.valPathFromRef VT.getAtomFromTree ref -> do
            let
              selfAddr = Path.noSubValAddr (Cursor.tcTreeAddr tc)
              trail = Set.fromList [selfAddr]
              origAddrsM = VT.refOrigAddrs ref

            watchRefRM valPath origAddrsM tc
            getDstTC valPath origAddrsM trail tc
      _ -> return $ Just tc

{- | Monitor the absoluate address of the reference searched from the original environment by adding a notifier pair
from the current environment address to the searched address.

If the reference is not found, the function does nothing.

Duplicate cases are handled by the addCtxNotifPair.
-}
watchRefRM ::
  (RM.ReduceMonad s r m) =>
  Path.ValPath ->
  Maybe Path.TreeAddr ->
  TCOps.TrCur ->
  m ()
watchRefRM ref origAddrsM tc = do
  srcAddrM <-
    refToPotentialAddr ref origAddrsM tc >>= \xM -> return $ do
      x <- xM
      Path.referableAddr x
  -- Since we are in the /sv environment, we need to get the referable addr.
  let recvAddr = Path.noSubValAddr $ Cursor.tcTreeAddr tc

  maybe
    (logDebugStr $ printf "watchRefRM: ref %s is not found" (show ref))
    ( \srcAddr -> do
        ctx <- RM.getRMContext
        RM.putRMContext $ Common.addCtxNotifPair ctx (srcAddr, recvAddr)
        logDebugStr $ printf "watchRefRM: (%s -> %s)" (show srcAddr) (show recvAddr)
    )
    srcAddrM

{- | Get the tree cursor pointed by the reference.

If the reference value is another reference, it will follow the reference.
-}
getDstTC ::
  (RM.ReduceMonad s r m) =>
  Path.ValPath ->
  Maybe Path.TreeAddr ->
  Set.Set Path.TreeAddr ->
  TCOps.TrCur ->
  m (Maybe TCOps.TrCur)
getDstTC ref origAddrsM trail tc = RM.debugSpanArgsRM
  (printf "getDstTC: ref: %s" (show ref))
  (printf "trail: %s" (show $ Set.toList trail))
  tc
  $ do
    let addr = Cursor.tcTreeAddr tc

    rE <- getDstRawOrErr ref origAddrsM trail tc
    case rE of
      Left err -> return $ Just $ err `Cursor.setTCFocus` tc
      Right Nothing -> return Nothing
      Right (Just tarTC) -> do
        raw <- copyRefVal (Cursor.tcFocus tarTC)
        newVal <- processCopiedRaw addr trail tarTC raw
        RM.debugInstantRM
          "getDstTC"
          ( printf
              "ref: %s, dstVal: %s, raw: %s, newVal: %s"
              (show ref)
              (show $ Cursor.tcFocus tarTC)
              (show raw)
              (show newVal)
          )
          tc
        tryFollow trail (newVal `Cursor.setTCFocus` tarTC)

{- | Try to follow the reference if the new value is a concrete reference.

If the reference is not concrete, return Nothing.
-}
tryFollow ::
  (RM.ReduceMonad s r m) =>
  Set.Set Path.TreeAddr ->
  TCOps.TrCur ->
  m (Maybe TCOps.TrCur)
tryFollow trail tc = case VT.treeNode (Cursor.tcFocus tc) of
  VT.TNMutable (VT.Ref ref) ->
    maybe
      -- If we can not get the complete ref path, return nothing.
      (return Nothing)
      ( \newRef -> do
          let dstAddr = Cursor.tcTreeAddr tc
          getDstTC newRef (VT.refOrigAddrs ref) (Set.insert dstAddr trail) tc
      )
      (VT.valPathFromRef VT.getAtomFromTree ref)
  _ -> return (Just tc)

{- | The result of getting the destination value.

The result is either an error, such as a bottom or a structural cycle, or a valid value.
-}
type DstTC = Either VT.Tree (Maybe TCOps.TrCur)

{- | Get the processed tree cursor pointed by the reference.

If the reference addr is self or visited, then return the tuple of the absolute addr of the start of the cycle and
the cycle tail relative addr.
-}
getDstRawOrErr ::
  (RM.ReduceMonad s r m) =>
  Path.ValPath ->
  -- | The original addresses of the reference.
  Maybe Path.TreeAddr ->
  -- | keeps track of the followed *referable* addresses.
  Set.Set Path.TreeAddr ->
  -- | The cursor should be the reference.
  TCOps.TrCur ->
  m DstTC
getDstRawOrErr valPath origAddrsM trail refTC =
  debugSpan
    "deref_getDstTCOrErr"
    (show $ Cursor.tcTreeAddr refTC)
    (Just $ printf "valPath: %s, origAddrsM: %s, trail: %s" (show valPath) (show origAddrsM) (show $ Set.toList trail))
    (Cursor.tcFocus refTC)
    $ traceAdapt
    $ do
      let
        -- srcAddr is the starting address of searching for the reference.
        f x srcAddr = locateRefAndRun valPath x (_detectCycle valPath srcAddr trail)

      maybe
        (f refTC (Cursor.tcTreeAddr refTC))
        -- If the ref is an outer reference, we should first go to the original value address.
        ( \origValAddr -> inAbsAddrTCMust origValAddr refTC $ \tarTC ->
            -- If the ref is an outer reference inside the referenced value, we should check if the ref leads to
            -- infinite structure (structural cycle).
            -- For example, { x: a, y: 1, a: {b: y} }, where /a is the address of the subt value.
            -- The "y" in the struct {b: y} is an outer reference.
            -- We should first go to the original value address, which is /a/b.
            -- infE <- locateRefAndRun ref tarTC (_checkInf ref srcAddr origValAddr)
            f tarTC origValAddr
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
  (Common.Env r s m) =>
  Path.ValPath ->
  Path.TreeAddr ->
  Set.Set Path.TreeAddr ->
  TCOps.TrCur ->
  m DstTC
_detectCycle valPath srcAddr trail tarTC = do
  let
    dstAddr = Cursor.tcTreeAddr tarTC
    canSrcAddr = Path.canonicalizeAddr srcAddr
    canDstAddr = Path.canonicalizeAddr dstAddr
  debugSpan
    "deref_detectCycle"
    (show srcAddr)
    ( Just $
        printf
          "valPath: %s, trail: %s, dstAddr: %s, canSrcAddr: %s, canDstAddr: %s"
          (show valPath)
          (show $ Set.toList trail)
          (show dstAddr)
          (show canSrcAddr)
          (show canDstAddr)
    )
    (Cursor.tcFocus tarTC)
    $ traceAdapt
    $ do
      let tar = Cursor.tcFocus tarTC
      val <-
        if
          -- The bottom must return early so that the identifier not found error would not be replaced with the cycle error.
          | Common.isTreeBottom tar -> return tar
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
                  (show valPath)
                  (show dstAddr)
                  (show $ Set.toList trail)
              return (VT.setTN tar VT.TNRefCycle)
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
              return (VT.setTN tar VT.TNRefCycle)
          -- According to spec,
          -- If a node "a" references an ancestor node, we call it and any of its field values a.f cyclic. So if "a" is
          -- cyclic, all of its descendants are also regarded as cyclic.
          | Path.isPrefix canDstAddr canSrcAddr && canSrcAddr /= canDstAddr ->
              return $ tar{VT.treeIsCyclic = True}
          | otherwise -> return tar
      return . Right $ Just (val `Cursor.setTCFocus` tarTC)
 where
  traceAdapt f = do
    r <- f
    let after = case r of
          Left err -> err
          Right m -> maybe (VT.mkBottomTree "Healthy Not found") Cursor.tcFocus m
    return (r, after)

{- | Copy the value of the reference.

The arg trail is used to decide whether to close the deref'd value.

The ReduceTCMonad is only used to run the evalExpr.

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
    VT.TNRefCycle -> return tar
    VT.TNAtomCnstr c -> return (VT.mkAtomVTree $ VT.cnsAtom c)
    _ -> do
      e <- maybe (Common.buildASTExpr False tar) return (VT.treeExpr tar)
      RM.evalExprRM e

{- | Process the copied raw value.

The tree cursor is the target cursor without the copied raw value.
-}
processCopiedRaw ::
  (RM.ReduceMonad s r m) => Path.TreeAddr -> Set.Set Path.TreeAddr -> TCOps.TrCur -> VT.Tree -> m VT.Tree
processCopiedRaw srcAddr trail tarTC raw = do
  let dstAddr = Cursor.tcTreeAddr tarTC
  -- evaluate the original expression.
  marked <- markOuterIdents srcAddr (raw `Cursor.setTCFocus` tarTC)
  let visited = Set.insert dstAddr trail
  closeMarked <- checkRefDef marked visited

  val <-
    if VT.treeIsCyclic (Cursor.tcFocus tarTC)
      then markCyclic closeMarked
      else return closeMarked

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

markCyclic :: (Common.Env r s m) => VT.Tree -> m VT.Tree
markCyclic val = do
  utc <- TCOps.traverseTCSimple VT.subNodes mark valTC
  return $ Cursor.tcFocus utc
 where
  -- Create a tree cursor based on the value.
  valTC = Cursor.TreeCursor val [(Path.RootTASeg, VT.mkNewTree VT.TNTop)]

  mark :: (Common.Env r s m) => TCOps.TrCur -> m VT.Tree
  mark tc = do
    let focus = Cursor.tcFocus tc
    return $ focus{VT.treeIsCyclic = True}

{- | Mark all outer references inside a block with original value address.

The outer references are the reference nodes inside (not equal to) a block pointing to the identifiers that are
1. out of the block, and
2. not accessible from the current reducing node

This is needed because after copying the value, the original scope has been lost.

For example, given the following tree:

y: a.s
a: {
	s: {j1: i2}
	i2: 2
}

The block to copy is {j1: i2}. We need to mark the i2 because i2 is out of the block and not accessible from the y.

Consider the example,

y: a.s
a: {
	s: {j1: i2, i2: 2}
}

The i2 is not marked because it is within the block.

Consider the example,

y: a.s
i2: 2
a: {
  s: {j1: i2}
}

The i2 is not marked because it is out of the block but accessible from the y.

However, the following example is valid:

y: a.s
i2: 2
a: {
  i2: 3
  s: {j1: i2}
}

The i2 is marked because it is out of the block but the i2 in the block is not accessible from the y.
-}
markOuterIdents ::
  (RM.ReduceMonad s r m) =>
  -- | The current tree cursor.
  Path.TreeAddr ->
  TCOps.TrCur ->
  m VT.Tree
markOuterIdents srcAddr ptc = RM.debugSpanRM "markOuterIdents" ptc $ do
  let blockAddr = Cursor.tcTreeAddr ptc
  utc <- TCOps.traverseTCSimple VT.subNodes (mark blockAddr) ptc
  debugInstant
    "markOuterRefs"
    (show blockAddr)
    (Just $ printf "blockAddr: %s, result: %s" (show blockAddr) (VT.treeFullStr 0 $ Cursor.tcFocus utc))
  return $ Cursor.tcFocus utc
 where
  -- Mark the outer references with the original value address.
  mark :: (RM.ReduceMonad s r m) => Path.TreeAddr -> TCOps.TrCur -> m VT.Tree
  mark blockAddr tc = do
    let focus = Cursor.tcFocus tc
    rM <- case VT.getMutableFromTree focus of
      Just (VT.Ref rf) -> return $ do
        newValPath <- VT.valPathFromRef VT.getAtomFromTree rf
        return (newValPath, \as -> VT.setTN focus $ VT.TNMutable . VT.Ref $ rf{VT.refOrigAddrs = Just as})
      _ -> return Nothing
    maybe
      (return focus)
      ( \(valPath, f) -> do
          isOuter <- isOuterScope valPath srcAddr blockAddr tc
          return $
            if isOuter
              then f (Cursor.tcTreeAddr tc)
              else focus
      )
      rM

-- | Check if the reference is an outer reference.
isOuterScope ::
  (RM.ReduceMonad s r m) =>
  Path.ValPath ->
  Path.TreeAddr ->
  Path.TreeAddr ->
  TCOps.TrCur ->
  m Bool
isOuterScope valPath srcAddr blockAddr tc = do
  tarIdentAddrM <- searchIdent valPath tc
  isOuter <-
    maybe
      (return False)
      ( \tarIdentAddr -> do
          let
            tarIdentAccessible = Path.isPrefix tarIdentAddr srcAddr
            tarIdentInBlock = Path.isPrefix blockAddr tarIdentAddr && blockAddr /= tarIdentAddr
          return $ not (tarIdentAccessible || tarIdentInBlock)
      )
      tarIdentAddrM
  debugInstant "isOuterScope" (show $ Cursor.tcTreeAddr tc) $
    Just $
      printf
        "valPath: %s, srcAddr: %s, blockAddr: %s, tarIdentAddrM: %s, isOuterScope: %s"
        (show valPath)
        (show srcAddr)
        (show blockAddr)
        (show tarIdentAddrM)
        (show isOuter)
  return isOuter
 where
  -- Search the first identifier of the reference and convert it to absolute tree addr if it exists.
  searchIdent :: (RM.ReduceMonad s r m) => Path.ValPath -> TCOps.TrCur -> m (Maybe Path.TreeAddr)
  searchIdent ref xtc = do
    let fstSel = fromJust $ Path.headSel ref
    ident <- selToIdent fstSel
    resM <- searchTCIdent ident xtc
    return $ Cursor.tcTreeAddr . fst <$> resM

markRecurClosed :: (Common.Env r s m) => VT.Tree -> m VT.Tree
markRecurClosed val = do
  utc <- TCOps.traverseTCSimple VT.subNodes mark valTC
  return $ Cursor.tcFocus utc
 where
  -- Create a tree cursor based on the value.
  valTC = Cursor.TreeCursor val [(Path.RootTASeg, VT.mkNewTree VT.TNTop)]
  mark :: (Common.Env r s m) => TCOps.TrCur -> m VT.Tree
  mark tc = do
    let focus = Cursor.tcFocus tc
    return $
      focus
        { VT.treeRecurClosed = True
        , VT.treeNode = case VT.treeNode focus of
            VT.TNStruct struct -> VT.TNStruct $ struct{VT.stcClosed = True}
            _ -> VT.treeNode focus
        }

-- | Check if the reference leads to a structural cycle.
isRefInf :: (RM.ReduceMonad s r m) => Path.ValPath -> Path.TreeAddr -> TCOps.TrCur -> m Bool
isRefInf valPath blockAddr tc = do
  rE <- locateRefAndRun valPath tc $ \tarTC -> do
    let
      fromAddr = Cursor.tcTreeAddr tc
      canFromAddr = Path.canonicalizeAddr fromAddr
      -- tarAddr is the address of the referenced value.
      tarAddr = Cursor.tcTreeAddr tarTC
      canBlockAddr = Path.canonicalizeAddr blockAddr
      canTarAddr = Path.canonicalizeAddr tarAddr
    -- Pointing to ancestor generates a structural cycle. The current tree cursor must be a sub value of the block.
    return $ Right $ Just $ Path.isPrefix canTarAddr canBlockAddr && canFromAddr /= canBlockAddr
  case rE of
    Right (Just r) -> return r
    _ -> return False

{- | Convert the first identifier of the reference to absolute tree addr.

It does not follow the reference.
-}
refToPotentialAddr ::
  (RM.ReduceMonad s r m) =>
  Path.ValPath ->
  Maybe Path.TreeAddr ->
  TCOps.TrCur ->
  m (Maybe Path.TreeAddr)
refToPotentialAddr ref origAddrsM tc = do
  let fstSel = fromJust $ Path.headSel ref
  ident <- selToIdent fstSel
  let f x = searchTCIdent ident x >>= (\r -> return $ Cursor.tcTreeAddr . fst <$> r)

  -- Search the address of the first identifier, whether from the current env or the original env.
  maybe
    (f tc)
    ( \origValAddr -> inAbsAddrTCMust origValAddr tc f
    )
    origAddrsM

-- | Locate the reference and if the reference is found, run the action.
locateRefAndRun ::
  (RM.ReduceMonad s r m) =>
  Path.ValPath ->
  TCOps.TrCur ->
  (TCOps.TrCur -> m (Either VT.Tree (Maybe a))) ->
  m (Either VT.Tree (Maybe a))
locateRefAndRun ref tc f = do
  tarE <- goTCLAAddr ref tc
  case tarE of
    Left err -> return $ Left err
    Right Nothing -> return $ Right Nothing
    Right (Just tarTC) -> f tarTC

-- | Locate the node in the lowest ancestor tree by given reference path. The path must start with a locatable ident.
goTCLAAddr ::
  (RM.ReduceMonad s r m) => Path.ValPath -> TCOps.TrCur -> m (Either VT.Tree (Maybe TCOps.TrCur))
goTCLAAddr valPath tc = do
  when (Path.isValPathEmpty valPath) $ throwErrSt "empty valPath"
  let fstSel = fromJust $ Path.headSel valPath
  ident <- selToIdent fstSel
  searchTCIdent ident tc >>= \case
    Nothing -> return . Left $ VT.mkBottomTree $ printf "identifier %s is not found" (show fstSel)
    Just (identTC, _) -> do
      -- The ref is non-empty, so the rest must be a valid addr.
      let rest = fromJust $ Path.tailValPath valPath
          r = goDownTCAddr (Path.valPathToAddr rest) identTC
      return $ Right r

inAbsAddrRMMust :: (RM.ReduceTCMonad s r m, Show a) => Path.TreeAddr -> m a -> m a
inAbsAddrRMMust dst f = RM.debugSpanTM (printf "inAbsAddrRMMust: dst: %s" (show dst)) $ do
  addr <- RM.getTMAbsAddr
  m <- inAbsAddrRM dst f
  case m of
    Just r -> return r
    Nothing -> throwErrSt $ printf "failed to go to the dst %s, from: %s" (show dst) (show addr)

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrRM :: (RM.ReduceTCMonad s r m) => Path.TreeAddr -> m a -> m (Maybe a)
inAbsAddrRM p f = do
  origAbsAddr <- RM.getTMAbsAddr

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
  whenM :: (RM.ReduceTCMonad s r m) => m Bool -> m a -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then Just <$> g else return Nothing

-- | Go to the absolute addr in the tree.
goRMAbsAddr :: (RM.ReduceTCMonad s r m) => Path.TreeAddr -> m Bool
goRMAbsAddr dst = do
  when (Path.headSeg dst /= Just Path.RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  RM.propUpTMUntilSeg Path.RootTASeg
  let dstNoRoot = fromJust $ Path.tailTreeAddr dst
  RM.descendTM dstNoRoot

goRMAbsAddrMust :: (RM.ReduceTCMonad s r m) => Path.TreeAddr -> m ()
goRMAbsAddrMust dst = do
  from <- RM.getTMAbsAddr
  ok <- goRMAbsAddr dst
  unless ok $ do
    tc <- RM.getTMCursor
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
_markTCFocusReferred :: TCOps.TrCur -> TCOps.TrCur
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

selToIdent :: (Common.Env r s m) => Path.Selector -> m String
selToIdent (Path.StringSel s) = return s
selToIdent _ = throwErrSt "invalid selector"

{- | Search in the parent scope for the first identifier that can match the segment.

Also return if the identifier is a let binding.
-}
searchTCIdentInPar :: (RM.ReduceMonad s r m) => String -> TCOps.TrCur -> m (Maybe (Path.TreeAddr, Bool))
searchTCIdentInPar name tc = do
  ptc <- Cursor.parentTCMust tc
  if Cursor.isTCTop ptc
    then return Nothing
    else do
      m <- searchTCIdent name ptc
      return $ maybe Nothing (\(x, y) -> Just (Cursor.tcTreeAddr x, y)) m

{- | Search in the tree for the first identifier that can match the name.

Searching identifiers only searches for the identifiers declared in the block, not for the identifiers added by
unification with embeddings.

Return a pair. The first is address of the identifier, the second is the identifier is a let binding.

The child value will not be propagated to the parent block. Propagation is not needed because all static fields should
already exist.

The tree cursor must at least have the root segment.
-}
searchTCIdent :: (RM.ReduceMonad s r m) => String -> TCOps.TrCur -> m (Maybe (TCOps.TrCur, Bool))
searchTCIdent name tc = do
  subM <- findSubInBlock name $ Cursor.tcFocus tc
  r <-
    maybe
      (goUp tc)
      ( \(sub, isLB) -> do
          let
            -- The ident address is the address of the value, with the updated segment paired with the it.
            identTC = Cursor.mkSubTC (mkSeg isLB) sub tc
          when isLB $ do
            -- Mark the ident as referred if it is a let binding.
            RM.markRMLetReferred (Cursor.tcTreeAddr identTC)
            unrefLets <- RM.getRMUnreferredLets
            RM.debugInstantRM
              "searchLetBindValue"
              (printf "ident: %s, unrefLets: %s" (show $ Cursor.tcTreeAddr identTC) (show unrefLets))
              tc
          return $ Just (identTC, isLB)
      )
      subM

  logDebugStr $ printf "searchTCIdent: name: %s, cur_path: %s, result: %s" name (show $ Cursor.tcTreeAddr tc) (show r)
  return r
 where
  mkSeg isLB = Path.StructTASeg $ if isLB then Path.LetTASeg name else Path.StringTASeg name

  goUp :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m (Maybe (TCOps.TrCur, Bool))
  goUp (Cursor.TreeCursor _ [(Path.RootTASeg, _)]) = return Nothing -- stop at the root.
  goUp utc = do
    ptc <- maybe (throwErrSt "already on the top") return $ Cursor.parentTC utc
    searchTCIdent name ptc

  -- TODO: findSub for default disjunct
  findSubInBlock :: (Common.Env r s m) => String -> VT.Tree -> m (Maybe (VT.Tree, Bool))
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

searchLetBindValue :: (RM.ReduceMonad s r m) => String -> TCOps.TrCur -> m (Maybe VT.Tree)
searchLetBindValue ident tc = do
  m <- searchTCIdent ident tc
  case m of
    Just (identTC, True) -> return $ Just (Cursor.tcFocus identTC)
    _ -> return Nothing

{- | Go to the absolute addr in the tree. No propagation is involved.

The tree must have all the latest changes.
-}
goTCAbsAddr :: (Common.Env r s m) => Path.TreeAddr -> TCOps.TrCur -> m (Maybe TCOps.TrCur)
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
  (Common.Env r s m) =>
  Path.TreeAddr ->
  TCOps.TrCur ->
  (TCOps.TrCur -> m a) ->
  m a
inAbsAddrTCMust p tc f = do
  tarM <- goTCAbsAddr p tc
  maybe (throwErrSt $ printf "%s is not found" (show p)) f tarM

mustReferableAddr :: (Common.Env r s m) => Path.TreeAddr -> m Path.TreeAddr
mustReferableAddr addr = do
  let r = Path.referableAddr addr
  when (isNothing r) $ throwErrSt $ printf "the addr %s is not referable" (show addr)
  return $ fromJust r