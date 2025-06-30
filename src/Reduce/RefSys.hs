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
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, isNothing)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import Path
import Reduce.RMonad (
  ReduceMonad,
  ReduceTCMonad,
  debugInstantOpRM,
  debugInstantRM,
  debugSpanArgsRM,
  debugSpanRM,
  descendTM,
  evalExprRM,
  getRMContext,
  getRMUnreferredLets,
  getTMAbsAddr,
  getTMCursor,
  markRMLetReferred,
  propUpTMUntilSeg,
  putRMContext,
 )
import {-# SOURCE #-} Reduce.Root (reduceToNonMut)
import Text.Printf (printf)
import Value

data DerefResult = DerefResult
  { drValue :: Maybe Tree
  , drIsComprehBinding :: Bool
  }
  deriving (Show)

notFound :: DerefResult
notFound = DerefResult Nothing False

derefResFromValue :: Tree -> DerefResult
derefResFromValue v = DerefResult (Just v) False

-- | Resolve the reference value.
resolveTCIfRef :: (ReduceMonad s r m) => TrCur -> m DerefResult
resolveTCIfRef tc = case treeNode (tcFocus tc) of
  TNMutable (Ref ref) -> index ref tc
  _ -> return $ derefResFromValue (tcFocus tc)

{- | Index the tree with the segments.

Index has the form of either "a" or "a.b.c" or "{}.b".

If the index operand is a tree node, the tc is used as the environment to evaluate the tree node.

The return value will not be another reference.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
index ::
  (ReduceMonad s r m) => Reference -> TrCur -> m DerefResult
index argRef@Reference{refArg = (RefPath var sels), refOrigAddrs = origAddrsM} tc =
  debugSpanRM (printf "index: var: %s" var) drValue tc $ do
    lbM <- searchLetBindValue var tc
    case lbM of
      Just (IsRef rf)
        -- Let value is an index. For example, let x = ({a:1}).a
        | Just segs <- getIndexSegs rf -> do
            let newRef = (mkIndexRef (segs Seq.>< sels)){refOrigAddrs = origAddrsM}
                -- build the new reference tree.
                refTC = setTCFocusTN (TNMutable $ Ref newRef) tc
            resolveTCIfRef refTC
      Just lb -> do
        -- If the let value is not a reference, but a regular expression.
        -- For example, let x = {}, let x = 1 + 2
        let
          newRef = (mkIndexRef (lb Seq.<| sels)){refOrigAddrs = origAddrsM}
          -- build the new reference tree.
          refTC = setTCFocusTN (TNMutable $ Ref newRef) tc
        resolveTCIfRef refTC

      -- Rest of the cases. For cases such as { let x = a.b, a: b: {}, c: x } where let value is a refernece, it can be handled.
      _ -> do
        refTCM <- refTCFromRef argRef tc
        maybe
          (return notFound)
          ( \(refTC, newRefValPath) -> do
              rTCM <- getDstTC newRefValPath origAddrsM refTC
              return $
                maybe
                  notFound
                  ( \tarTC ->
                      DerefResult
                        (Just $ tcFocus tarTC)
                        (isPathIterBinding (tcCanAddr tarTC))
                  )
                  rTCM
          )
          refTCM

-- in-place expression, like ({}).a, or regular functions. Notice the selector must exist.
index Reference{refArg = arg@(RefIndex _)} tc = debugSpanRM "index" drValue tc $ do
  operandTC <- goDownTCSegMust (MutArgTASeg 0) tc
  reducedOperandM <- reduceToNonMut operandTC

  idxValPathM <- resolveRefValPath arg tc
  let
    tarTCM = do
      idxValPath <- idxValPathM
      reducedOperand <- reducedOperandM
      -- Use the tc as the environment for the reduced operand.
      let reducedTC = reducedOperand `setTCFocus` tc
      case treeNode reducedOperand of
        -- If the operand evaluates to a bottom, we should return the bottom.
        TNBottom _ -> return reducedTC
        _ -> goDownTCAddr (valPathToAddr idxValPath) reducedTC

  maybe (return notFound) resolveTCIfRef tarTCM

-- | Resolve the reference value path using the tree cursor and replace the focus with the resolved value.
refTCFromRef :: (ReduceMonad s r m) => Reference -> TrCur -> m (Maybe (TrCur, ValPath))
refTCFromRef Reference{refArg = arg@(RefPath var _), refOrigAddrs = origAddrsM} tc = do
  refRestPathM <- resolveRefValPath arg tc

  maybe
    (return Nothing)
    ( \refRestPath@(ValPath reducedSels) -> do
        newRef <- mkRefFromValPath mkAtomTree var refRestPath
        let
          newRefValPath = ValPath $ StringSel (TE.encodeUtf8 var) : reducedSels
          -- build the new reference tree.
          refTC = setTCFocusTN (TNMutable $ Ref newRef{refOrigAddrs = origAddrsM}) tc
        return $ Just (refTC, newRefValPath)
    )
    refRestPathM
refTCFromRef _ _ = throwErrSt "refTCFromRef: invalid reference"

{- | Resolve the reference value path.

The tree cursor must be the reference.
-}
resolveRefValPath :: (ReduceMonad s r m) => RefArg -> TrCur -> m (Maybe ValPath)
resolveRefValPath arg tc = do
  l <- case arg of
    (RefPath _ sels) -> return $ zip [0 ..] (toList sels)
    (RefIndex (_ Seq.:<| rest)) -> return $ zip [1 ..] (toList rest)
    _ -> throwErrSt "invalid index"
  m <-
    mapM
      ( \(i, _) -> do
          argTC <- goDownTCSegMust (MutArgTASeg i) tc
          reduceToNonMut argTC
      )
      l
  return $ treesToValPath . Data.Maybe.catMaybes $ m

{- | Get the value pointed by the value path and the original addresses.

The env is to provide the context for the dereferencing the reference.
-}
getDstTC :: (ReduceMonad s r m) => ValPath -> Maybe TreeAddr -> TrCur -> m (Maybe TrCur)
getDstTC valPath origAddrsM _env = do
  -- Make deref see the latest tree, even with unreduced nodes.
  env <- syncTC _env
  debugSpanRM "getDstTC" (fmap tcFocus) env $ do
    let
      selfAddr = tcCanAddr env
      trail = Set.fromList [selfAddr]

    watchRefRM valPath origAddrsM env
    getDstTCInner False valPath origAddrsM trail env

{- | Monitor the absoluate address of the reference searched from the original environment by adding a notifier pair
from the current environment address to the searched address.

If the reference is not found, the function does nothing.

Duplicate cases are handled by the addCtxNotifPair.
-}
watchRefRM ::
  (ReduceMonad s r m) =>
  ValPath ->
  Maybe TreeAddr ->
  TrCur ->
  m ()
watchRefRM ref origAddrsM refEnv = do
  srcAddrM <- do
    identAddrM <- getRefIdentAddr ref origAddrsM refEnv
    return $ do
      x <- identAddrM
      getReferableAddr x
  let recvAddr = tcCanAddr refEnv

  maybe
    (debugInstantRM "watchRefRM" (printf "ref %s is not found" (show ref)) refEnv)
    ( \srcAddr -> do
        ctx <- getRMContext
        putRMContext $ Common.addCtxNotifPair ctx (srcAddr, recvAddr)
        debugInstantRM "watchRefRM" (printf "(%s -> %s)" (show srcAddr) (show recvAddr)) refEnv
    )
    srcAddrM

{- | Get the tree cursor pointed by the reference.

If the reference value is another reference, it will follow the reference.
-}
getDstTCInner ::
  (ReduceMonad s r m) =>
  Bool ->
  ValPath ->
  Maybe TreeAddr ->
  Set.Set TreeAddr ->
  TrCur ->
  m (Maybe TrCur)
getDstTCInner isRefCyclic ref origAddrsM trail refEnv = do
  rE <- getDstRawOrErr ref origAddrsM trail refEnv
  case rE of
    Left err -> return $ Just $ err `setTCFocus` refEnv
    Right Nothing -> return Nothing
    Right (Just tarTC) -> do
      newVal <- copyValFromTarTC isRefCyclic refEnv trail tarTC
      debugInstantRM
        "getDstTCInner"
        (printf "ref: %s, dstVal: %s, newVal: %s" (show ref) (show $ tcFocus tarTC) (show newVal))
        refEnv
      tryFollow trail (newVal `setTCFocus` tarTC) refEnv

{- | Try to follow the reference.

If the reference is not concrete, return Nothing.
-}
tryFollow ::
  (ReduceMonad s r m) =>
  Set.Set TreeAddr ->
  TrCur ->
  TrCur ->
  m (Maybe TrCur)
tryFollow trail tarTC refEnv =
  case treeNode (tcFocus tarTC) of
    TNMutable (Ref ref)
      | refHasRefPath ref -> debugSpanArgsRM "tryFollow" (printf "ref: %s" (show ref)) (fmap tcFocus) refEnv $ do
          -- If ref has unresolved path, we should resolve it with the target tree.
          refTCM <- refTCFromRef ref tarTC
          maybe
            (return Nothing)
            ( \(_, newRefValPath) -> do
                let addr = tcCanAddr refEnv
                getDstTCInner
                  (treeIsCyclic $ tcFocus tarTC)
                  newRefValPath
                  (refOrigAddrs ref)
                  (Set.insert addr trail)
                  refEnv
            )
            refTCM
    _ -> return (Just tarTC)

{- | The result of getting the destination value.

The result is either an error, such as a bottom or a structural cycle, or a valid value.
-}
type DstTC = Either Tree (Maybe TrCur)

{- | Get the processed tree cursor pointed by the reference.

If the reference addr is self or visited, then return the tuple of the absolute addr of the start of the cycle and
the cycle tail relative addr.
-}
getDstRawOrErr ::
  (ReduceMonad s r m) =>
  ValPath ->
  -- | The original addresses of the reference.
  Maybe TreeAddr ->
  -- | keeps track of the followed *referable* addresses.
  Set.Set TreeAddr ->
  -- | The cursor should be the reference.
  TrCur ->
  m DstTC
getDstRawOrErr valPath origAddrsM trail refEnv = do
  let
    -- srcAddr is the starting address of searching for the reference.
    f = locateRef valPath trail

  maybe
    (f refEnv)
    -- If the ref is an outer reference, we should first go to the original value address.
    ( \origValAddr -> inAbsAddrTCMust origValAddr refEnv $ \origValTC ->
        -- If the ref is an outer reference inside the referenced value, we should check if the ref leads to
        -- infinite structure (structural cycle).
        -- For example, { x: a, y: 1, a: {b: y} }, where /a is the address of the subt value.
        -- The "y" in the struct {b: y} is an outer reference.
        -- We should first go to the original value address, which is /a/b.
        f origValTC
    )
    origAddrsM

-- | Locate the reference.
locateRef ::
  (ReduceMonad s r m) =>
  ValPath ->
  Set.Set TreeAddr ->
  TrCur ->
  m DstTC
locateRef valPath trail refEnv = do
  rE <- goTCLAAddr valPath refEnv
  case rE of
    Left err -> return $ Left err
    Right Nothing -> do
      -- If the target is not found, we still need to check if the reference leads to a sub field reference cycle.
      identAddrM <- getRefIdentAddr valPath Nothing refEnv
      cycleDetection <-
        maybe
          (return NoCycleDetected)
          ( \identAddr -> do
              -- The ref is non-empty, so the rest must be a valid addr.
              let rest = fromJust $ tailValPath valPath
                  potentialTarAddr = appendTreeAddr identAddr (valPathToAddr rest)
              detectCycle valPath (tcCanAddr refEnv) Set.empty potentialTarAddr
          )
          identAddrM
      case cycleDetection of
        -- If the reference is a reference cycle referencing the sub field, return the cycle.
        RCDetected tarAddr -> return $ Right $ Just $ setTCFocusTN (TNRefCycle tarAddr) refEnv
        SCDetected -> throwErrSt "should not detect structural cycle here"
        _ -> return $ Right Nothing
    Right (Just tarTC) -> do
      cycleDetection <- detectCycle valPath (tcCanAddr refEnv) trail (tcCanAddr tarTC)
      case cycleDetection of
        RCDetected rfbTarAddr -> return . Right . Just $ setTCFocusTN (TNRefCycle rfbTarAddr) tarTC
        SCDetected ->
          return . Right . Just $
            ((tcFocus tarTC){treeIsCyclic = True}) `setTCFocus` tarTC
        _ -> return . Right $ Just tarTC

data CycleDetection = RCDetected TreeAddr | SCDetected | NoCycleDetected deriving (Show)

{- | Detect if the reference leads to a cycle.

If it does, modify the cursor to be the related cycle node.
-}
detectCycle ::
  (ReduceMonad s r m) =>
  ValPath ->
  TreeAddr ->
  Set.Set TreeAddr ->
  TreeAddr ->
  m CycleDetection
detectCycle valPath srcAddr trail tarAddr = do
  let rfbTarAddr = trimToReferable tarAddr
  debugInstantOpRM
    "detectCycle"
    ( printf
        "valPath: %s, trail: %s, tarAddr: %s, rfbTarAddr: %s, srcAddr: %s"
        (show valPath)
        (show $ Set.toList trail)
        (show tarAddr)
        (show rfbTarAddr)
        (show srcAddr)
    )
    srcAddr
  if
    -- This handles the case when following the chain of references leads to a cycle.
    -- For example, { a: b, b: a, d: a } and we are at d.
    -- The values of d would be: 1. a -> b, 2. b -> a, 3. a (seen) -> RC.
    -- The returned RC would be a self-reference cycle, which has empty addr because the cycle is formed by all
    -- references.
    -- dstAddr is already in the referable form.
    | Set.member tarAddr trail -> do
        debugInstantOpRM
          "detectCycle"
          ( printf
              "horizontal reference cycle detected: %s, dst: %s, trail: %s"
              (show valPath)
              (show tarAddr)
              (show $ Set.toList trail)
          )
          srcAddr
        return (RCDetected tarAddr)
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
    | tarAddr `isPrefix` srcAddr
    , let diff = trimPrefixTreeAddr tarAddr srcAddr
          rfbDiff = trimToReferable diff
    , -- The diff should not have any meaningful segments.
      isTreeAddrEmpty rfbDiff
    , -- The last segment of the tar address should be a struct string segment.
      Just (StructTASeg (StringTASeg _)) <- lastSeg rfbTarAddr -> do
        debugInstantOpRM
          "detectCycle"
          (printf "vertical reference cycle detected: %s == %s." (show tarAddr) (show srcAddr))
          srcAddr
        return (RCDetected rfbTarAddr)

    -- This handles the case when the reference in a sub structure refers to an ancestor.
    -- For example,
    -- x: y: x
    -- x: [{y: x}], where x is at /x, y is at /x/0/y.
    -- or:
    -- x: [x], where x is at /x, y is at /x/0.
    --
    -- According to spec,
    -- If a node "a" references an ancestor node, we call it and any of its field values a.f cyclic. So if "a" is
    -- cyclic, all of its descendants are also regarded as cyclic.
    | tarAddr `isPrefix` srcAddr
    , let diff = trimPrefixTreeAddr tarAddr srcAddr
          rfbDiff = trimToReferable diff
    , -- The diff should have some meaningful segments.
      not (isTreeAddrEmpty rfbDiff) -> do
        debugInstantOpRM
          "detectCycle"
          ( printf
              "ancestor reference cycle detected: %s == %s."
              (show valPath)
              (show tarAddr)
          )
          srcAddr
        return SCDetected
    -- This handles the case when the reference in a sub structure refers to a child.
    -- The target is a sub field of the current field. This is a child reference cycle.
    -- The diff should have some meaningful segments.
    -- For example, x: x.c <> some_op.
    | let opReducedSrcAddr = trimToSingleValueTA srcAddr
    , opReducedSrcAddr `isPrefix` rfbTarAddr
    , let diff = trimPrefixTreeAddr opReducedSrcAddr rfbTarAddr
          rfbDiff = diff
    , not (isTreeAddrEmpty rfbDiff) ->
        do
          debugInstantOpRM
            "detectCycle"
            ( printf
                "child reference cycle detected: src: %s, tar: %s, diff: %s"
                (show srcAddr)
                (show tarAddr)
                (show diff)
            )
            srcAddr
          return (RCDetected rfbTarAddr)
    | otherwise -> return NoCycleDetected

{- | Copy the value of the reference.

From the spec:
The value of a reference is a copy of the expression associated with the field that it is bound to, with
any references within that expression bound to the respective copies of the fields they were originally
bound to.
-}
copyRefVal :: (ReduceMonad s r m) => Tree -> m Tree
copyRefVal tar = do
  case treeNode tar of
    TNAtom _ -> return tar
    TNBottom _ -> return tar
    TNRefCycle _ -> return tar
    TNAtomCnstr c -> return (mkAtomTree $ cnsAtom c)
    _ -> do
      e <- maybe (buildASTExpr False tar) return (treeExpr tar)
      evalExprRM e

{- | Copy the value from the target cursor.

The tree cursor is the target cursor without the copied raw value.
-}
copyValFromTarTC ::
  (ReduceMonad s r m) => Bool -> TrCur -> Set.Set TreeAddr -> TrCur -> m Tree
copyValFromTarTC isRefCyclic srcTC trail tarTC = do
  raw <- copyRefVal (tcFocus tarTC)
  let dstAddr = tcCanAddr tarTC
  -- evaluate the original expression.
  marked <- markOuterIdents (tcCanAddr srcTC) (raw `setTCFocus` tarTC)
  let visited = Set.insert dstAddr trail
  closeMarked <- checkRefDef marked visited

  -- If the target is ancestor or the source reference is a cyclic reference, we should mark the value as cyclic.
  -- For example, x: y: x.
  -- Or, {f: h: g, g: f} -> {f: h: g, g: h: g}, the nested g would find the ancestor g's value "f" because of
  -- expression copying. Then it becomes {f: h: g, g: h: f(Cyclic)}. So here, we should mark f's value as cyclic.
  if treeIsCyclic (tcFocus tarTC) || isRefCyclic
    then markCyclic closeMarked
    else return closeMarked
 where
  checkRefDef val visited = do
    -- Check if the referenced value has recurClose.
    let
      recurClose = treeRecurClosed (tcFocus tarTC)
      shouldClose = any addrHasDef visited
    if shouldClose || recurClose
      then markRecurClosed val
      else return val

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
  (ReduceMonad s r m) =>
  -- | The current tree cursor.
  TreeAddr ->
  TrCur ->
  m Tree
markOuterIdents srcAddr ptc = do
  let blockAddr = tcCanAddr ptc
  utc <- traverseTCSimple subNodes (mark blockAddr) ptc
  return $ tcFocus utc
 where
  -- Mark the outer references with the original value address.
  mark :: (ReduceMonad s r m) => TreeAddr -> TrCur -> m Tree
  mark blockAddr tc = do
    let focus = tcFocus tc
    rM <- case focus of
      IsRef rf -> return $ do
        newValPath <- valPathFromRef rtrAtom rf
        return (newValPath, \as -> setTN focus $ TNMutable . Ref $ rf{refOrigAddrs = Just as})
      _ -> return Nothing
    maybe
      (return focus)
      ( \(valPath, f) -> do
          isOuter <- isOuterScope valPath srcAddr blockAddr tc
          return $
            if isOuter
              then f (tcCanAddr tc)
              else focus
      )
      rM

-- | Check if the reference is an outer reference.
isOuterScope ::
  (ReduceMonad s r m) =>
  ValPath ->
  TreeAddr ->
  TreeAddr ->
  TrCur ->
  m Bool
isOuterScope valPath srcAddr blockAddr tc = do
  tarIdentAddrM <- searchIdent valPath tc
  isOuter <-
    maybe
      (return False)
      ( \tarIdentAddr -> do
          let
            tarIdentAccessible = isPrefix tarIdentAddr srcAddr
            tarIdentInBlock = isPrefix blockAddr tarIdentAddr && blockAddr /= tarIdentAddr
          return $ not (tarIdentAccessible || tarIdentInBlock)
      )
      tarIdentAddrM
  debugInstantRM
    "isOuterScope"
    ( printf
        "valPath: %s, srcAddr: %s, blockAddr: %s, tarIdentAddrM: %s, isOuterScope: %s"
        (show valPath)
        (show srcAddr)
        (show blockAddr)
        (show tarIdentAddrM)
        (show isOuter)
    )
    tc
  return isOuter
 where
  -- Search the first identifier of the reference and convert it to absolute tree addr if it exists.
  searchIdent :: (ReduceMonad s r m) => ValPath -> TrCur -> m (Maybe TreeAddr)
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
getRefIdentAddr ::
  (ReduceMonad s r m) =>
  ValPath ->
  Maybe TreeAddr ->
  TrCur ->
  m (Maybe TreeAddr)
getRefIdentAddr valPath origAddrsM tc = do
  let fstSel = fromJust $ headSel valPath
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

-- | Locate the node in the lowest ancestor tree by given reference path. The path must start with a locatable ident.
goTCLAAddr ::
  (ReduceMonad s r m) => ValPath -> TrCur -> m DstTC
goTCLAAddr valPath tc = do
  when (isValPathEmpty valPath) $ throwErrSt "empty valPath"
  let fstSel = fromJust $ headSel valPath
  ident <- selToIdent fstSel
  searchTCIdent ident tc >>= \case
    Nothing -> do
      errMsg <- notFoundMsg ident (treeExpr (tcFocus tc) >>= AST.wpPos)
      return . Left $
        mkBottomTree errMsg
    Just (identTC, _) -> do
      -- The ref is non-empty, so the rest must be a valid addr.
      let rest = fromJust $ tailValPath valPath
          r = goDownTCAddr (valPathToAddr rest) identTC
      return $ Right r

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrRM :: (ReduceTCMonad s r m) => TreeAddr -> m a -> m (Maybe a)
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
  whenM :: (ReduceTCMonad s r m) => m Bool -> m a -> m (Maybe a)
  whenM cond g = do
    b <- cond
    if b then Just <$> g else return Nothing

-- | Go to the absolute addr in the tree.
goRMAbsAddr :: (ReduceTCMonad s r m) => TreeAddr -> m Bool
goRMAbsAddr dst = do
  when (headSeg dst /= Just RootTASeg) $
    throwErrSt (printf "the addr %s should start with the root segment" (show dst))
  propUpTMUntilSeg RootTASeg
  let dstNoRoot = fromJust $ tailTreeAddr dst
  descendTM dstNoRoot

goRMAbsAddrMust :: (ReduceTCMonad s r m) => TreeAddr -> m ()
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
        StructTASeg (StringTASeg s) -> fromMaybe False $ do
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
searchTCIdentInPar :: (ReduceMonad s r m) => T.Text -> TrCur -> m (Maybe (TreeAddr, Bool))
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

Return a pair. The first is address of the identifier, the second is the identifier is a let binding.

The child value will not be propagated to the parent block. Propagation is not needed because all static fields should
already exist.

The tree cursor must at least have the root segment.
-}
searchTCIdent :: (ReduceMonad s r m) => T.Text -> TrCur -> m (Maybe (TrCur, Bool))
searchTCIdent name tc = do
  subM <- findIdent name tc
  maybe
    (goUp tc)
    ( \(identTC, isLB) -> do
        when isLB $ do
          -- Mark the ident as referred if it is a let binding.
          markRMLetReferred (tcCanAddr identTC)
          unrefLets <- getRMUnreferredLets
          debugInstantRM
            "searchLetBindValue"
            (printf "ident: %s, unrefLets: %s" (show $ tcCanAddr identTC) (show unrefLets))
            tc
        return $ Just (identTC, isLB)
    )
    subM
 where
  mkSeg isLB = let nt = TE.encodeUtf8 name in StructTASeg $ if isLB then LetTASeg nt else StringTASeg nt

  goUp :: (ReduceMonad s r m) => TrCur -> m (Maybe (TrCur, Bool))
  goUp (TrCur _ [(RootTASeg, _)]) = return Nothing -- stop at the root.
  goUp utc = do
    ptc <- maybe (throwErrSt "already on the top") return $ parentTC utc
    searchTCIdent name ptc

  -- TODO: findIdent for default disjunct?
  findIdent :: (Common.Env r s m) => T.Text -> TrCur -> m (Maybe (TrCur, Bool))
  findIdent ident blockTC = do
    case treeNode (tcFocus blockTC) of
      TNBlock blk@(Block{blkStruct = struct})
        -- If the block reduces to non-struct, then the fields are not searchable in the block. The fields have
        -- behaved like mutable argument.
        -- For example, { x: {a:1, c:d, e}, e: {a: int} | {b: int}, d:1 }
        -- - merge -> {x: {a:1, c:d} | {a:1, c:d, b:int}, d:1, e: {..}}
        -- Then when we reduce the merged value, at /x/dj0/c, it finds d in the top /.
        | isNothing (blkNonStructValue blk) -> do
            let
              inBlock = ident `Set.member` stcBlockIdents struct
              m =
                catMaybes
                  [ do
                      sf <- lookupStructIdentField ident struct
                      return (mkSubTC (mkSeg False) (ssfValue sf) blockTC, False)
                  , do
                      lb <- lookupStructLet ident struct
                      return (mkSubTC (mkSeg True) (lbValue lb) blockTC, True)
                  ]
            if inBlock
              then case m of
                [] -> return Nothing
                [x] -> return $ Just x
                (fstTC, _) : _ ->
                  return $
                    Just
                      ( mkBottomTree (printf "multiple fields found for %s" ident) `setTCFocus` fstTC
                      , False
                      )
              else return Nothing
      TNMutable (Compreh c) -> do
        let binds = cphIterBindings c
        debugInstantRM
          "searchTCIdent"
          (printf "binds: %s" (show binds))
          blockTC
        foldM
          ( \acc (i, bind) ->
              if isJust acc
                then return acc
                else
                  let bindName = cphBindName bind
                   in if bindName == ident
                        then do
                          debugInstantRM
                            "searchTCIdent"
                            (printf "found in comprehension binding: %s" (show bindName))
                            blockTC
                          -- Since the bindName is an identifier and watchRefRM only watches referable identifiers, we
                          -- do not need to worry that the bindValTC will be accessed.
                          -- The ComprehIterBindingTASeg is used to make sure the address passes the cycle detection.
                          let bindValTC =
                                mkSubTC
                                  (ComprehTASeg (ComprehIterBindingTASeg i))
                                  (cphBindValue bind)
                                  blockTC
                          return $ Just (bindValTC, False)
                        else return acc
          )
          Nothing
          (reverse (zip [0 ..] binds))
      _ -> return Nothing

searchLetBindValue :: (ReduceMonad s r m) => T.Text -> TrCur -> m (Maybe Tree)
searchLetBindValue ident tc = do
  m <- searchTCIdent ident tc
  case m of
    Just (identTC, True) -> return $ Just (tcFocus identTC)
    _ -> return Nothing

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

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrTCMust ::
  (Common.Env r s m) =>
  TreeAddr ->
  TrCur ->
  (TrCur -> m a) ->
  m a
inAbsAddrTCMust p tc f = do
  tarM <- goTCAbsAddr p tc
  maybe (throwErrSt $ printf "%s is not found" (show p)) f tarM
