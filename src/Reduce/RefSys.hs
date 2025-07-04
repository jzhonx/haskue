{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RefSys where

import qualified AST
import qualified Common
import Control.Monad (unless, when)
import Cursor
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe)
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
  , drIsInBinding :: Bool
  -- ^ Whether the dereferenced value is part of a let binding.
  }
  deriving (Show)

notFound :: DerefResult
notFound = DerefResult Nothing False

derefResFromValue :: Tree -> DerefResult
derefResFromValue v = DerefResult (Just v) False

-- | Resolve the reference value.
resolveTCIfRef :: (ReduceMonad s r m) => TrCur -> m DerefResult
resolveTCIfRef tc = case tc of
  TCFocus (IsRef _ ref) -> index ref tc
  _ -> return $ derefResFromValue (tcFocus tc)

{- | Index the tree with the segments.

Index has the form of either "a" or "a.b.c" or "{}.b".

If the index operand is a tree node, the tc is used as the environment to evaluate the tree node.

The return value will not be another reference.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
index :: (ReduceMonad s r m) => Reference -> TrCur -> m DerefResult
index argRef@Reference{refArg = (RefPath var sels), refOrigAddrs = origAddrsM} tc =
  debugSpanRM (printf "index: var: %s" var) drValue tc $ do
    lbM <- searchTCIdent var tc
    case lbM of
      Just (TCFocus (IsRef mut rf), True)
        -- Let value is an index. For example, let x = ({a:1}).a
        | Just segs <- getIndexSegs rf -> do
            let newRef = (mkIndexRef (segs Seq.>< sels)){refOrigAddrs = origAddrsM}
                -- build the new reference tree.
                refTC = setTCFocusTN (TNMutable $ setMutOp (Ref newRef) mut) tc
            resolveTCIfRef refTC
      Just (TCFocus lb, True) -> do
        -- If the let value is not a reference, but a regular expression.
        -- For example, let x = {}, let x = 1 + 2
        let
          newRef = (mkIndexRef (lb Seq.<| sels)){refOrigAddrs = origAddrsM}
          -- build the new reference tree.
          refTC = setTCFocusTN (TNMutable $ withEmptyMutFrame (Ref newRef)) tc
        resolveTCIfRef refTC

      -- Rest of the cases. For cases such as { let x = a.b, a: b: {}, c: x } where let value is a refernece, it can be
      -- handled.
      _ -> do
        refTCM <- refTCFromRef argRef tc
        maybe
          (return notFound)
          ( \(refTC, newRefValPath) -> do
              rTCM <- getDstTC newRefValPath origAddrsM refTC
              return $
                maybe
                  notFound
                  (\tarTC -> DerefResult (Just $ tcFocus tarTC) False)
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
          refTC = setTCFocusTN (TNMutable $ withEmptyMutFrame (Ref newRef{refOrigAddrs = origAddrsM})) tc
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
watchRefRM :: (ReduceMonad s r m) => ValPath -> Maybe TreeAddr -> TrCur -> m ()
watchRefRM ref origAddrsM refEnv = do
  tarAddrM <- do
    identAddrM <- getRefIdentAddr ref origAddrsM refEnv
    return $ do
      x <- identAddrM
      getReferableAddr x
  let recvAddr = tcCanAddr refEnv

  maybe
    (debugInstantRM "watchRefRM" (printf "ref %s is not found" (show ref)) refEnv)
    ( \tarAddr -> do
        ctx <- getRMContext
        putRMContext $ Common.addCtxNotifPair ctx (tarAddr, recvAddr)
        debugInstantRM "watchRefRM" (printf "(%s -> %s)" (show tarAddr) (show recvAddr)) refEnv
    )
    tarAddrM

{- | Get the tree cursor pointed by the reference.

If the reference value is another reference, it will follow the reference.
-}
getDstTCInner ::
  (ReduceMonad s r m) => Bool -> ValPath -> Maybe TreeAddr -> Set.Set TreeAddr -> TrCur -> m (Maybe TrCur)
getDstTCInner isRefCyclic ref origAddrsM trail refEnv = do
  rE <- getTarRaw ref origAddrsM trail refEnv
  case rE of
    Left err -> do
      debugInstantRM
        "getDstTCInner"
        (printf "ref: %s, err: %s, tc: %s" (show ref) (show err) (showCursor refEnv))
        refEnv
      return $ Just $ err `setTCFocus` refEnv
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
tryFollow :: (ReduceMonad s r m) => Set.Set TreeAddr -> TrCur -> TrCur -> m (Maybe TrCur)
tryFollow trail tarTC refEnv =
  case tarTC of
    TCFocus (IsRef _ ref)
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

The result is either an error, or the target tree cursor.
-}
type DstTC = Either Tree (Maybe TrCur)

{- | Get the processed tree cursor pointed by the reference.

If the reference addr is self or visited, then return the tuple of the absolute addr of the start of the cycle and
the cycle tail relative addr.

* @valPath@ The reference value path.
* @origAddrsM@ The original addresses of the reference.
* @trail@ The trail of the *referable* addresses followed.
* @refEnv@ The environment to resolve the reference.
-}
getTarRaw :: (ReduceMonad s r m) => ValPath -> Maybe TreeAddr -> Set.Set TreeAddr -> TrCur -> m DstTC
getTarRaw valPath Nothing trail refEnv = do
  lr <- locateRef valPath refEnv
  case lr of
    LRIdentNotFound err -> return $ Left err
    _ -> Right . fst <$> detectCycle valPath trail lr refEnv
-- The ref is an outer reference.
-- We need to go to the original value address to fetch the value because searching up in the tree for the identifier of
-- the reference from the original environment is the correct way to find the bound value of the identifier, according
-- to spec's definition on the bound value of a reference:
-- > The value of a reference is a copy of the expression associated with the field that it is bound to, with any
-- > references within that expression bound to the respective copies of the fields they were originally bound to.
--
-- We need to check cycles in two environments. First starting from the original value address, and then from the
-- current environment.
-- Consider the following example:
--       CA (common ancestor)
--       / \
--      .   .
--   a /     \ b
--   node      node
--    | x      | x
--    r'       r
--
-- r' is a copy of r.
-- If r's value is a (resolved to /CA/../a), then in the original environment (/CA/../b/x), there is no cycles. But
-- after we put the r's value, in the current environment (/CA/../a/x), there is a cycle. Depending on what the node and
-- x are, the cycle could be a structural cycle or a reference cycle.
-- Consider some concrete examples:
-- 1.
-- {a: b + 100, b: a - 100}
-- We are at /a/fa0. The "b" is resolved to a - 100. We mark the "a" with the origAddrs. Then at /a/fa0/fa0, we evaluate
-- the "a", which is not a cycle. However, once we put the value to the /a/fa0/fa0, it becomes a reference cycle.
-- 2.
-- {a: b, b: b}
-- We are at /a. The "b" is resolved to b. We mark the "b" with the origAddrs. Then at /a, we evaluate the "b". We need
-- to go to the original value address of "b", which is /b. The "b" is resolved to a reference cycle. So the result is a
-- reference cycle.
-- 3.
-- {a: p.b, p: b: p}
-- We are at /a. The "p.b" is resolved to p. We mark the "p" with the origAddrs. Then at /a, we evaluate the "p". We
-- need to go to the original value address of "p", which is /p/b. The "p" is resolved to a structural cycle. So the
-- result is a structural cycle.
-- 4.
-- {p: a: b, b: p}
-- We are at /p/a. The "b" is resolved to p. We mark the "p" with the origAddrs. Then at /p/a, we evaluate the "p". We
-- need to go to the original value address of "p", which is /b. The "p" is resolved to {a: b} with address equal to /p,
-- which is ok. After putting the value to /p/a, we find that the target address /p is the ancestor of the current
-- address /p/a, so it is a structural cycle.
getTarRaw valPath (Just origValAddr) trail refEnv = do
  (lr, rM, cd) <- inAbsAddrTCMust origValAddr refEnv $ \origValTC -> do
    lr <- locateRef valPath origValTC
    case lr of
      LRIdentNotFound _ -> return (lr, Nothing, NoCycleDetected)
      _ -> do
        (rM, cd) <- detectCycle valPath trail lr origValTC
        return (lr, rM, cd)
  case (lr, cd) of
    (LRIdentNotFound err, _) -> return $ Left err
    (_, NoCycleDetected) -> Right . fst <$> detectCycle valPath trail lr refEnv
    _ -> return $ Right rM

data CycleDetection = RCDetected TreeAddr | SCDetected | NoCycleDetected deriving (Show)

{- | Detect if the reference leads to a cycle.

Returns the target tree cursor and the cycle detection result.
-}
detectCycle ::
  (ReduceMonad s r m) => ValPath -> Set.Set TreeAddr -> LocateRefResult -> TrCur -> m (Maybe TrCur, CycleDetection)
detectCycle valPath _ (LRPartialFound lastMatchedTC potentialTarAddr) refEnv = do
  -- If the target is not found, we still need to check if the reference leads to a sub field reference cycle.
  cd <- detectCycleForNotFound valPath (tcCanAddr refEnv) lastMatchedTC potentialTarAddr
  case cd of
    -- If the reference is a reference cycle referencing the sub field, return the cycle.
    RCDetected tarAddr -> return (Just $ setTCFocusTN (TNRefCycle tarAddr) refEnv, cd)
    _ -> return (Nothing, cd)
detectCycle valPath trail (LRRefFound tarTC) refEnv = do
  cd <- detectCycleForFound valPath (tcCanAddr refEnv) trail (tcCanAddr tarTC)
  case cd of
    RCDetected rfbTarAddr -> return (Just $ setTCFocusTN (TNRefCycle rfbTarAddr) tarTC, cd)
    SCDetected ->
      return
        ( Just $
            ((tcFocus tarTC){treeIsCyclic = True}) `setTCFocus` tarTC
        , cd
        )
    _ -> return (Just tarTC, cd)
detectCycle _ _ (LRIdentNotFound _) _ = return (Nothing, NoCycleDetected)

{- | Detect if the referenced value forms a cycle.

If the referenced node is found, there are only two cases, structural cycle and reference cycle, which are all somewhat
ancestors of the reference. If the referenced node is uncle, sibling, or nephew, it is not a cycle.

* @valPath@ is the value path of the reference, which is only used for printing debug messages.
-}
detectCycleForFound ::
  (ReduceMonad s r m) => ValPath -> TreeAddr -> Set.Set TreeAddr -> TreeAddr -> m CycleDetection
detectCycleForFound valPath startAddr trail tarAddr = do
  let rfbTarAddr = trimToReferable tarAddr
  debugInstantOpRM
    "detectCycleForFound"
    ( printf
        "valPath: %s, trail: %s, tarAddr: %s, rfbTarAddr: %s, startAddr: %s"
        (show valPath)
        (show $ Set.toList trail)
        (show tarAddr)
        (show rfbTarAddr)
        (show startAddr)
    )
    startAddr
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
          startAddr
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
    | tarAddr `isPrefix` startAddr
    , let diff = trimPrefixTreeAddr tarAddr startAddr
          rfbDiff = trimToReferable diff
    , -- The diff should not have any meaningful segments.
      isTreeAddrEmpty rfbDiff
    , -- The last segment of the tar address should be a struct string segment.
      Just (BlockTASeg (StringTASeg _)) <- lastSeg rfbTarAddr -> do
        debugInstantOpRM
          "detectCycle"
          (printf "vertical reference cycle detected: %s == %s." (show tarAddr) (show startAddr))
          startAddr
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
    | tarAddr `isPrefix` startAddr
    , let diff = trimPrefixTreeAddr tarAddr startAddr
          rfbDiff = trimToReferable diff
    , -- The diff should have some meaningful (referable) segments.
      not (isTreeAddrEmpty rfbDiff) -> do
        debugInstantOpRM
          "detectCycle"
          ( printf
              "ancestor reference cycle detected: %s == %s."
              (show valPath)
              (show tarAddr)
          )
          startAddr
        return SCDetected
    | otherwise -> return NoCycleDetected

{- | Detect if the would-be referenced value forms a cycle.

It assumes that there is some selectors are not matched, so the reference is not found.
-}
detectCycleForNotFound :: (ReduceMonad s r m) => ValPath -> TreeAddr -> TrCur -> TreeAddr -> m CycleDetection
detectCycleForNotFound valPath originAddr lastMatchedTC potentialTarAddr = do
  let
    lastMatchedAddr = tcCanAddr lastMatchedTC
    rfbLastMatched = trimToReferable lastMatchedAddr
  debugInstantOpRM
    "detectCycleForNotFound"
    ( printf
        "valPath: %s, lastMatchedAddr: %s, rfbLastMatched: %s, originAddr: %s"
        (show valPath)
        (show lastMatchedAddr)
        (show rfbLastMatched)
        (show originAddr)
    )
    originAddr
  if
    -- This handles the case when the reference as an operand references a field of the to be constructed struct of the
    -- operation.
    -- This is a child reference cycle.
    -- It is a cycle because to generate the struct, we need the field of the struct beforehand.
    -- For example, x: x.c <> some_op. /x/c would be the potentialTarAddr, /x/fa0 would be the originAddr. The last
    -- matched address is /x. The x.c <> some_op would be a struct, but it is not yet constructed.
    --
    -- The last matched address should be the prefix of the origin address. This ensures that the value pointed by the
    -- origin address is part of a operation that is building a struct.
    | lastMatchedAddr `isPrefix` originAddr
    , let diff = trimPrefixTreeAddr lastMatchedAddr originAddr
          rfbDiff = trimToReferable diff
    , -- The diff should not have any meaningful segments.
      isTreeAddrEmpty rfbDiff
    , -- The last segment of the last matched address should be a struct string segment.
      Just (BlockTASeg (StringTASeg _)) <- lastSeg lastMatchedAddr
    , -- The value of the last matched address should not be a built struct.
      -- For example, x: {a: x.c}
      -- The struct has already existed and its existence does not rely on the field of the struct.
      Nothing <- rtrBlock (tcFocus lastMatchedTC) -> do
        do
          debugInstantOpRM
            "detectCycle"
            ( printf
                "child reference cycle detected: origin: %s, lastMatchedAddr: %s, diff: %s"
                (show originAddr)
                (show lastMatchedAddr)
                (show diff)
            )
            originAddr
          return (RCDetected (trimToReferable potentialTarAddr))
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
      e <- maybe (buildASTExpr tar) return (treeExpr tar)
      evalExprRM e

{- | Copy the value from the target cursor.

The tree cursor is the target cursor without the copied raw value.
-}
copyValFromTarTC ::
  (ReduceMonad s r m) => Bool -> TrCur -> Set.Set TreeAddr -> TrCur -> m Tree
copyValFromTarTC isRefCyclic originTC trail tarTC = do
  raw <- copyRefVal (tcFocus tarTC)
  let dstAddr = tcCanAddr tarTC
  -- evaluate the original expression.
  marked <- markOuterIdents (tcCanAddr originTC) (raw `setTCFocus` tarTC)
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

{- | Mark all outer references inside a tree with original value address.

The outer references are the reference nodes in a tree pointing outside of the tree, not including the tree itself.

This is needed because we need to record the original fields that these references bound to.

For example, given the following tree:

y: a.s
a: {
	s: {j1: i2}
	i2: 2
}

The tree to copy is {j1: i2}. We need to mark the i2 because i2 is out of the tree.

Consider the example,

y: a.s
a: {
	s: {j1: i2, i2: 2}
}

The i2 is not marked because it is within the tree.
-}
markOuterIdents :: (ReduceMonad s r m) => TreeAddr -> TrCur -> m Tree
markOuterIdents originAddr treeTC = do
  let tAddr = tcCanAddr treeTC
  utc <- traverseTCSimple subNodes (mark tAddr) treeTC
  return $ tcFocus utc
 where
  -- Mark the outer references with the original value address.
  mark :: (ReduceMonad s r m) => TreeAddr -> TrCur -> m Tree
  mark tAddr tc = do
    let focus = tcFocus tc
    rM <- case focus of
      IsRef mut rf -> return $ do
        newValPath <- valPathFromRef rtrAtom rf
        return (newValPath, \as -> setTN focus $ TNMutable $ setMutOp (Ref $ rf{refOrigAddrs = Just as}) mut)
      _ -> return Nothing
    maybe
      (return focus)
      ( \(valPath, f) -> do
          isOuter <- isOuterScope valPath originAddr tAddr tc
          return $
            if isOuter
              then f (tcCanAddr tc)
              else focus
      )
      rM

-- | Check if the reference is an outer reference.
isOuterScope :: (ReduceMonad s r m) => ValPath -> TreeAddr -> TreeAddr -> TrCur -> m Bool
isOuterScope valPath originAddr tAddr tc = do
  tarIdentAddrM <- searchIdent valPath tc
  isOuter <-
    maybe
      (return False)
      ( \tarIdentAddr -> do
          let tarIdentInTree = isPrefix tAddr tarIdentAddr && tAddr /= tarIdentAddr
          return (not tarIdentInTree)
      )
      tarIdentAddrM
  debugInstantRM
    "isOuterScope"
    ( printf
        "valPath: %s, originAddr: %s, tAddr: %s, tarIdentAddrM: %s, isOuterScope: %s"
        (show valPath)
        (show originAddr)
        (show tAddr)
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
getRefIdentAddr :: (ReduceMonad s r m) => ValPath -> Maybe TreeAddr -> TrCur -> m (Maybe TreeAddr)
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
locateRef :: (ReduceMonad s r m) => ValPath -> TrCur -> m LocateRefResult
locateRef valPath tc = do
  when (isValPathEmpty valPath) $ throwErrSt "empty valPath"
  let fstSel = fromJust $ headSel valPath
  ident <- selToIdent fstSel
  searchTCIdent ident tc >>= \case
    Nothing -> do
      errMsg <- notFoundMsg ident (treeExpr (tcFocus tc) >>= AST.anPos)
      return . LRIdentNotFound $ mkBottomTree errMsg
    Just (identTC, _) -> do
      -- The ref is non-empty, so the rest must be a valid addr.
      let rest = fromJust $ tailValPath valPath
          (matchedTC, unmatchedSels) = go identTC (getRefSels rest)
      return $
        if null unmatchedSels
          then LRRefFound matchedTC
          else LRPartialFound matchedTC (appendTreeAddr (tcCanAddr matchedTC) (valPathToAddr (ValPath unmatchedSels)))
 where
  -- return $
  --   Right
  --     ( matchedTC
  --     , appendTreeAddr (tcCanAddr matchedTC) (valPathToAddr (ValPath unmatchedSels))
  --     , null unmatchedSels
  --     )

  go x [] = (x, [])
  go x sels@(sel : rs) =
    maybe
      (x, sels)
      (`go` rs)
      (goDownTCSeg (selToTASeg sel) x)

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

Return a pair. The first is address of the identifier, the second is whether the identifier is a let binding.

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
            "searchTCIdent"
            (printf "ident: %s, unrefLets: %s" (show $ tcCanAddr identTC) (show unrefLets))
            tc
        return $ Just (identTC, isLB)
    )
    subM
 where
  mkSeg isLB = let nt = TE.encodeUtf8 name in BlockTASeg $ if isLB then LetTASeg nt else StringTASeg nt

  goUp :: (ReduceMonad s r m) => TrCur -> m (Maybe (TrCur, Bool))
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
            debugInstantRM
              "findIdent"
              (printf "ident %s not found in block, tc: %s" (show ident) (showCursor blockTC))
              blockTC
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
        debugInstantRM
          "findIdent"
          (printf "ident %s not found in value, tc: %s" (show ident) (showCursor blockTC))
          blockTC
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

{- | Go to the absolute addr in the tree and execute the action if the addr exists.

If the addr does not exist, return Nothing.
-}
inAbsAddrTCMust :: (Common.Env r s m) => TreeAddr -> TrCur -> (TrCur -> m a) -> m a
inAbsAddrTCMust p tc f = do
  tarM <- goTCAbsAddr p tc
  maybe (throwErrSt $ printf "%s is not found" (show p)) f tarM
