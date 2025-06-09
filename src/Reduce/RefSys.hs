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
import qualified Cursor
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, isNothing)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import TCOps (goDownTCAddr, topTC)
import qualified TCOps
import Text.Printf (printf)
import qualified Value.Tree as VT

data DerefResult = DerefResult
  { drValue :: Maybe VT.Tree
  , drIsComprehBinding :: Bool
  }
  deriving (Show)

notFound :: DerefResult
notFound = DerefResult Nothing False

derefResFromValue :: VT.Tree -> DerefResult
derefResFromValue v = DerefResult (Just v) False

-- | Resolve the reference value.
resolveTCIfRef :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m DerefResult
resolveTCIfRef tc = case VT.treeNode (Cursor.tcFocus tc) of
  VT.TNMutable (VT.Ref ref) -> index ref tc
  _ -> return $ derefResFromValue (Cursor.tcFocus tc)

{- | Index the tree with the segments.

Index has the form of either "a" or "a.b.c" or "{}.b".

If the index operand is a tree node, the tc is used as the environment to evaluate the tree node.

The return value will not be another reference.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
index ::
  (RM.ReduceMonad s r m) => VT.Reference VT.Tree -> TCOps.TrCur -> m DerefResult
index argRef@VT.Reference{VT.refArg = (VT.RefPath var sels), VT.refOrigAddrs = origAddrsM} tc =
  RM.debugSpanRM (printf "index: var: %s" var) drValue tc $ do
    lbM <- searchLetBindValue var tc
    case lbM of
      Just lb
        -- If the let value is not a reference, but a regular expression.
        -- For example, let x = {}, let x = 1 + 2
        | Nothing <- VT.getRefFromTree lb -> do
            let
              newRef = (VT.mkIndexRef (lb : sels)){VT.refOrigAddrs = origAddrsM}
              -- build the new reference tree.
              refTC = TCOps.setTCFocusTN (VT.TNMutable $ VT.Ref newRef) tc
            resolveTCIfRef refTC
        -- Let value is an index. For example, let x = ({a:1}).a
        | Just rf <- VT.getRefFromTree lb
        , Just segs <- VT.getIndexSegs rf -> do
            let newRef = (VT.mkIndexRef (segs ++ sels)){VT.refOrigAddrs = origAddrsM}
                -- build the new reference tree.
                refTC = TCOps.setTCFocusTN (VT.TNMutable $ VT.Ref newRef) tc
            resolveTCIfRef refTC
      -- Rest of the cases. For cases such as { let x = a.b, a: b: {}, c: x } can be handled.
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
                        (Just $ Cursor.tcFocus tarTC)
                        (Path.isPathIterBinding (Cursor.tcCanAddr tarTC))
                  )
                  rTCM
          )
          refTCM

-- in-place expression, like ({}).a, or regular functions. Notice the selector must exist.
index VT.Reference{VT.refArg = arg@(VT.RefIndex _)} tc = RM.debugSpanRM "index" drValue tc $ do
  operandTC <- TCOps.goDownTCSegMust (Path.MutableArgTASeg 0) tc
  reducedOperandM <- Mutate.reduceToNonMut operandTC

  idxValPathM <- resolveRefValPath arg tc
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

  maybe (return notFound) resolveTCIfRef tarTCM

-- | Resolve the reference value path using the tree cursor and replace the focus with the resolved value.
refTCFromRef :: (RM.ReduceMonad s r m) => VT.Reference VT.Tree -> TCOps.TrCur -> m (Maybe (TCOps.TrCur, Path.ValPath))
refTCFromRef VT.Reference{VT.refArg = arg@(VT.RefPath var _), VT.refOrigAddrs = origAddrsM} tc = do
  refRestPathM <- resolveRefValPath arg tc

  maybe
    (return Nothing)
    ( \refRestPath@(Path.ValPath reducedSels) -> do
        newRef <- VT.mkRefFromValPath VT.mkAtomTree var refRestPath
        let
          newRefValPath = Path.ValPath $ Path.StringSel (TE.encodeUtf8 var) : reducedSels
          -- build the new reference tree.
          refTC = TCOps.setTCFocusTN (VT.TNMutable $ VT.Ref newRef{VT.refOrigAddrs = origAddrsM}) tc
        return $ Just (refTC, newRefValPath)
    )
    refRestPathM
refTCFromRef _ _ = throwErrSt "refTCFromRef: invalid reference"

{- | Resolve the reference value path.

The tree cursor must be the reference.
-}
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
          Mutate.reduceToNonMut argTC
      )
      l
  return $ VT.treesToValPath . Data.Maybe.catMaybes $ m

{- | Get the value pointed by the value path and the original addresses.

The env is to provide the context for the dereferencing the reference.
-}
getDstTC :: (RM.ReduceMonad s r m) => Path.ValPath -> Maybe Path.TreeAddr -> TCOps.TrCur -> m (Maybe TCOps.TrCur)
getDstTC valPath origAddrsM _env = do
  -- Make deref see the latest tree, even with unreduced nodes.
  env <- TCOps.syncTC _env
  RM.debugSpanRM "getDstTC" (fmap Cursor.tcFocus) env $ do
    let
      selfAddr = Cursor.tcCanAddr env
      trail = Set.fromList [selfAddr]

    watchRefRM valPath origAddrsM env
    getDstTCInner False valPath origAddrsM trail env

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
watchRefRM ref origAddrsM refEnv = do
  srcAddrM <- do
    identAddrM <- getRefIdentAddr ref origAddrsM refEnv
    return $ do
      x <- identAddrM
      Path.getReferableAddr x
  let recvAddr = Cursor.tcCanAddr refEnv

  maybe
    (RM.debugInstantRM "watchRefRM" (printf "ref %s is not found" (show ref)) refEnv)
    ( \srcAddr -> do
        ctx <- RM.getRMContext
        RM.putRMContext $ Common.addCtxNotifPair ctx (srcAddr, recvAddr)
        RM.debugInstantRM "watchRefRM" (printf "(%s -> %s)" (show srcAddr) (show recvAddr)) refEnv
    )
    srcAddrM

{- | Get the tree cursor pointed by the reference.

If the reference value is another reference, it will follow the reference.
-}
getDstTCInner ::
  (RM.ReduceMonad s r m) =>
  Bool ->
  Path.ValPath ->
  Maybe Path.TreeAddr ->
  Set.Set Path.TreeAddr ->
  TCOps.TrCur ->
  m (Maybe TCOps.TrCur)
getDstTCInner isRefCyclic ref origAddrsM trail refEnv = do
  rE <- getDstRawOrErr ref origAddrsM trail refEnv
  case rE of
    Left err -> return $ Just $ err `Cursor.setTCFocus` refEnv
    Right Nothing -> return Nothing
    Right (Just tarTC) -> do
      newVal <- copyValFromTarTC isRefCyclic refEnv trail tarTC
      RM.debugInstantRM
        "getDstTCInner"
        (printf "ref: %s, dstVal: %s, newVal: %s" (show ref) (show $ Cursor.tcFocus tarTC) (show newVal))
        refEnv
      tryFollow trail (newVal `Cursor.setTCFocus` tarTC) refEnv

{- | Try to follow the reference.

If the reference is not concrete, return Nothing.
-}
tryFollow ::
  (RM.ReduceMonad s r m) =>
  Set.Set Path.TreeAddr ->
  TCOps.TrCur ->
  TCOps.TrCur ->
  m (Maybe TCOps.TrCur)
tryFollow trail tarTC refEnv =
  case VT.treeNode (Cursor.tcFocus tarTC) of
    VT.TNMutable (VT.Ref ref)
      | VT.refHasRefPath ref -> RM.debugSpanArgsRM "tryFollow" (printf "ref: %s" (show ref)) (fmap Cursor.tcFocus) refEnv $ do
          -- If ref has unresolved path, we should resolve it with the target tree.
          refTCM <- refTCFromRef ref tarTC
          maybe
            (return Nothing)
            ( \(_, newRefValPath) -> do
                let addr = Cursor.tcCanAddr refEnv
                getDstTCInner
                  (VT.treeIsCyclic $ Cursor.tcFocus tarTC)
                  newRefValPath
                  (VT.refOrigAddrs ref)
                  (Set.insert addr trail)
                  refEnv
            )
            refTCM
    _ -> return (Just tarTC)

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
  (RM.ReduceMonad s r m) =>
  Path.ValPath ->
  Set.Set Path.TreeAddr ->
  TCOps.TrCur ->
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
              let rest = fromJust $ Path.tailValPath valPath
                  potentialTarAddr = Path.appendTreeAddr identAddr (Path.valPathToAddr rest)
              detectCycle valPath (Cursor.tcCanAddr refEnv) Set.empty potentialTarAddr
          )
          identAddrM
      case cycleDetection of
        -- If the reference is a reference cycle referencing the sub field, return the cycle.
        RCDetected tarAddr -> return $ Right $ Just $ TCOps.setTCFocusTN (VT.TNRefCycle tarAddr) refEnv
        SCDetected -> throwErrSt "should not detect structural cycle here"
        _ -> return $ Right Nothing
    Right (Just tarTC) -> do
      cycleDetection <- detectCycle valPath (Cursor.tcCanAddr refEnv) trail (Cursor.tcCanAddr tarTC)
      case cycleDetection of
        RCDetected rfbTarAddr -> return . Right . Just $ TCOps.setTCFocusTN (VT.TNRefCycle rfbTarAddr) tarTC
        SCDetected ->
          return . Right . Just $
            ((Cursor.tcFocus tarTC){VT.treeIsCyclic = True}) `Cursor.setTCFocus` tarTC
        _ -> return . Right $ Just tarTC

data CycleDetection = RCDetected Path.TreeAddr | SCDetected | NoCycleDetected deriving (Show)

{- | Detect if the reference leads to a cycle.

If it does, modify the cursor to be the related cycle node.
-}
detectCycle ::
  (RM.ReduceMonad s r m) =>
  Path.ValPath ->
  Path.TreeAddr ->
  Set.Set Path.TreeAddr ->
  Path.TreeAddr ->
  m CycleDetection
detectCycle valPath srcAddr trail tarAddr = do
  let rfbTarAddr = Path.trimToReferable tarAddr
  RM.debugInstantOpRM
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
        RM.debugInstantOpRM
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
    | tarAddr `Path.isPrefix` srcAddr
    , let diff = Path.trimPrefixTreeAddr tarAddr srcAddr
          rfbDiff = Path.trimToReferable diff
    , -- The diff should not have any meaningful segments.
      Path.isTreeAddrEmpty rfbDiff
    , -- The last segment of the tar address should be a struct string segment.
      Just (Path.StructTASeg (Path.StringTASeg _)) <- Path.lastSeg rfbTarAddr -> do
        RM.debugInstantOpRM
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
    | tarAddr `Path.isPrefix` srcAddr
    , let diff = Path.trimPrefixTreeAddr tarAddr srcAddr
          rfbDiff = Path.trimToReferable diff
    , -- The diff should have some meaningful segments.
      not (Path.isTreeAddrEmpty rfbDiff) -> do
        RM.debugInstantOpRM
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
    | let opReducedSrcAddr = Path.trimToSingleValueTA srcAddr
    , opReducedSrcAddr `Path.isPrefix` rfbTarAddr
    , let diff = Path.trimPrefixTreeAddr opReducedSrcAddr rfbTarAddr
          rfbDiff = diff
    , not (Path.isTreeAddrEmpty rfbDiff) ->
        do
          RM.debugInstantOpRM
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
copyRefVal :: (RM.ReduceMonad s r m) => VT.Tree -> m VT.Tree
copyRefVal tar = do
  case VT.treeNode tar of
    VT.TNAtom _ -> return tar
    VT.TNBottom _ -> return tar
    VT.TNRefCycle _ -> return tar
    VT.TNAtomCnstr c -> return (VT.mkAtomVTree $ VT.cnsAtom c)
    _ -> do
      e <- maybe (Common.buildASTExpr False tar) return (VT.treeExpr tar)
      RM.evalExprRM e

{- | Copy the value from the target cursor.

The tree cursor is the target cursor without the copied raw value.
-}
copyValFromTarTC ::
  (RM.ReduceMonad s r m) => Bool -> TCOps.TrCur -> Set.Set Path.TreeAddr -> TCOps.TrCur -> m VT.Tree
copyValFromTarTC isRefCyclic srcTC trail tarTC = do
  raw <- copyRefVal (Cursor.tcFocus tarTC)
  let dstAddr = Cursor.tcCanAddr tarTC
  -- evaluate the original expression.
  marked <- markOuterIdents (Cursor.tcCanAddr srcTC) (raw `Cursor.setTCFocus` tarTC)
  let visited = Set.insert dstAddr trail
  closeMarked <- checkRefDef marked visited

  -- If the target is ancestor or the source reference is a cyclic reference, we should mark the value as cyclic.
  -- For example, x: y: x.
  -- Or, {f: h: g, g: f} -> {f: h: g, g: h: g}, the nested g would find the ancestor g's value "f" because of
  -- expression copying. Then it becomes {f: h: g, g: h: f(Cyclic)}. So here, we should mark f's value as cyclic.
  if VT.treeIsCyclic (Cursor.tcFocus tarTC) || isRefCyclic
    then markCyclic closeMarked
    else return closeMarked
 where
  checkRefDef val visited = do
    -- Check if the referenced value has recurClose.
    let
      recurClose = VT.treeRecurClosed (Cursor.tcFocus tarTC)
      shouldClose = any addrHasDef visited
    if shouldClose || recurClose
      then markRecurClosed val
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
markOuterIdents srcAddr ptc = do
  let blockAddr = Cursor.tcCanAddr ptc
  utc <- TCOps.traverseTCSimple VT.subNodes (mark blockAddr) ptc
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
              then f (Cursor.tcCanAddr tc)
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
  RM.debugInstantRM
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
  searchIdent :: (RM.ReduceMonad s r m) => Path.ValPath -> TCOps.TrCur -> m (Maybe Path.TreeAddr)
  searchIdent ref xtc = do
    let fstSel = fromJust $ Path.headSel ref
    ident <- selToIdent fstSel
    resM <- searchTCIdent ident xtc
    return $ Cursor.tcCanAddr . fst <$> resM

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
            VT.TNBlock block -> VT.TNBlock $ VT.modifyBlockStruct (\s -> s{VT.stcClosed = True}) block
            _ -> VT.treeNode focus
        }

{- | Get the first identifier of the reference to absolute tree addr.

If the identifier is not found, it returns Nothing.

It does not follow the reference.
-}
getRefIdentAddr ::
  (RM.ReduceMonad s r m) =>
  Path.ValPath ->
  Maybe Path.TreeAddr ->
  TCOps.TrCur ->
  m (Maybe Path.TreeAddr)
getRefIdentAddr valPath origAddrsM tc = do
  let fstSel = fromJust $ Path.headSel valPath
  ident <- selToIdent fstSel
  let f x = searchTCIdent ident x >>= (\r -> return $ Cursor.tcCanAddr . fst <$> r)

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
  (RM.ReduceMonad s r m) => Path.ValPath -> TCOps.TrCur -> m DstTC
goTCLAAddr valPath tc = do
  when (Path.isValPathEmpty valPath) $ throwErrSt "empty valPath"
  let fstSel = fromJust $ Path.headSel valPath
  ident <- selToIdent fstSel
  searchTCIdent ident tc >>= \case
    Nothing -> do
      errMsg <- notFoundMsg ident (VT.treeExpr (Cursor.tcFocus tc) >>= AST.wpPos)
      return . Left $
        VT.mkBottomTree errMsg
    Just (identTC, _) -> do
      -- The ref is non-empty, so the rest must be a valid addr.
      let rest = fromJust $ Path.tailValPath valPath
          r = goDownTCAddr (Path.valPathToAddr rest) identTC
      return $ Right r

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
          typ <- VT.getFieldType (T.unpack $ TE.decodeUtf8 s)
          return $ typ == VT.SFTDefinition
        _ -> False
    )
    $ Path.addrToList p

selToIdent :: (Common.Env r s m) => Path.Selector -> m T.Text
selToIdent (Path.StringSel s) = return $ TE.decodeUtf8 s
selToIdent _ = throwErrSt "invalid selector"

{- | Search in the parent scope for the first identifier that can match the segment.

Also return if the identifier is a let binding.
-}
searchTCIdentInPar :: (RM.ReduceMonad s r m) => T.Text -> TCOps.TrCur -> m (Maybe (Path.TreeAddr, Bool))
searchTCIdentInPar name tc = do
  ptc <- Cursor.parentTCMust tc
  if Cursor.isTCTop ptc
    then return Nothing
    else do
      m <- searchTCIdent name ptc
      return $ maybe Nothing (\(x, y) -> Just (Cursor.tcCanAddr x, y)) m

{- | Search in the tree for the first identifier that can match the name.

Searching identifiers only searches for the identifiers declared in the block, not for the identifiers added by
unification with embeddings.

Return a pair. The first is address of the identifier, the second is the identifier is a let binding.

The child value will not be propagated to the parent block. Propagation is not needed because all static fields should
already exist.

The tree cursor must at least have the root segment.
-}
searchTCIdent :: (RM.ReduceMonad s r m) => T.Text -> TCOps.TrCur -> m (Maybe (TCOps.TrCur, Bool))
searchTCIdent name tc = do
  subM <- findIdent name tc
  maybe
    (goUp tc)
    ( \(identTC, isLB) -> do
        when isLB $ do
          -- Mark the ident as referred if it is a let binding.
          RM.markRMLetReferred (Cursor.tcCanAddr identTC)
          unrefLets <- RM.getRMUnreferredLets
          RM.debugInstantRM
            "searchLetBindValue"
            (printf "ident: %s, unrefLets: %s" (show $ Cursor.tcCanAddr identTC) (show unrefLets))
            tc
        return $ Just (identTC, isLB)
    )
    subM
 where
  mkSeg isLB = let nt = TE.encodeUtf8 name in Path.StructTASeg $ if isLB then Path.LetTASeg nt else Path.StringTASeg nt

  goUp :: (RM.ReduceMonad s r m) => TCOps.TrCur -> m (Maybe (TCOps.TrCur, Bool))
  goUp (Cursor.TreeCursor _ [(Path.RootTASeg, _)]) = return Nothing -- stop at the root.
  goUp utc = do
    ptc <- maybe (throwErrSt "already on the top") return $ Cursor.parentTC utc
    searchTCIdent name ptc

  -- TODO: findIdent for default disjunct?
  findIdent :: (Common.Env r s m) => T.Text -> TCOps.TrCur -> m (Maybe (TCOps.TrCur, Bool))
  findIdent ident blockTC = do
    case VT.treeNode (Cursor.tcFocus blockTC) of
      VT.TNBlock blk@(VT.Block{VT.blkStruct = struct})
        -- If the block reduces to non-struct, then the fields are not searchable in the block. The fields have
        -- behaved like mutable argument.
        -- For example, { x: {a:1, c:d, e}, e: {a: int} | {b: int}, d:1 }
        -- - merge -> {x: {a:1, c:d} | {a:1, c:d, b:int}, d:1, e: {..}}
        -- Then when we reduce the merged value, at /x/dj0/c, it finds d in the top /.
        | isNothing (VT.blkNonStructValue blk) -> do
            let
              inBlock = ident `Set.member` VT.stcBlockIdents struct
              m =
                catMaybes
                  [ do
                      sf <- VT.lookupStructIdentField ident struct
                      return (Cursor.mkSubTC (mkSeg False) (VT.ssfValue sf) blockTC, False)
                  , do
                      lb <- VT.lookupStructLet ident struct
                      return (Cursor.mkSubTC (mkSeg True) (VT.lbValue lb) blockTC, True)
                  ]
            if inBlock
              then case m of
                [] -> return Nothing
                [x] -> return $ Just x
                (fstTC, _) : _ ->
                  return $
                    Just
                      ( VT.mkBottomTree (printf "multiple fields found for %s" ident) `Cursor.setTCFocus` fstTC
                      , False
                      )
              else return Nothing
      VT.TNMutable (VT.Compreh c) -> do
        let binds = VT.cphIterBindings c
        RM.debugInstantRM
          "searchTCIdent"
          (printf "binds: %s" (show binds))
          blockTC
        foldM
          ( \acc (i, bind) ->
              if isJust acc
                then return acc
                else
                  let bindName = VT.cphBindName bind
                   in if bindName == ident
                        then do
                          RM.debugInstantRM
                            "searchTCIdent"
                            (printf "found in comprehension binding: %s" (show bindName))
                            blockTC
                          -- Since the bindName is an identifier and watchRefRM only watches referable identifiers, we
                          -- do not need to worry that the bindValTC will be accessed.
                          -- The ComprehIterBindingTASeg is used to make sure the address passes the cycle detection.
                          let bindValTC =
                                Cursor.mkSubTC
                                  (Path.ComprehTASeg (Path.ComprehIterBindingTASeg i))
                                  (VT.cphBindValue bind)
                                  blockTC
                          return $ Just (bindValTC, False)
                        else return acc
          )
          Nothing
          (reverse (zip [0 ..] binds))
      _ -> return Nothing

searchLetBindValue :: (RM.ReduceMonad s r m) => T.Text -> TCOps.TrCur -> m (Maybe VT.Tree)
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
