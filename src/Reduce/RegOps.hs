{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.RegOps where

import qualified AST
import Control.Monad.Reader (asks)
import qualified Cursor
import Data.Maybe (catMaybes, fromJust, isJust)
import Exception (throwErrSt)
import qualified MutEnv
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified TCursorOps
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

reduceAtomOpArg :: (RM.ReduceTCMonad s r m) => Path.TASeg -> m (Maybe VT.Tree)
reduceAtomOpArg seg =
  RM.debugSpanArgsTM "reduceAtomOpArg" (printf "seg: %s" (show seg)) $
    Mutate.mutValToArgsRM
      seg
      ( do
          MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
          reduce
          RM.withTree $ \x -> return $ case VT.treeNode x of
            VT.TNMutable mut -> do
              mv <- VT.getMutVal mut
              -- Make sure the mutval is an atom.
              _ <- VT.getAtomFromTree mv
              return mv
            _ -> Just x
      )

-- * Regular Unary Ops

regUnaryOp :: (RM.ReduceTCMonad s r m) => AST.UnaryOp -> VT.Tree -> m ()
regUnaryOp op _t = do
  t <- Mutate.reduceMutableArg Path.unaryOpTASeg
  case VT.treeNode t of
    VT.TNBottom _ -> RM.putTMTree t
    VT.TNMutable _ -> return ()
    VT.TNRefCycle (VT.RefCycleVertMerger _) -> RM.putTMTree t
    _
      | Just ta <- VT.getAtomFromTree t -> case (op, ta) of
          (AST.Plus, VT.Int i) -> ia i id
          (AST.Plus, VT.Float i) -> fa i id
          (AST.Minus, VT.Int i) -> ia i negate
          (AST.Minus, VT.Float i) -> fa i negate
          (AST.Not, VT.Bool b) -> RM.putTMTree (VT.mkAtomTree (VT.Bool (not b)))
          (AST.UnaRelOp uop, _) -> case (uop, ta) of
            (AST.NE, a) -> mkb (VT.BdNE a)
            (AST.LT, VT.Int i) -> mkib VT.BdLT i
            (AST.LT, VT.Float f) -> mkfb VT.BdLT f
            (AST.LE, VT.Int i) -> mkib VT.BdLE i
            (AST.LE, VT.Float f) -> mkfb VT.BdLE f
            (AST.GT, VT.Int i) -> mkib VT.BdGT i
            (AST.GT, VT.Float f) -> mkfb VT.BdGT f
            (AST.GE, VT.Int i) -> mkib VT.BdGE i
            (AST.GE, VT.Float f) -> mkfb VT.BdGE f
            (AST.ReMatch, VT.String p) -> RM.putTMTree (VT.mkBoundsTree [VT.BdStrMatch $ VT.BdReMatch p])
            (AST.ReNotMatch, VT.String p) -> RM.putTMTree (VT.mkBoundsTree [VT.BdStrMatch $ VT.BdReNotMatch p])
            _ -> putConflict
          _ -> putConflict
    _ -> putConflict
 where
  conflictErr :: VT.Tree
  conflictErr = VT.mkBottomTree $ printf "%s cannot be used for %s" (show _t) (show op)

  putConflict :: (RM.ReduceTCMonad s r m) => m ()
  putConflict = RM.putTMTree conflictErr

  ia :: (RM.ReduceTCMonad s r m) => Integer -> (Integer -> Integer) -> m ()
  ia a f = RM.putTMTree (VT.mkAtomTree (VT.Int $ f a))

  fa :: (RM.ReduceTCMonad s r m) => Double -> (Double -> Double) -> m ()
  fa a f = RM.putTMTree (VT.mkAtomTree (VT.Float $ f a))

  mkb :: (RM.ReduceTCMonad s r m) => VT.Bound -> m ()
  mkb b = RM.putTMTree (VT.mkBoundsTree [b])

  mkib :: (RM.ReduceTCMonad s r m) => VT.BdNumCmpOp -> Integer -> m ()
  mkib uop i = RM.putTMTree (VT.mkBoundsTree [VT.BdNumCmp $ VT.BdNumCmpCons uop (VT.NumInt i)])

  mkfb :: (RM.ReduceTCMonad s r m) => VT.BdNumCmpOp -> Double -> m ()
  mkfb uop f = RM.putTMTree (VT.mkBoundsTree [VT.BdNumCmp $ VT.BdNumCmpCons uop (VT.NumFloat f)])

-- * Regular Binary Ops

regBin :: (RM.ReduceTCMonad s r m) => AST.BinaryOp -> VT.Tree -> VT.Tree -> m ()
regBin op t1 t2 = regBinDir op (Path.L, t1) (Path.R, t2)

regBinDir ::
  (RM.ReduceTCMonad s r m) => AST.BinaryOp -> (Path.BinOpDirect, VT.Tree) -> (Path.BinOpDirect, VT.Tree) -> m ()
regBinDir op (d1, _t1) (d2, _t2) = do
  RM.withAddrAndFocus $ \addr _ ->
    logDebugStr $
      printf "regBinDir: addr: %s, %s: %s with %s: %s" (show addr) (show d1) (show _t1) (show d2) (show _t2)

  t1M <- reduceAtomOpArg (Path.toBinOpTASeg d1)
  t2M <- reduceAtomOpArg (Path.toBinOpTASeg d2)

  RM.withAddrAndFocus $ \addr _ ->
    logDebugStr $
      printf "regBinDir: addr: %s, reduced args, %s: %s with %s: %s" (show addr) (show d1) (show t1M) (show d2) (show t2M)

  case (t1M, t2M) of
    (Just t1, Just t2) -> case (VT.treeNode t1, VT.treeNode t2) of
      (VT.TNBottom _, _) -> RM.putTMTree t1
      (_, VT.TNBottom _) -> RM.putTMTree t2
      (VT.TNRefCycle (VT.RefCycleVertMerger _), _) -> RM.putTMTree t1
      (_, VT.TNRefCycle (VT.RefCycleVertMerger _)) -> RM.putTMTree t2
      (VT.TNAtom l1, _) -> regBinLeftAtom op (d1, l1, t1) (d2, t2)
      (_, VT.TNAtom l2) -> regBinLeftAtom op (d2, l2, t2) (d1, t1)
      (VT.TNStruct s1, _) -> regBinLeftStruct op (d1, s1, t1) (d2, t2)
      (_, VT.TNStruct s2) -> regBinLeftStruct op (d2, s2, t2) (d1, t1)
      (VT.TNDisj dj1, _) -> regBinLeftDisj op (d1, dj1, t1) (d2, t2)
      (_, VT.TNDisj dj2) -> regBinLeftDisj op (d2, dj2, t2) (d1, t1)
      _ -> regBinLeftOther op (d1, t1) (d2, t2)
    (Just t1, _)
      | VT.TNBottom _ <- VT.treeNode t1 -> RM.putTMTree t1
      | VT.TNRefCycle (VT.RefCycleVertMerger _) <- VT.treeNode t1 -> RM.putTMTree t1
    (_, Just t2)
      | VT.TNBottom _ <- VT.treeNode t2 -> RM.putTMTree t2
      | VT.TNRefCycle (VT.RefCycleVertMerger _) <- VT.treeNode t2 -> RM.putTMTree t2
    _ -> return ()

regBinLeftAtom ::
  (RM.ReduceTCMonad s r m) => AST.BinaryOp -> (Path.BinOpDirect, VT.AtomV, VT.Tree) -> (Path.BinOpDirect, VT.Tree) -> m ()
regBinLeftAtom op (d1, ta1, t1) (d2, t2) = do
  logDebugStr $ printf "regBinLeftAtom: %s (%s: %s) (%s: %s)" (show op) (show d1) (show ta1) (show d2) (show t2)
  if
    -- comparison operators
    | Data.Maybe.isJust (lookup op cmpOps) -> case VT.treeNode t2 of
        VT.TNAtom ta2 ->
          let
            a2 = VT.amvAtom ta2
            f :: (VT.Atom -> VT.Atom -> Bool)
            f = Data.Maybe.fromJust (lookup op cmpOps)
            rb = Right . VT.Bool
            r = case (a1, a2) of
              (VT.String _, VT.String _) -> rb $ dirApply f (d1, a1) a2
              (VT.Int _, VT.Int _) -> rb $ dirApply f (d1, a1) a2
              (VT.Int _, VT.Float _) -> rb $ dirApply f (d1, a1) a2
              (VT.Float _, VT.Int _) -> rb $ dirApply f (d1, a1) a2
              (VT.Float _, VT.Float _) -> rb $ dirApply f (d1, a1) a2
              (VT.Bool _, VT.Bool _) -> rb $ dirApply f (d1, a1) a2
              (VT.Null, _) -> rb $ dirApply f (d1, a1) a2
              (_, VT.Null) -> rb $ dirApply f (d2, a2) a1
              _ -> Left $ uncmpAtoms a1 a2
           in
            case r of
              Right b -> RM.putTMTree $ VT.mkAtomTree b
              Left err -> RM.putTMTree err
        VT.TNDisj dj2 -> regBinLeftDisj op (d2, dj2, t2) (d1, t1)
        VT.TNStruct _ -> RM.putTMTree $ cmpNull a1 t2
        VT.TNList _ -> RM.putTMTree $ cmpNull a1 t2
        _ -> regBinLeftOther op (d2, t2) (d1, t1)
    -- arithmetic operators
    | op `elem` arithOps -> case VT.treeNode t2 of
        VT.TNAtom ta2 ->
          let
            ri = Right . VT.Int
            rf = Right . VT.Float
            r = case op of
              AST.Add -> case (a1, VT.amvAtom ta2) of
                (VT.Int i1, VT.Int i2) -> ri $ dirApply (+) (d1, i1) i2
                (VT.Int i1, VT.Float i2) -> rf $ dirApply (+) (d1, fromIntegral i1) i2
                (VT.Float i1, VT.Int i2) -> rf $ dirApply (+) (d1, i1) (fromIntegral i2)
                (VT.String s1, VT.String s2) -> Right . VT.String $ dirApply (++) (d1, s1) s2
                _ -> Left $ mismatch op a1 (VT.amvAtom ta2)
              AST.Sub -> case (a1, VT.amvAtom ta2) of
                (VT.Int i1, VT.Int i2) -> ri $ dirApply (-) (d1, i1) i2
                (VT.Int i1, VT.Float i2) -> rf $ dirApply (-) (d1, fromIntegral i1) i2
                (VT.Float i1, VT.Int i2) -> rf $ dirApply (-) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (VT.amvAtom ta2)
              AST.Mul -> case (a1, VT.amvAtom ta2) of
                (VT.Int i1, VT.Int i2) -> ri $ dirApply (*) (d1, i1) i2
                (VT.Int i1, VT.Float i2) -> rf $ dirApply (*) (d1, fromIntegral i1) i2
                (VT.Float i1, VT.Int i2) -> rf $ dirApply (*) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (VT.amvAtom ta2)
              AST.Div -> case (a1, VT.amvAtom ta2) of
                (VT.Int i1, VT.Int i2) -> rf $ dirApply (/) (d1, fromIntegral i1) (fromIntegral i2)
                (VT.Int i1, VT.Float i2) -> rf $ dirApply (/) (d1, fromIntegral i1) i2
                (VT.Float i1, VT.Int i2) -> rf $ dirApply (/) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (VT.amvAtom ta2)
              _ -> Left $ mismatch op a1 (VT.amvAtom ta2)
           in
            case r of
              Right b -> RM.putTMTree $ VT.mkAtomTree b
              Left err -> RM.putTMTree err
        VT.TNDisj dj2 -> regBinLeftDisj op (d2, dj2, t2) (d1, t1)
        VT.TNStruct _ -> RM.putTMTree $ mismatchArith a1 t2
        VT.TNList _ -> RM.putTMTree $ mismatchArith a1 t2
        _ -> regBinLeftOther op (d2, t2) (d1, t1)
    | otherwise -> RM.putTMTree (VT.mkBottomTree $ printf "operator %s is not supported" (show op))
 where
  a1 = VT.amvAtom ta1
  cmpOps = [(AST.Equ, (==)), (AST.BinRelOp AST.NE, (/=))]
  arithOps = [AST.Add, AST.Sub, AST.Mul, AST.Div]

  uncmpAtoms :: VT.Atom -> VT.Atom -> VT.Tree
  uncmpAtoms x y = VT.mkBottomTree $ printf "%s and %s are not comparable" (show x) (show y)

  cmpNull :: VT.Atom -> VT.Tree -> VT.Tree
  cmpNull a t =
    if
      -- There is no way for a non-atom to be compared with a non-null atom.
      | a /= VT.Null -> mismatch op a t
      | op == AST.Equ -> VT.mkAtomTree (VT.Bool False)
      | op == AST.BinRelOp AST.NE -> VT.mkAtomTree (VT.Bool True)
      | otherwise -> VT.mkBottomTree $ printf "operator %s is not supported" (show op)

  mismatchArith :: (Show a, Show b) => a -> b -> VT.Tree
  mismatchArith = mismatch op

dirApply :: (a -> a -> b) -> (Path.BinOpDirect, a) -> a -> b
dirApply f (di1, i1) i2 = if di1 == Path.L then f i1 i2 else f i2 i1

mismatch :: (Show a, Show b) => AST.BinaryOp -> a -> b -> VT.Tree
mismatch op x y = VT.mkBottomTree $ printf "%s can not be used for %s and %s" (show op) (show x) (show y)

regBinLeftStruct ::
  (RM.ReduceTCMonad s r m) =>
  AST.BinaryOp ->
  (Path.BinOpDirect, VT.Struct VT.Tree, VT.Tree) ->
  (Path.BinOpDirect, VT.Tree) ->
  m ()
regBinLeftStruct op (d1, _, t1) (d2, t2) = case VT.treeNode t2 of
  VT.TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1)
  _ -> RM.putTMTree (mismatch op t1 t2)

regBinLeftDisj ::
  (RM.ReduceTCMonad s r m) =>
  AST.BinaryOp ->
  (Path.BinOpDirect, VT.Disj VT.Tree, VT.Tree) ->
  (Path.BinOpDirect, VT.Tree) ->
  m ()
regBinLeftDisj op (d1, dj1, t1) (d2, t2) = case dj1 of
  VT.Disj{VT.dsjDefault = Just d} -> regBinDir op (d1, d) (d2, t2)
  _ -> case VT.treeNode t2 of
    VT.TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1)
    _ -> RM.putTMTree (mismatch op t1 t2)

regBinLeftOther ::
  (RM.ReduceTCMonad s r m) => AST.BinaryOp -> (Path.BinOpDirect, VT.Tree) -> (Path.BinOpDirect, VT.Tree) -> m ()
regBinLeftOther op (d1, t1) (d2, t2) = do
  RM.withAddrAndFocus $ \addr _ ->
    logDebugStr $ printf "regBinLeftOther: addr: %s, %s: %s, %s: %s" (show addr) (show d1) (show t1) (show d2) (show t2)
  case (VT.treeNode t1, t2) of
    (VT.TNRefCycle _, _) -> return ()
    (VT.TNAtomCnstr c, _) -> do
      na <- regBinDir op (d1, VT.mkNewTree (VT.TNAtom $ VT.cnsAtom c)) (d2, t2) >> RM.getRMTree
      case VT.treeNode na of
        VT.TNAtom atom -> RM.putTMTree (VT.mkNewTree (VT.TNAtomCnstr $ VT.updateCnstrAtom atom c))
        _ -> undefined
    _ -> RM.putTMTree (VT.mkBottomTree mismatchErr)
 where
  mismatchErr :: String
  mismatchErr = printf "values %s and %s cannot be used for %s" (show t1) (show t2) (show op)

{- | Index the tree with the segments.

The index should have a list of arguments where the first argument is the tree to be indexed, and the rest of the
arguments are the segments.
-}
index ::
  (RM.ReduceTCMonad s r m) =>
  Maybe (Path.TreeAddr, Path.TreeAddr) ->
  VT.RefArg VT.Tree ->
  m (Either VT.Tree (Maybe Path.TreeAddr))
index origAddrsM (VT.RefPath var sels) = do
  refSels <- mapM (\(i, _) -> reduceAtomOpArg (Path.MutableArgTASeg i)) (zip [0 ..] sels)
  let refRestPathM = VT.treesToValPath . Data.Maybe.catMaybes $ refSels
  logDebugStr $ printf "index: refRestPathM is reduced to %s" (show refRestPathM)
  maybe
    (return $ Right Nothing)
    ( \refRestPath -> do
        lbM <- RefSys.searchRMLetBindValue var
        case lbM of
          Just lb -> do
            logDebugStr $ printf "index: let %s bind value is %s" var (show lb)
            case sels of
              -- If there are no selectors, it is a simple reference to the let value. We treat it like pending value.
              [] -> return $ Left lb
              _ -> do
                let newRef = case VT.treeNode lb of
                      -- If the let value is a reference, we append the selectors to the reference.
                      VT.TNMutable m
                        | Just ref <- VT.getRefFromMutable m ->
                            VT.mkMutableTree $
                              VT.Ref $
                                ref
                                  { VT.refArg = VT.appendRefArgs sels (VT.refArg ref)
                                  , VT.refOrigAddrs = origAddrsM
                                  }
                      _ -> VT.mkMutableTree $ VT.Ref $ (VT.mkIndexRef (lb : sels)){VT.refOrigAddrs = origAddrsM}
                return $ Left newRef
          _ -> do
            let newRef = Path.appendValPaths (Path.ValPath [Path.StringSel var]) refRestPath
            -- Use the index's original addrs since it is the referable node
            r <- RefSys.deref newRef origAddrsM
            return $ Right r
    )
    refRestPathM
-- in-place expression, like ({}).a, or regular functions.
index _ (VT.RefIndex (end : rest)) = do
  idxSels <- mapM (\(i, _) -> reduceAtomOpArg (Path.MutableArgTASeg i)) (zip [1 ..] rest)
  let idxRefM = VT.treesToValPath . Data.Maybe.catMaybes $ idxSels
  logDebugStr $ printf "index: idxRefM is reduced to %s" (show idxRefM)
  maybe
    (return $ Right Nothing)
    ( \idxRef -> do
        _indexExpr idxRef end
        return $ Right Nothing
    )
    idxRefM
index _ _ = throwErrSt "invalid index"

_indexExpr :: (RM.ReduceTCMonad s r m) => Path.ValPath -> VT.Tree -> m ()
_indexExpr idxRef end = do
  MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
  orig <- RM.getRMTree -- save stub
  RM.putTMTree end
  reduce
  RM.unlessFocusBottom () $ do
    -- descendTM can not be used here because it would change the tree cursor.
    tc <- RM.getTMCursor
    maybe
      -- If the index is not found, the original tree (stub) is restored.
      (RM.putTMTree orig)
      (RM.putTMTree . Cursor.tcFocus)
      (TCursorOps.goDownTCAddr (Path.valPathToAddr idxRef) tc)

    RM.withAddrAndFocus $ \_ r -> logDebugStr $ printf "index: the indexed is %s" (show r)

evalIndexArg :: (RM.ReduceTCMonad s r m) => Int -> m VT.Tree
evalIndexArg i =
  Mutate.mutValToArgsRM
    (Path.MutableArgTASeg i)
    ( do
        MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
        reduce >> RM.getRMTree
    )

comprehend :: (RM.ReduceTCMonad s r m) => VT.Comprehension VT.Tree -> m ()
comprehend c = do
  t <- Mutate.reduceMutableArg (Path.ComprehTASeg Path.ComprehStartTASeg)
  RM.withAddrAndFocus $ \addr _ ->
    logDebugStr $ printf "comprehend: addr: %s start reduced to: %s" (show addr) (show t)
  case VT.treeNode t of
    VT.TNBottom _ -> RM.putTMTree t
    VT.TNMutable _ -> return ()
    _
      | Just (VT.Bool b) <- VT.getAtomFromTree t ->
          if b
            then do
              RM.putTMTree (VT.cphStruct c)
              MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
              reduce
            else RM.putTMTree $ VT.mkStructTree VT.emptyStruct
    _ -> RM.putTMTree $ VT.mkBottomTree $ printf "%s is not a boolean" (VT.showTreeSymbol t)