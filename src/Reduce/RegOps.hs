{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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
import qualified TCOps
import Text.Printf (printf)
import Util (logDebugStr)
import qualified Value.Tree as VT

-- reduceAtomOpArg :: (RM.ReduceMonad s r m) => Path.TASeg -> m (Maybe VT.Tree)
-- reduceAtomOpArg seg = undefined

-- reduceAtomOpArg :: (RM.ReduceTCMonad s r m) => Path.TASeg -> m (Maybe VT.Tree)
-- reduceAtomOpArg seg =
--   RM.debugSpanArgsTM "reduceAtomOpArg" (printf "seg: %s" (show seg)) $
--     Mutate.mutValToArgsRM
--       seg
--       ( do
--           MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
--           reduce
--           RM.withTree $ \x -> return $ case VT.treeNode x of
--             VT.TNMutable mut -> do
--               mv <- VT.getMutVal mut
--               -- Make sure the mutval is an atom.
--               _ <- VT.getAtomFromTree mv
--               return mv
--             _ -> Just x
--       )

-- handleRefCycle :: VT.RefCycle -> TCOps.TrCur -> Maybe VT.Tree
-- handleRefCycle (VT.RefCycle addr) opTC = Nothing

-- if addr == Cursor.tcTreeAddr opTC
--   then Nothing
--   else Just $ VT.mkNewTree $ VT.TNRefCycle (VT.RefCycle addr)

-- * Regular Unary Ops

retVal :: (RM.ReduceMonad s r m) => VT.Tree -> m (Maybe VT.Tree)
retVal = return . Just

regUnaryOp :: (RM.ReduceMonad s r m) => AST.UnaryOp -> TCOps.TrCur -> m (Maybe VT.Tree)
regUnaryOp op opTC = do
  argTC <- TCOps.goDownTCSegMust Path.unaryOpTASeg opTC
  tM <- Mutate.reduceToConcrete argTC
  case tM of
    Just t -> case VT.treeNode t of
      VT.TNBottom _ -> retVal t
      VT.TNMutable _ -> return Nothing
      VT.TNRefCycle -> return Nothing
      _
        | Just ta <- VT.getAtomFromTree t -> case (op, ta) of
            (AST.Plus, VT.Int i) -> ia i id
            (AST.Plus, VT.Float i) -> fa i id
            (AST.Minus, VT.Int i) -> ia i negate
            (AST.Minus, VT.Float i) -> fa i negate
            (AST.Not, VT.Bool b) -> retVal (VT.mkAtomTree (VT.Bool (not b)))
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
              (AST.ReMatch, VT.String p) -> retVal (VT.mkBoundsTree [VT.BdStrMatch $ VT.BdReMatch p])
              (AST.ReNotMatch, VT.String p) -> retVal (VT.mkBoundsTree [VT.BdStrMatch $ VT.BdReNotMatch p])
              _ -> returnErr t
            _ -> returnErr t
      _ -> returnErr t
    _ -> return Nothing
 where
  returnErr v = retVal $ VT.mkBottomTree $ printf "%s cannot be used for %s" (show v) (show op)

  ia a f = retVal (VT.mkAtomTree (VT.Int $ f a))

  fa a f = retVal (VT.mkAtomTree (VT.Float $ f a))

  mkb b = retVal (VT.mkBoundsTree [b])

  mkib uop i = retVal (VT.mkBoundsTree [VT.BdNumCmp $ VT.BdNumCmpCons uop (VT.NumInt i)])

  mkfb uop f = retVal (VT.mkBoundsTree [VT.BdNumCmp $ VT.BdNumCmpCons uop (VT.NumFloat f)])

-- * Regular Binary Ops

regBin ::
  (RM.ReduceMonad s r m) => AST.BinaryOp -> TCOps.TrCur -> TCOps.TrCur -> m (Maybe VT.Tree)
regBin op tc1 tc2 = regBinDir op (Path.L, tc1) (Path.R, tc2)

regBinDir ::
  (RM.ReduceMonad s r m) =>
  AST.BinaryOp ->
  (Path.BinOpDirect, TCOps.TrCur) ->
  (Path.BinOpDirect, TCOps.TrCur) ->
  m (Maybe VT.Tree)
regBinDir op (d1, _tc1) (d2, _tc2) = do
  -- RM.withAddrAndFocus $ \addr _ ->
  --   logDebugStr $
  --     printf "regBinDir: addr: %s, %s: %s with %s: %s" (show addr) (show d1) (show _t1) (show d2) (show _t2)

  t1M <- Mutate.reduceToConcrete _tc1
  t2M <- Mutate.reduceToConcrete _tc2

  opTC <- Cursor.parentTCMust _tc1
  RM.debugInstantOpRM
    "regBinDir"
    (printf "reduced args, %s: %s with %s: %s" (show d1) (show t1M) (show d2) (show t2M))
    (Cursor.tcTreeAddr opTC)

  case (t1M, t2M) of
    (Just t1, Just t2) ->
      let
        tc1 = t1 `Cursor.setTCFocus` _tc1
        tc2 = t2 `Cursor.setTCFocus` _tc2
       in
        case (VT.treeNode t1, VT.treeNode t2) of
          (VT.TNBottom _, _) -> retVal t1
          (_, VT.TNBottom _) -> retVal t2
          (VT.TNRefCycle, _) -> return Nothing
          (_, VT.TNRefCycle) -> return Nothing
          (VT.TNAtom l1, _) -> regBinLeftAtom op (d1, l1, tc1) (d2, tc2)
          (_, VT.TNAtom l2) -> regBinLeftAtom op (d2, l2, tc2) (d1, tc1)
          (VT.TNStruct s1, _) -> regBinLeftStruct op (d1, s1, tc1) (d2, tc2)
          (_, VT.TNStruct s2) -> regBinLeftStruct op (d2, s2, tc2) (d1, tc1)
          (VT.TNDisj dj1, _) -> regBinLeftDisj op (d1, dj1, tc1) (d2, tc2)
          (_, VT.TNDisj dj2) -> regBinLeftDisj op (d2, dj2, tc2) (d1, tc1)
          _ -> regBinLeftOther op (d1, tc1) (d2, tc2)
    (Just t1, _)
      | VT.TNBottom _ <- VT.treeNode t1 -> retVal t1
      | VT.TNRefCycle <- VT.treeNode t1 -> return Nothing
    (_, Just t2)
      | VT.TNBottom _ <- VT.treeNode t2 -> retVal t2
      | VT.TNRefCycle <- VT.treeNode t2 -> return Nothing
    _ -> return Nothing

regBinLeftAtom ::
  (RM.ReduceMonad s r m) =>
  AST.BinaryOp ->
  (Path.BinOpDirect, VT.AtomV, TCOps.TrCur) ->
  (Path.BinOpDirect, TCOps.TrCur) ->
  m (Maybe VT.Tree)
regBinLeftAtom op (d1, ta1, tc1) (d2, tc2) = do
  let
    t1 = Cursor.tcFocus tc1
    t2 = Cursor.tcFocus tc2
  logDebugStr $ printf "regBinLeftAtom: %s (%s: %s) (%s: %s)" (show op) (show d1) (show ta1) (show d2) (show t2)
  if
    -- comparison operators
    | isJust (lookup op cmpOps) -> case VT.treeNode t2 of
        VT.TNAtom ta2 ->
          let
            a2 = VT.amvAtom ta2
            f :: (VT.Atom -> VT.Atom -> Bool)
            f = fromJust (lookup op cmpOps)
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
              Right b -> retVal $ VT.mkAtomTree b
              Left err -> retVal err
        VT.TNDisj dj2 -> regBinLeftDisj op (d2, dj2, tc2) (d1, tc1)
        VT.TNStruct _ -> retVal $ cmpNull a1 t2
        VT.TNList _ -> retVal $ cmpNull a1 t2
        _ -> regBinLeftOther op (d2, tc2) (d1, tc1)
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
              Right b -> retVal $ VT.mkAtomTree b
              Left err -> retVal err
        VT.TNDisj dj2 -> regBinLeftDisj op (d2, dj2, tc2) (d1, tc1)
        VT.TNStruct _ -> retVal $ mismatchArith a1 t2
        VT.TNList _ -> retVal $ mismatchArith a1 t2
        _ -> regBinLeftOther op (d2, tc2) (d1, tc1)
    | otherwise -> retVal (VT.mkBottomTree $ printf "operator %s is not supported" (show op))
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
  (RM.ReduceMonad s r m) =>
  AST.BinaryOp ->
  (Path.BinOpDirect, VT.Struct VT.Tree, TCOps.TrCur) ->
  (Path.BinOpDirect, TCOps.TrCur) ->
  m (Maybe VT.Tree)
regBinLeftStruct op (d1, _, tc1) (d2, tc2) = do
  let
    t1 = Cursor.tcFocus tc1
    t2 = Cursor.tcFocus tc2
  case VT.treeNode t2 of
    VT.TNAtom a2 -> regBinLeftAtom op (d2, a2, tc2) (d1, tc1)
    _ -> retVal (mismatch op t1 t2)

regBinLeftDisj ::
  (RM.ReduceMonad s r m) =>
  AST.BinaryOp ->
  (Path.BinOpDirect, VT.Disj VT.Tree, TCOps.TrCur) ->
  (Path.BinOpDirect, TCOps.TrCur) ->
  m (Maybe VT.Tree)
regBinLeftDisj op (d1, dj1, tc1) (d2, tc2) = do
  let
    t1 = Cursor.tcFocus tc1
    t2 = Cursor.tcFocus tc2
  case dj1 of
    VT.Disj{VT.dsjDefault = Just d} -> regBinDir op (d1, d `Cursor.setTCFocus` tc1) (d2, tc2)
    _ -> case VT.treeNode t2 of
      VT.TNAtom a2 -> regBinLeftAtom op (d2, a2, tc2) (d1, tc1)
      _ -> retVal (mismatch op t1 t2)

regBinLeftOther ::
  (RM.ReduceMonad s r m) =>
  AST.BinaryOp ->
  (Path.BinOpDirect, TCOps.TrCur) ->
  (Path.BinOpDirect, TCOps.TrCur) ->
  m (Maybe VT.Tree)
regBinLeftOther op (d1, tc1) (d2, tc2) = do
  let
    t1 = Cursor.tcFocus tc1
    t2 = Cursor.tcFocus tc2
  -- RM.withAddrAndFocus $ \addr _ ->
  --   logDebugStr $ printf "regBinLeftOther: addr: %s, %s: %s, %s: %s" (show addr) (show d1) (show t1) (show d2) (show t2)
  case (VT.treeNode t1, t2) of
    (VT.TNRefCycle, _) -> return Nothing
    (VT.TNAtomCnstr c, _) -> do
      naM <- regBinDir op (d1, VT.mkNewTree (VT.TNAtom $ VT.cnsAtom c) `Cursor.setTCFocus` tc1) (d2, tc2)
      maybe
        (return Nothing)
        ( \na ->
            case VT.treeNode na of
              VT.TNAtom atom -> retVal (VT.mkNewTree (VT.TNAtomCnstr $ VT.updateCnstrAtom atom c))
              _ -> undefined
        )
        naM
    _ -> retVal (VT.mkBottomTree $ mismatchErr t1 t2)
 where
  mismatchErr t1 t2 = printf "values %s and %s cannot be used for %s" (show t1) (show t2) (show op)

-- MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
-- orig <- RM.getTMTree -- save stub
-- RM.putTMTree operand
-- reduce
-- RM.unlessFocusBottom () $ do
-- descendTM can not be used here because it would change the tree cursor.
-- tc <- RM.getTMCursor
-- maybe
-- If the index is not found, the original tree (stub) is restored.
-- (RM.putTMTree orig)
-- (RM.putTMTree . Cursor.tcFocus)
-- (TCOps.goDownTCAddr (Path.valPathToAddr idxRef) tc)

-- RM.withAddrAndFocus
-- \$ \_ r -> logDebugStr $ printf "index: the indexed is %s" (show r)

-- evalIndexArg :: (RM.ReduceTCMonad s r m) => Int -> m VT.Tree
-- evalIndexArg i =
--   Mutate.mutValToArgsRM
--     (Path.MutableArgTASeg i)
--     ( do
--         MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
--         reduce >> RM.getTMTree
--     )

comprehend :: (RM.ReduceTCMonad s r m) => VT.Comprehension VT.Tree -> m ()
comprehend c = undefined

-- comprehend c = do
--   t <- Mutate.reduceMutableArg (Path.ComprehTASeg Path.ComprehStartTASeg)
--   RM.withAddrAndFocus $ \addr _ ->
--     logDebugStr $ printf "comprehend: addr: %s start reduced to: %s" (show addr) (show t)
--   case VT.treeNode t of
--     VT.TNBottom _ -> RM.putTMTree t
--     VT.TNMutable _ -> return ()
--     _
--       | Just (VT.Bool b) <- VT.getAtomFromTree t ->
--           if b
--             then do
--               RM.putTMTree (VT.cphStruct c)
--               MutEnv.Functions{MutEnv.fnReduce = reduce} <- asks MutEnv.getFuncs
--               reduce
--             else RM.putTMTree $ VT.mkStructTree VT.emptyStruct
--     _ -> RM.putTMTree $ VT.mkBottomTree $ printf "%s is not a boolean" (VT.showTreeSymbol t)