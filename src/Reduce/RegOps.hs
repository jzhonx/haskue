{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Reduce.RegOps where

import qualified AST
import Cursor
import Data.Maybe (fromJust, isJust)
import Path
import Reduce.RMonad (
  ReduceMonad,
  debugInstantOpRM,
  debugSpanArgsRM,
 )
import {-# SOURCE #-} Reduce.Root (reduce)
import Text.Printf (printf)
import Value

-- * Regular Unary Ops

retVal :: (ReduceMonad s r m) => Tree -> m (Maybe Tree)
retVal = return . Just

{- | Reduce the tree cursor to concrete.

According to the spec,
A value is concrete if it is either an atom, or a struct whose field values are all concrete, recursively.
-}
reduceToConcrete :: (ReduceMonad s r m) => TrCur -> m (Maybe Tree)
reduceToConcrete tc = debugSpanArgsRM "reduceToConcrete" (show tc) id tc $ do
  -- Reduce the argument and get the CUE value.
  rM <- rtrCUE <$> reduce tc
  return $ do
    cval <- rM
    case rtrBottom cval of
      Just _ -> return cval
      _ -> rtrConcrete cval

regUnaryOp :: (ReduceMonad s r m) => AST.UnaryOp -> TrCur -> m (Maybe Tree)
regUnaryOp op opTC = do
  argTC <- goDownTCSegMust unaryOpTASeg opTC
  tM <- reduceToConcrete argTC
  case tM of
    Just t -> case treeNode t of
      TNBottom _ -> retVal t
      _
        | Just ta <- rtrAtom t -> case (AST.wpVal op, ta) of
            (AST.Plus, Int i) -> ia i id
            (AST.Plus, Float i) -> fa i id
            (AST.Minus, Int i) -> ia i negate
            (AST.Minus, Float i) -> fa i negate
            (AST.Not, Bool b) -> retVal (mkAtomTree (Bool (not b)))
            (AST.UnaRelOp uop, _) -> case (uop, ta) of
              (AST.NE, a) -> mkb (BdNE a)
              (AST.LT, Int i) -> mkib BdLT i
              (AST.LT, Float f) -> mkfb BdLT f
              (AST.LE, Int i) -> mkib BdLE i
              (AST.LE, Float f) -> mkfb BdLE f
              (AST.GT, Int i) -> mkib BdGT i
              (AST.GT, Float f) -> mkfb BdGT f
              (AST.GE, Int i) -> mkib BdGE i
              (AST.GE, Float f) -> mkfb BdGE f
              (AST.ReMatch, String p) -> retVal (mkBoundsTree [BdStrMatch $ BdReMatch p])
              (AST.ReNotMatch, String p) -> retVal (mkBoundsTree [BdStrMatch $ BdReNotMatch p])
              _ -> returnErr t
            _ -> returnErr t
      _ -> returnErr t
    _ -> return Nothing
 where
  returnErr v = retVal $ mkBottomTree $ printf "%s cannot be used for %s" (show v) (show op)

  ia a f = retVal (mkAtomTree (Int $ f a))

  fa a f = retVal (mkAtomTree (Float $ f a))

  mkb b = retVal (mkBoundsTree [b])

  mkib uop i = retVal (mkBoundsTree [BdNumCmp $ BdNumCmpCons uop (NumInt i)])

  mkfb uop f = retVal (mkBoundsTree [BdNumCmp $ BdNumCmpCons uop (NumFloat f)])

-- * Regular Binary Ops

regBin ::
  (ReduceMonad s r m) => AST.BinaryOp -> TrCur -> TrCur -> m (Maybe Tree)
regBin op tc1 tc2 = regBinDir op (L, tc1) (R, tc2)

regBinDir ::
  (ReduceMonad s r m) =>
  AST.BinaryOp ->
  (BinOpDirect, TrCur) ->
  (BinOpDirect, TrCur) ->
  m (Maybe Tree)
regBinDir op (d1, _tc1) (d2, _tc2) = do
  t1M <- reduceToConcrete _tc1
  t2M <- reduceToConcrete _tc2

  opTC <- parentTCMust _tc1
  debugInstantOpRM
    "regBinDir"
    (printf "reduced args,op: %s, %s: %s with %s: %s" (show op) (show d1) (show t1M) (show d2) (show t2M))
    (tcCanAddr opTC)

  case (t1M, t2M) of
    (Just t1, Just t2) ->
      let
        tc1 = t1 `setTCFocus` _tc1
        tc2 = t2 `setTCFocus` _tc2
       in
        case (treeNode t1, treeNode t2) of
          (TNBottom _, _) -> retVal $ regBinLeftBottom op t1 t2M
          (_, TNBottom _) -> retVal $ regBinLeftBottom op t2 t1M
          (TNAtom l1, _) -> regBinLeftAtom op (d1, l1, tc1) (d2, tc2)
          (_, TNAtom l2) -> regBinLeftAtom op (d2, l2, tc2) (d1, tc1)
          (TNBlock s1, _) -> regBinLeftBlock op (d1, s1, tc1) (d2, tc2)
          (_, TNBlock s2) -> regBinLeftBlock op (d2, s2, tc2) (d1, tc1)
          (TNDisj dj1, _) -> regBinLeftDisj op (d1, dj1, tc1) (d2, tc2)
          (_, TNDisj dj2) -> regBinLeftDisj op (d2, dj2, tc2) (d1, tc1)
          _ -> regBinLeftOther op (d1, tc1) (d2, tc2)
    (Just t1, _)
      | TNBottom _ <- treeNode t1 -> retVal $ regBinLeftBottom op t1 t2M
    (_, Just t2)
      | TNBottom _ <- treeNode t2 -> retVal $ regBinLeftBottom op t2 t1M
    _ -> return Nothing

regBinLeftBottom ::
  AST.BinaryOp ->
  Tree ->
  Maybe Tree ->
  Tree
regBinLeftBottom (AST.wpVal -> AST.Equ) _ t2M = case t2M of
  -- If the second argument is a bottom, then the result is True.
  Just t2
    | TNBottom _ <- treeNode t2 -> mkAtomTree (Bool True)
  -- If the second argument is incomplete which is treated as bottom, then the result is True.
  Nothing -> mkAtomTree (Bool True)
  _ -> mkAtomTree (Bool False)
regBinLeftBottom (AST.wpVal -> AST.BinRelOp AST.NE) b1 t2M = do
  let r = regBinLeftBottom (pure AST.Equ) b1 t2M
  case rtrAtom r of
    Just (Bool b) -> mkAtomTree (Bool (not b))
    _ -> r
regBinLeftBottom _ b1 _ = b1

regBinLeftAtom ::
  (ReduceMonad s r m) =>
  AST.BinaryOp ->
  (BinOpDirect, Atom, TrCur) ->
  (BinOpDirect, TrCur) ->
  m (Maybe Tree)
regBinLeftAtom op@(AST.wpVal -> opv) (d1, a1, tc1) (d2, tc2) = do
  let t2 = tcFocus tc2
  if
    -- comparison operators
    | isJust (lookup opv cmpOps) -> case treeNode t2 of
        TNAtom a2 ->
          let
            f :: (Atom -> Atom -> Bool)
            f = fromJust (lookup opv cmpOps)
            rb = Right . Bool
            r = case (a1, a2) of
              (String _, String _) -> rb $ dirApply f (d1, a1) a2
              (Int _, Int _) -> rb $ dirApply f (d1, a1) a2
              (Int _, Float _) -> rb $ dirApply f (d1, a1) a2
              (Float _, Int _) -> rb $ dirApply f (d1, a1) a2
              (Float _, Float _) -> rb $ dirApply f (d1, a1) a2
              (Bool _, Bool _) -> rb $ dirApply f (d1, a1) a2
              (Null, _) -> rb $ dirApply f (d1, a1) a2
              (_, Null) -> rb $ dirApply f (d2, a2) a1
              _ -> Left $ uncmpAtoms a1 a2
           in
            case r of
              Right b -> retVal $ mkAtomTree b
              Left err -> retVal err
        TNDisj dj2 -> regBinLeftDisj op (d2, dj2, tc2) (d1, tc1)
        TNBlock _ -> retVal $ cmpNull a1 t2
        TNList _ -> retVal $ cmpNull a1 t2
        _ -> regBinLeftOther op (d2, tc2) (d1, tc1)
    -- arithmetic operators
    | opv `elem` arithOps -> case treeNode t2 of
        TNAtom ta2 ->
          let
            ri = Right . Int
            rf = Right . Float
            r = case opv of
              AST.Add -> case (a1, ta2) of
                (Int i1, Int i2) -> ri $ dirApply (+) (d1, i1) i2
                (Int i1, Float i2) -> rf $ dirApply (+) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> rf $ dirApply (+) (d1, i1) (fromIntegral i2)
                (String s1, String s2) -> Right . String $ dirApply (<>) (d1, s1) s2
                _ -> Left $ mismatch op a1 (ta2)
              AST.Sub -> case (a1, ta2) of
                (Int i1, Int i2) -> ri $ dirApply (-) (d1, i1) i2
                (Int i1, Float i2) -> rf $ dirApply (-) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> rf $ dirApply (-) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (ta2)
              AST.Mul -> case (a1, ta2) of
                (Int i1, Int i2) -> ri $ dirApply (*) (d1, i1) i2
                (Int i1, Float i2) -> rf $ dirApply (*) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> rf $ dirApply (*) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (ta2)
              AST.Div -> case (a1, ta2) of
                (Int i1, Int i2) -> rf $ dirApply (/) (d1, fromIntegral i1) (fromIntegral i2)
                (Int i1, Float i2) -> rf $ dirApply (/) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> rf $ dirApply (/) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (ta2)
              _ -> Left $ mismatch op a1 (ta2)
           in
            case r of
              Right b -> retVal $ mkAtomTree b
              Left err -> retVal err
        TNDisj dj2 -> regBinLeftDisj op (d2, dj2, tc2) (d1, tc1)
        TNBlock _ -> retVal $ mismatchArith a1 t2
        TNList _ -> retVal $ mismatchArith a1 t2
        _ -> regBinLeftOther op (d2, tc2) (d1, tc1)
    | otherwise -> retVal (mkBottomTree $ printf "operator %s is not supported" (show op))
 where
  cmpOps = [(AST.Equ, (==)), (AST.BinRelOp AST.NE, (/=))]
  arithOps = [AST.Add, AST.Sub, AST.Mul, AST.Div]

  uncmpAtoms :: Atom -> Atom -> Tree
  uncmpAtoms x y = mkBottomTree $ printf "%s and %s are not comparable" (show x) (show y)

  cmpNull :: Atom -> Tree -> Tree
  cmpNull a t =
    if
      -- There is no way for a non-atom to be compared with a non-null atom.
      | a /= Null -> mismatch op a t
      | opv == AST.Equ -> mkAtomTree (Bool False)
      | opv == AST.BinRelOp AST.NE -> mkAtomTree (Bool True)
      | otherwise -> mkBottomTree $ printf "operator %s is not supported" (show op)

  mismatchArith :: (Show a, Show b) => a -> b -> Tree
  mismatchArith = mismatch op

dirApply :: (a -> a -> b) -> (BinOpDirect, a) -> a -> b
dirApply f (di1, i1) i2 = if di1 == L then f i1 i2 else f i2 i1

mismatch :: (Show a, Show b) => AST.BinaryOp -> a -> b -> Tree
mismatch op x y = mkBottomTree $ printf "%s can not be used for %s and %s" (show op) (show x) (show y)

regBinLeftBlock ::
  (ReduceMonad s r m) =>
  AST.BinaryOp ->
  (BinOpDirect, Block, TrCur) ->
  (BinOpDirect, TrCur) ->
  m (Maybe Tree)
regBinLeftBlock op (d1, _, tc1) (d2, tc2) = do
  let
    t1 = tcFocus tc1
    t2 = tcFocus tc2
  case treeNode t2 of
    TNAtom a2 -> regBinLeftAtom op (d2, a2, tc2) (d1, tc1)
    _ -> retVal (mismatch op t1 t2)

regBinLeftDisj ::
  (ReduceMonad s r m) =>
  AST.BinaryOp ->
  (BinOpDirect, Disj, TrCur) ->
  (BinOpDirect, TrCur) ->
  m (Maybe Tree)
regBinLeftDisj op (d1, dj1, tc1) (d2, tc2) = do
  let
    t1 = tcFocus tc1
    t2 = tcFocus tc2
  case dj1 of
    Disj{dsjDefault = Just d} -> regBinDir op (d1, d `setTCFocus` tc1) (d2, tc2)
    _ -> case treeNode t2 of
      TNAtom a2 -> regBinLeftAtom op (d2, a2, tc2) (d1, tc1)
      _ -> retVal (mismatch op t1 t2)

regBinLeftOther ::
  (ReduceMonad s r m) =>
  AST.BinaryOp ->
  (BinOpDirect, TrCur) ->
  (BinOpDirect, TrCur) ->
  m (Maybe Tree)
regBinLeftOther op (d1, tc1) (d2, tc2) = do
  let
    t1 = tcFocus tc1
    t2 = tcFocus tc2
  case (treeNode t1, t2) of
    (TNRefCycle _, _) -> return Nothing
    (TNAtomCnstr c, _) -> do
      naM <- regBinDir op (d1, mkNewTree (TNAtom $ cnsAtom c) `setTCFocus` tc1) (d2, tc2)
      maybe
        (return Nothing)
        ( \na ->
            case treeNode na of
              TNAtom atom -> retVal (mkNewTree (TNAtomCnstr $ updateCnstrAtom atom c))
              _ -> undefined
        )
        naM
    _ -> retVal (mkBottomTree $ mismatchErr t1 t2)
 where
  mismatchErr t1 t2 = printf "values %s and %s cannot be used for %s" (show t1) (show t2) (show op)
