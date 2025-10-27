{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Reduce.RegOps where

import qualified AST
import Cursor
import Path
import Reduce.RMonad (
  ResolveMonad,
  debugInstantOpRM,
  throwFatal,
 )
import Text.Printf (printf)
import Value

-- * Regular Unary Ops

retVal :: (ResolveMonad r s m) => Tree -> m (Maybe Tree)
retVal = return . Just

resolveUnaryOp :: (ResolveMonad r s m) => AST.UnaryOp -> Maybe Tree -> m (Maybe Tree)
resolveUnaryOp op tM = do
  case tM of
    Just (IsBottom _) -> return tM
    Just t | Just a <- rtrAtom t -> case (AST.anVal op, a) of
      (AST.Plus, Int i) -> ia i id
      (AST.Plus, Float i) -> fa i id
      (AST.Minus, Int i) -> ia i negate
      (AST.Minus, Float i) -> fa i negate
      (AST.Not, Bool b) -> retVal (mkAtomTree (Bool (not b)))
      (AST.UnaRelOp uop, _) -> case (uop, a) of
        (AST.NE, x) -> mkb (BdNE x)
        (AST.LT, Int i) -> mkib BdLT i
        (AST.LT, Float f) -> mkfb BdLT f
        (AST.LE, Int i) -> mkib BdLE i
        (AST.LE, Float f) -> mkfb BdLE f
        (AST.GT, Int i) -> mkib BdGT i
        (AST.GT, Float f) -> mkfb BdGT f
        (AST.GE, Int i) -> mkib BdGE i
        (AST.GE, Float f) -> mkfb BdGE f
        (AST.ReMatch, String p) -> retVal (mkBoundsTreeFromList [BdStrMatch $ BdReMatch p])
        (AST.ReNotMatch, String p) -> retVal (mkBoundsTreeFromList [BdStrMatch $ BdReNotMatch p])
        _ -> returnErr t
      _ -> returnErr t
    _ -> return Nothing
 where
  returnErr v = retVal $ mkBottomTree $ printf "%s cannot be used for %s" (show v) (show op)

  ia a f = retVal (mkAtomTree (Int $ f a))

  fa a f = retVal (mkAtomTree (Float $ f a))

  mkb b = retVal (mkBoundsTreeFromList [b])

  mkib uop i = retVal (mkBoundsTreeFromList [BdNumCmp $ BdNumCmpCons uop (NumInt i)])

  mkfb uop f = retVal (mkBoundsTreeFromList [BdNumCmp $ BdNumCmpCons uop (NumFloat f)])

-- * Regular Binary Ops

resolveRegBinOp ::
  (ResolveMonad r s m) => AST.BinaryOp -> Maybe Tree -> Maybe Tree -> TrCur -> m (Maybe Tree)
resolveRegBinOp op t1M t2M opTC = do
  debugInstantOpRM
    "resolveRegBinOp"
    (printf "reduced args, op: %s, L: %s with R: %s" (show $ AST.anVal op) (show t1M) (show t2M))
    (tcAddr opTC)
  resolveRegBinDir op (L, t1M) (R, t2M)

resolveRegBinDir ::
  (ResolveMonad r s m) =>
  AST.BinaryOp ->
  (BinOpDirect, Maybe Tree) ->
  (BinOpDirect, Maybe Tree) ->
  m (Maybe Tree)
resolveRegBinDir op@(AST.anVal -> opv) (d1, t1M) (d2, t2M) = do
  if
    | opv `elem` cmpOps -> return $ cmp (opv == AST.Equ) (d1, t1M) (d2, t2M)
    | opv `elem` arithOps -> case (t1M, t2M) of
        -- First consider when either of the trees is bottom.
        (Just (IsBottom _), _) -> return t1M
        (_, Just (IsBottom _)) -> return t2M
        (Just t1, Just t2)
          -- Tops are incomplete.
          | IsTop <- t1 -> return Nothing
          | IsTop <- t2 -> return Nothing
          | IsRefCycle <- t1 -> return Nothing
          | IsRefCycle <- t2 -> return Nothing
          -- When both trees are atoms.
          | Just a1 <- rtrAtom t1, Just a2 <- rtrAtom t2 -> return $ Just $ calc op (d1, a1) (d2, a2)
          -- When both trees are non-union values.
          | Just _ <- rtrNonUnion t1, Just _ <- rtrNonUnion t2 -> return $ Just $ mismatch op t1 t2
        _ -> return Nothing
    | otherwise ->
        throwFatal $
          printf "regular binary op %s is not supported for %s and %s" (show $ AST.anVal op) (show t1M) (show t2M)
 where
  cmpOps = [AST.Equ, AST.BinRelOp AST.NE]
  arithOps = [AST.Add, AST.Sub, AST.Mul, AST.Div]

cmp :: Bool -> (BinOpDirect, Maybe Tree) -> (BinOpDirect, Maybe Tree) -> Maybe Tree
cmp cmpEqu (d1, t1M) (d2, t2M) =
  case (t1M, t2M) of
    -- First consider when either of the trees is bottom.
    (Just (IsBottom _), _)
      -- Incomplete is treated as bottom.
      | Nothing <- t2M -> Just $ mkAtomTree (Bool cmpEqu)
      | Just (IsBottom _) <- t2M -> Just $ mkAtomTree (Bool cmpEqu)
      | Just _ <- t2M -> Just $ mkAtomTree (Bool $ not cmpEqu)
    (_, Just (IsBottom _)) -> cmp cmpEqu (d2, t2M) (d1, t1M)
    -- When both trees are not bottom.
    (Just t1, Just t2)
      | Just Null <- rtrAtom t1 -> Just $ cmpNull cmpEqu t2
      | Just Null <- rtrAtom t2 -> Just $ cmpNull cmpEqu t1
      -- When both trees are non-null atoms.
      | Just a1 <- rtrAtom t1
      , Just a2 <- rtrAtom t2 ->
          Just $ mkAtomTree (Bool $ if cmpEqu then a1 == a2 else a1 /= a2)
      -- When both trees are Singular values.
      | Just _ <- rtrNonUnion t1
      , Just _ <- rtrNonUnion t2 ->
          Just $ mkBottomTree $ printf "%s and %s are not comparable" (show t1) (show t2)
    _ -> Nothing

cmpNull :: Bool -> Tree -> Tree
cmpNull cmpEqu t =
  if
    | Just a <- rtrAtom t -> mkAtomTree (Bool $ if cmpEqu then a == Null else a /= Null)
    -- There is no way for a non-atom to be compared with a non-null atom.
    | otherwise -> mkAtomTree (Bool $ not cmpEqu)

calc :: AST.BinaryOp -> (BinOpDirect, Atom) -> (BinOpDirect, Atom) -> Tree
calc op@(AST.anVal -> opv) (L, a1) (_, a2) =
  case a1 of
    Int i1
      | Int i2 <- a2, Just f <- lookup opv regIntOps -> ri (f i1 i2)
      | Int i2 <- a2, opv == AST.Div -> rf (fromIntegral i1 / fromIntegral i2)
      | Float f2 <- a2, Just f <- lookup opv floatOps -> rf (f (fromIntegral i1) f2)
    Float f1
      | Float f2 <- a2, Just f <- lookup opv floatOps -> rf (f f1 f2)
      | Int i2 <- a2, Just f <- lookup opv floatOps -> rf (f f1 (fromIntegral i2))
    String s1
      | String s2 <- a2, opv == AST.Add -> mkAtomTree (String $ s1 <> s2)
    _ -> mismatch op a1 a2
 where
  ri = mkAtomTree . Int
  rf = mkAtomTree . Float

  regIntOps = [(AST.Add, (+)), (AST.Sub, (-)), (AST.Mul, (*))]
  floatOps = [(AST.Add, (+)), (AST.Sub, (-)), (AST.Mul, (*)), (AST.Div, (/))]
calc op x@(R, _) y = calc op y x

mismatch :: (Show a, Show b) => AST.BinaryOp -> a -> b -> Tree
mismatch op x y = mkBottomTree $ printf "%s can not be used for %s and %s" (show $ AST.anVal op) (show x) (show y)
