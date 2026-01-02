{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Reduce.RegOps where

import qualified AST
import Cursor
import Feature
import Reduce.RMonad (
  RM,
  throwFatal,
 )
import Text.Printf (printf)
import Value

-- * Regular Unary Ops

retVal :: (Monad m) => Val -> m (Maybe Val)
retVal = return . Just

resolveUnaryOp :: (Monad m) => AST.UnaryOp -> Maybe Val -> m (Maybe Val)
resolveUnaryOp op tM = do
  case tM of
    Just (IsBottom _) -> return tM
    Just t | Just a <- rtrAtom t -> case (AST.anVal op, a) of
      (AST.Plus, Int i) -> ia i id
      (AST.Plus, Float i) -> fa i id
      (AST.Minus, Int i) -> ia i negate
      (AST.Minus, Float i) -> fa i negate
      (AST.Not, Bool b) -> retVal (mkAtomVal (Bool (not b)))
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
        (AST.ReMatch, String p) -> retVal (mkBoundsValFromList [BdStrMatch $ BdReMatch p])
        (AST.ReNotMatch, String p) -> retVal (mkBoundsValFromList [BdStrMatch $ BdReNotMatch p])
        _ -> returnErr t
      _ -> returnErr t
    _ -> return Nothing
 where
  returnErr v = retVal $ mkBottomVal $ printf "%s cannot be used for %s" (show v) (show op)

  ia a f = retVal (mkAtomVal (Int $ f a))

  fa a f = retVal (mkAtomVal (Float $ f a))

  mkb b = retVal (mkBoundsValFromList [b])

  mkib uop i = retVal (mkBoundsValFromList [BdNumCmp $ BdNumCmpCons uop (NumInt i)])

  mkfb uop f = retVal (mkBoundsValFromList [BdNumCmp $ BdNumCmpCons uop (NumFloat f)])

-- * Regular Binary Ops

resolveRegBinOp ::
  AST.BinaryOp -> Maybe Val -> Maybe Val -> VCur -> RM (Maybe Val)
resolveRegBinOp op t1M t2M opTC = do
  -- debugInstantOpRM
  --   "resolveRegBinOp"
  --   (printf "reduced args, op: %s, L: %s with R: %s" (show $ AST.anVal op) (show t1M) (show t2M))
  --   (vcAddr opTC)
  resolveRegBinDir op (L, t1M) (R, t2M)

resolveRegBinDir ::
  AST.BinaryOp ->
  (BinOpDirect, Maybe Val) ->
  (BinOpDirect, Maybe Val) ->
  RM (Maybe Val)
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
          | IsFix{} <- t1 -> return Nothing
          | IsFix{} <- t2 -> return Nothing
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

cmp :: Bool -> (BinOpDirect, Maybe Val) -> (BinOpDirect, Maybe Val) -> Maybe Val
cmp cmpEqu (d1, t1M) (d2, t2M) =
  case (t1M, t2M) of
    -- First consider when either of the trees is bottom.
    (Just (IsBottom _), _)
      -- Incomplete is treated as bottom.
      | Nothing <- t2M -> Just $ mkAtomVal (Bool cmpEqu)
      | Just (IsBottom _) <- t2M -> Just $ mkAtomVal (Bool cmpEqu)
      | Just _ <- t2M -> Just $ mkAtomVal (Bool $ not cmpEqu)
    (_, Just (IsBottom _)) -> cmp cmpEqu (d2, t2M) (d1, t1M)
    -- When both trees are not bottom.
    (Just t1, Just t2)
      | Just Null <- rtrAtom t1 -> Just $ cmpNull cmpEqu t2
      | Just Null <- rtrAtom t2 -> Just $ cmpNull cmpEqu t1
      -- When both trees are non-null atoms.
      | Just a1 <- rtrAtom t1
      , Just a2 <- rtrAtom t2 ->
          Just $ mkAtomVal (Bool $ if cmpEqu then a1 == a2 else a1 /= a2)
      -- When both trees are Singular values.
      | Just _ <- rtrNonUnion t1
      , Just _ <- rtrNonUnion t2 ->
          Just $ mkBottomVal $ printf "%s and %s are not comparable" (show t1) (show t2)
    _ -> Nothing

cmpNull :: Bool -> Val -> Val
cmpNull cmpEqu t =
  if
    | Just a <- rtrAtom t -> mkAtomVal (Bool $ if cmpEqu then a == Null else a /= Null)
    -- There is no way for a non-atom to be compared with a non-null atom.
    | otherwise -> mkAtomVal (Bool $ not cmpEqu)

calc :: AST.BinaryOp -> (BinOpDirect, Atom) -> (BinOpDirect, Atom) -> Val
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
      | String s2 <- a2, opv == AST.Add -> mkAtomVal (String $ s1 <> s2)
    _ -> mismatch op a1 a2
 where
  ri = mkAtomVal . Int
  rf = mkAtomVal . Float

  regIntOps = [(AST.Add, (+)), (AST.Sub, (-)), (AST.Mul, (*))]
  floatOps = [(AST.Add, (+)), (AST.Sub, (-)), (AST.Mul, (*)), (AST.Div, (/))]
calc op x@(R, _) y = calc op y x

mismatch :: (Show a, Show b) => AST.BinaryOp -> a -> b -> Val
mismatch op x y = mkBottomVal $ printf "%s can not be used for %s and %s" (show $ AST.anVal op) (show x) (show y)
