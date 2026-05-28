{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Primitives where

import Control.Monad (foldM)
import qualified Data.ByteString.Char8 as BC
import Data.Foldable (toList)
import qualified Data.Sequence as Seq
import qualified Data.Vector as V
import Feature
import {-# SOURCE #-} Reduce.Core (reduce)
import Reduce.Monad (
  RM,
  throwFatal,
 )
import Reduce.TraceSpan (debugInstStr, emptySpanValue, traceSpanTM)
import Syntax.Token (TokenType)
import qualified Syntax.Token as Token
import Text.Printf (printf)
import Value
import Value.Export.Debug (toTermsRepWithAddr)
import Value.Instances (mapMVectorWAddr)

-- * Regular Unary Ops

resolveUnaryOp :: (Monad m) => TokenType -> Val -> m Val
resolveUnaryOp op t = do
  case t of
    err@(VBottom _) -> return err
    _ | Just a <- rtrAtom t -> case op of
      Token.Plus
        | Int i <- a -> ia i id
        | Float f <- a -> fa f id
      Token.Minus
        | Int i <- a -> ia i negate
        | Float f <- a -> fa f negate
      Token.Exclamation
        | Bool b <- a -> return (VAtom (Bool (not b)))
      Token.NotEqual -> mkb (BdNE a)
      Token.Less
        | Int i <- a -> mkib BdLT i
        | Float f <- a -> mkfb BdLT f
      Token.LessEqual
        | Int i <- a -> mkib BdLE i
        | Float f <- a -> mkfb BdLE f
      Token.Greater
        | Int i <- a -> mkib BdGT i
        | Float f <- a -> mkfb BdGT f
      Token.GreaterEqual
        | Int i <- a -> mkib BdGE i
        | Float f <- a -> mkfb BdGE f
      Token.Match
        | String p <- a -> return (mkBottomValueFromList [BdStrMatch $ BdReMatch p])
      Token.NotMatch
        | String p <- a -> return (mkBottomValueFromList [BdStrMatch $ BdReNotMatch p])
      _ -> returnErr t
    _ -> return VUnknown
 where
  returnErr v = return $ mkBottomVal $ printf "%s cannot be used for %s" (show v) (show op)

  ia a f = return (VAtom (Int $ f a))

  fa a f = return (VAtom (Float $ f a))

  mkb b = return (mkBottomValueFromList [b])

  mkib uop i = return (mkBottomValueFromList [BdNumCmp $ BdNumCmpCons uop (NumInt i)])

  mkfb uop f = return (mkBottomValueFromList [BdNumCmp $ BdNumCmpCons uop (NumFloat f)])

-- * Regular Binary Ops

resolveRegBinOp :: TokenType -> Val -> Val -> ValAddr -> RM Val
resolveRegBinOp op t1 t2 _ = resolveRegBinDir op (L, t1) (R, t2)

resolveRegBinDir ::
  TokenType ->
  (BinOpDirect, Val) ->
  (BinOpDirect, Val) ->
  RM Val
resolveRegBinDir op (d1, t1) (d2, t2) = do
  if
    | op `elem` cmpOps -> return $ cmp (op == Token.Equal) (d1, t1) (d2, t2)
    | op `elem` arithOps -> case (t1, t2) of
        -- First consider when either of the trees is bottom.
        (err@(VBottom _), _) -> return err
        (_, err@(VBottom _)) -> return err
        _
          -- Tops are incomplete.
          | VTop <- t1 -> return VUnknown
          | VTop <- t2 -> return VUnknown
          -- When both trees are atoms.
          | Just a1 <- rtrAtom t1, Just a2 <- rtrAtom t2 -> return $ calc op (d1, a1) (d2, a2)
          -- When both trees are non-union values.
          | Just _ <- rtrNonUnion t1, Just _ <- rtrNonUnion t2 -> return $ mismatch op t1 t2
        _ -> return VUnknown
    | otherwise ->
        throwFatal $
          printf "regular binary op %s is not supported for %s and %s" (show op) (show t1) (show t2)
 where
  cmpOps = [Token.Equal, Token.NotEqual, Token.Less, Token.LessEqual, Token.Greater, Token.GreaterEqual]
  arithOps = [Token.Plus, Token.Minus, Token.Multiply, Token.Divide]

cmp :: Bool -> (BinOpDirect, Val) -> (BinOpDirect, Val) -> Val
cmp cmpEqu (d1, t1) (d2, t2) =
  case (t1, t2) of
    -- First consider when either of the trees is bottom.
    (VBottom _, _)
      -- Incomplete is treated as bottom.
      | VUnknown <- t2 -> VAtom (Bool cmpEqu)
      | VBottom _ <- t2 -> VAtom (Bool cmpEqu)
      | _ <- t2 -> VAtom (Bool $ not cmpEqu)
    (_, VBottom _) -> cmp cmpEqu (d2, t2) (d1, t1)
    -- When both trees are not bottom.
    _
      | Just Null <- rtrAtom t1 -> cmpNull cmpEqu t2
      | Just Null <- rtrAtom t2 -> cmpNull cmpEqu t1
      -- When both trees are non-null atoms.
      | Just a1 <- rtrAtom t1
      , Just a2 <- rtrAtom t2 ->
          VAtom (Bool $ if cmpEqu then a1 == a2 else a1 /= a2)
      -- When both trees are Singular values.
      | Just _ <- rtrNonUnion t1
      , Just _ <- rtrNonUnion t2 ->
          mkBottomVal $ printf "%s and %s are not comparable" (show t1) (show t2)
    _ -> VUnknown

cmpNull :: Bool -> Val -> Val
cmpNull cmpEqu t =
  if
    | Just a <- rtrAtom t -> VAtom (Bool $ if cmpEqu then a == Null else a /= Null)
    -- There is no way for a non-atom to be compared with a non-null atom.
    | otherwise -> VAtom (Bool $ not cmpEqu)

calc :: TokenType -> (BinOpDirect, Atom) -> (BinOpDirect, Atom) -> Val
calc op (L, a1) (_, a2) =
  case a1 of
    Int i1
      | Int i2 <- a2, Just f <- lookup op regIntOps -> ri (f i1 i2)
      | Int i2 <- a2, op == Token.Divide -> rf (fromIntegral i1 / fromIntegral i2)
      | Float f2 <- a2, Just f <- lookup op floatOps -> rf (f (fromIntegral i1) f2)
    Float f1
      | Float f2 <- a2, Just f <- lookup op floatOps -> rf (f f1 f2)
      | Int i2 <- a2, Just f <- lookup op floatOps -> rf (f f1 (fromIntegral i2))
    String s1
      | String s2 <- a2, op == Token.Plus -> VAtom (String $ s1 <> s2)
    _ -> mismatch op a1 a2
 where
  ri = VAtom . Int
  rf = VAtom . Float

  regIntOps = [(Token.Plus, (+)), (Token.Minus, (-)), (Token.Multiply, (*))]
  floatOps = [(Token.Plus, (+)), (Token.Minus, (-)), (Token.Multiply, (*)), (Token.Divide, (/))]
calc op x@(R, _) y = calc op y x

mismatch :: (Show a, Show b) => TokenType -> a -> b -> Val
mismatch op x y = mkBottomVal $ printf "%s can not be used for %s and %s" (show op) (show x) (show y)

reduceList :: List -> ValAddr -> RM Val
reduceList l addr = traceSpanTM "reduceList" addr emptySpanValue do
  updstore <- mapMVectorWAddr reduce mkListStoreIdxFeature addr (store l)
  revR <-
    V.foldM
      ( \acc sub -> do
          debugInstStr "reduceList finalize" addr (show <$> toTermsRepWithAddr addr sub)
          case static $ constraints sub of
            -- If the element is a comprehension and the result of the comprehension is a list, per the spec, we insert
            -- the elements of the list into the list at the current index.
            OpCnstr (Compreh cph) Seq.:<| Seq.Empty
              | cph.isListCompreh
              , Just rList <- rtrList (value sub) ->
                  return $ (reverse . toList $ rList.final) ++ acc
            _ -> return $ sub : acc
      )
      []
      updstore
  let
    r = reverse revR
    finalV = V.fromList r

  -- TODO: faster
  finalV' <- mapMVectorWAddr reduce mkListIdxFeature addr finalV
  return
    ( VList $
        l
          { store = updstore
          , final = finalV'
          }
    )

resolveInterpolation :: Interpolation -> [Val] -> RM Val
resolveInterpolation l args = do
  r <-
    foldM
      ( \accRes seg -> case seg of
          IplSegExpr j -> do
            let r = args !! j
            if
              | Just s <- rtrString r -> return $ (`BC.append` s) <$> accRes
              | Just i <- rtrInt r -> return $ (`BC.append` (BC.pack $ show i)) <$> accRes
              | Just b <- rtrBool r -> return $ (`BC.append` (BC.pack $ show b)) <$> accRes
              | Just f <- rtrFloat r -> return $ (`BC.append` (BC.pack $ show f)) <$> accRes
              | Just _ <- rtrStruct r ->
                  return $
                    Left $
                      mkBottomVal $
                        printf "can not use struct in interpolation: %s" (showValType r)
              | Just _ <- rtrList r ->
                  return $
                    Left $
                      mkBottomVal $
                        printf "can not use list in interpolation: %s" (showValType r)
              | Just _ <- rtrBottom r -> return $ Left r
              | otherwise -> throwFatal $ printf "unsupported interpolation expression: %s" (showValType r)
          IplSegStr s -> return $ (`BC.append` s) <$> accRes
      )
      (Right BC.empty)
      (itpSegs l)
  case r of
    Left err -> return err
    Right res -> return $ VAtom (String res)
