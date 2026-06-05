{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Op where

import qualified Data.ByteString.Char8 as BC
import qualified Data.Map.Strict as Map
import Feature
import Reduce.Monad (
  RM,
  throwFatal,
 )
import Reduce.Unification (reMatch, reNotMatch)
import StringIndex (ShowWTIndexer (..))
import Syntax.AST (getNodeLoc)
import Syntax.Token (TokenType, toByteString)
import qualified Syntax.Token as Token
import Text.Printf (printf)
import Value

-- * Regular Unary Ops

resolveUnaryOp :: TokenType -> VNode -> RM Val
resolveUnaryOp op vn = do
  case vn.value of
    err@(VBottom _) -> return err
    _ | Just a <- rtrAtom vn.value -> case op of
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
      _ -> returnErr vn.value
    _ -> return VUnknown
 where
  returnErr v = return $ mkBottomVal $ printf "%s cannot be used for %s" (show v) (show op)

  ia a f = return (VAtom (Int $ f a))

  fa a f = return (VAtom (Float $ f a))

  mkb b = return (mkBottomValueFromList [b])

  mkib uop i = return (mkBottomValueFromList [BdNumCmp $ BdNumCmpCons uop (NumInt i)])

  mkfb uop f = return (mkBottomValueFromList [BdNumCmp $ BdNumCmpCons uop (NumFloat f)])

-- * Regular Binary Ops

resolveRegBinOp :: TokenType -> VNode -> VNode -> ValAddr -> RM Val
resolveRegBinOp op vn1 vn2 _ = resolveRegBinDir op (L, vn1) (R, vn2)

resolveRegBinDir :: TokenType -> (BinOpDirect, VNode) -> (BinOpDirect, VNode) -> RM Val
resolveRegBinDir op (d1, vn1@VNode{value = v1}) (d2, vn2@VNode{value = v2}) = do
  if
    | Just f <- Map.lookup op cmpOpsMap -> f (d1, vn1) (d2, vn2)
    | op `elem` matchOps -> case (v1, v2) of
        -- First consider when either of the trees is bottom.
        (err@(VBottom _), _) -> return err
        (_, err@(VBottom _)) -> return err
        _
          -- Tops are incomplete.
          | VTop <- v1 -> return VUnknown
          | VTop <- v2 -> return VUnknown
          -- When both trees are atoms.
          | Just (String s) <- rtrAtom v1
          , Just (String p) <- rtrAtom v2 ->
              return $ VAtom $ Bool $ if op == Token.Match then reMatch s p else reNotMatch s p
          -- When both trees are non-union values.
          | Just _ <- rtrNonUnion v1, Just _ <- rtrNonUnion v2 -> return $ mismatch op vn1 vn2
        _ -> return VUnknown
    | op `elem` arithOps -> case (v1, v2) of
        -- First consider when either of the trees is bottom.
        (err@(VBottom _), _) -> return err
        (_, err@(VBottom _)) -> return err
        _
          -- Tops are incomplete.
          | VTop <- v1 -> return VUnknown
          | VTop <- v2 -> return VUnknown
          -- When both trees are atoms.
          | Just a1 <- rtrAtom v1, Just a2 <- rtrAtom v2 -> return $ calc op (d1, a1) (d2, a2)
          -- When both trees are non-union values.
          | Just _ <- rtrNonUnion v1, Just _ <- rtrNonUnion v2 -> return $ mismatch op vn1 vn2
        _ -> return VUnknown
    | otherwise ->
        throwFatal $
          printf "regular binary op %s is not supported for %s and %s" (show op) (show vn1) (show vn2)
 where
  matchOps = [Token.Match, Token.NotMatch]
  arithOps = [Token.Plus, Token.Minus, Token.Multiply, Token.Divide]

cmpOpsMap :: Map.Map TokenType ((BinOpDirect, VNode) -> (BinOpDirect, VNode) -> RM Val)
cmpOpsMap =
  Map.fromList
    [ (Token.Equal, cmpEqu)
    ,
      ( Token.NotEqual
      , \x y -> do
          res <- cmpEqu x y
          case res of
            VAtom (Bool b) -> reta (Bool (not b))
            _ -> return res
      )
    , (Token.Less, cmpLess Token.Less)
    , (Token.LessEqual, cmpLessEqual Token.LessEqual)
    ,
      ( Token.Greater
      , \x y -> do
          res <- cmpLessEqual Token.Greater x y
          case res of
            VAtom (Bool b) -> reta (Bool (not b))
            _ -> return res
      )
    ,
      ( Token.GreaterEqual
      , \x y -> do
          res <- cmpLess Token.GreaterEqual x y
          case res of
            VAtom (Bool b) -> reta (Bool (not b))
            _ -> return res
      )
    ]

cmpEqu :: (BinOpDirect, VNode) -> (BinOpDirect, VNode) -> RM Val
cmpEqu (d1, vn1@VNode{value = v1}) (d2, vn2@VNode{value = v2}) =
  case (v1, v2) of
    -- First consider when either of the values is bottom.
    (VBottom _, _)
      -- Incomplete is treated as bottom.
      | VUnknown <- v2 -> reta (Bool True)
      | VBottom _ <- v2 -> reta (Bool True)
      | otherwise -> reta (Bool False)
    (_, VBottom _) -> cmpEqu (d2, vn2) (d1, vn1)
    -- When both trees are not bottom.
    _
      | Just Null <- rtrAtom v1 -> cmpNull vn2
      | Just Null <- rtrAtom v2 -> cmpNull vn1
      -- When both trees are non-null atoms.
      | Just a1 <- rtrAtom v1, Just a2 <- rtrAtom v2 -> reta (Bool $ a1 == a2)
      -- When both trees are non union values.
      | Just a1 <- rtrNonUnion v1, Just a2 <- rtrNonUnion v2 -> reta (Bool $ a1 == a2)
    _ -> return VUnknown

reta :: Atom -> RM Val
reta = return . VAtom

cmpNull :: VNode -> RM Val
cmpNull vn =
  if
    | Just a <- rtrAtom vn.value -> return $ VAtom (Bool $ a == Null)
    -- There is no way for a non-atom to be compared with a non-null atom.
    | otherwise -> return $ VAtom (Bool False)

cmpLess :: TokenType -> (BinOpDirect, VNode) -> (BinOpDirect, VNode) -> RM Val
cmpLess tktyp (_, vn1@VNode{value = v1}) (_, vn2@VNode{value = v2})
  | Just _ <- rtrBottom v1 = return v1
  | Just _ <- rtrBottom v2 = return v2
  | Just a1 <- rtrAtom v1
  , Just a2 <- rtrAtom v2 =
      case (a1, a2) of
        (Int i1, Int i2) -> reta (Bool $ i1 < i2)
        (Float f1, Float f2) -> reta (Bool $ f1 < f2)
        (Int i1, Float f2) -> reta (Bool $ fromIntegral i1 < f2)
        (Float f1, Int i2) -> reta (Bool $ f1 < fromIntegral i2)
        (String s1, String s2) -> reta (Bool $ s1 < s2)
        _ -> invalidCmpOperandsErr tktyp vn1 vn2
  | otherwise = invalidCmpOperandsErr tktyp vn1 vn2

cmpLessEqual :: TokenType -> (BinOpDirect, VNode) -> (BinOpDirect, VNode) -> RM Val
cmpLessEqual tktyp (_, vn1@VNode{value = v1}) (_, vn2@VNode{value = v2})
  | Just _ <- rtrBottom v1 = return v1
  | Just _ <- rtrBottom v2 = return v2
  | Just a1 <- rtrAtom v1
  , Just a2 <- rtrAtom v2 =
      case (a1, a2) of
        (Int i1, Int i2) -> reta (Bool $ i1 <= i2)
        (Float f1, Float f2) -> reta (Bool $ f1 <= f2)
        (Int i1, Float f2) -> reta (Bool $ fromIntegral i1 <= f2)
        (Float f1, Int i2) -> reta (Bool $ f1 <= fromIntegral i2)
        (String s1, String s2) -> reta (Bool $ s1 <= s2)
        _ -> invalidCmpOperandsErr tktyp vn1 vn2
  | otherwise = invalidCmpOperandsErr tktyp vn1 vn2

invalidCmpOperandsErr :: TokenType -> VNode -> VNode -> RM Val
invalidCmpOperandsErr tktyp vn1@VNode{value = v1} vn2@VNode{value = v2} = do
  v1T <- tshow v1
  v2T <- tshow v2
  v1Type <- showValueType v1
  v2Type <- showValueType v2
  return $
    mkBottomVal $
      printf
        "invalid operands %s and %s to '%s' (type %s and %s):\n\t%s\n\t%s"
        v1T
        v2T
        (BC.unpack $ toByteString tktyp)
        v1Type
        v2Type
        (show $ getNodeLoc vn1)
        (show $ getNodeLoc vn2)

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
