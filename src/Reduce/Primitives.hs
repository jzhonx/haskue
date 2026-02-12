{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Primitives where

import Control.Monad (foldM)
import Cursor
import Data.Foldable (toList)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Vector as V
import Feature
import {-# SOURCE #-} Reduce.Core (reduce)
import Reduce.Monad (
  RM,
  getTMVal,
  inSubTM,
  setTMVN,
  throwFatal,
 )
import Reduce.TraceSpan (traceSpanArgsTM)
import StringIndex (ShowWTIndexer (..))
import Syntax.Token (TokenType)
import qualified Syntax.Token as Token
import Text.Printf (printf)
import Value

-- * Regular Unary Ops

retVal :: (Monad m) => Val -> m (Maybe Val)
retVal = return . Just

resolveUnaryOp :: (Monad m) => TokenType -> Maybe Val -> m (Maybe Val)
resolveUnaryOp op tM = do
  case tM of
    Just (IsBottom _) -> return tM
    Just t | Just a <- rtrAtom t -> case op of
      Token.Plus
        | Int i <- a -> ia i id
        | Float f <- a -> fa f id
      Token.Minus
        | Int i <- a -> ia i negate
        | Float f <- a -> fa f negate
      Token.Exclamation
        | Bool b <- a -> retVal (mkAtomVal (Bool (not b)))
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
        | String p <- a -> retVal (mkBoundsValFromList [BdStrMatch $ BdReMatch p])
      Token.NotMatch
        | String p <- a -> retVal (mkBoundsValFromList [BdStrMatch $ BdReNotMatch p])
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

resolveRegBinOp :: TokenType -> Maybe Val -> Maybe Val -> VCur -> RM (Maybe Val)
resolveRegBinOp op t1M t2M _ =
  traceSpanArgsTM
    "resolveRegBinOp"
    ( const $ do
        t1MT <- mapM tshow t1M
        t2MT <- mapM tshow t2M
        return $ printf "op: %s, t1: %s, t2: %s" (show op) (show t1MT) (show t2MT)
    )
    $ resolveRegBinDir op (L, t1M) (R, t2M)

resolveRegBinDir ::
  TokenType ->
  (BinOpDirect, Maybe Val) ->
  (BinOpDirect, Maybe Val) ->
  RM (Maybe Val)
resolveRegBinDir op (d1, t1M) (d2, t2M) = do
  if
    | op `elem` cmpOps -> return $ cmp (op == Token.Equal) (d1, t1M) (d2, t2M)
    | op `elem` arithOps -> case (t1M, t2M) of
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
          printf "regular binary op %s is not supported for %s and %s" (show op) (show t1M) (show t2M)
 where
  cmpOps = [Token.Equal, Token.NotEqual, Token.Less, Token.LessEqual, Token.Greater, Token.GreaterEqual]
  arithOps = [Token.Plus, Token.Minus, Token.Multiply, Token.Divide]

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
      | String s2 <- a2, op == Token.Plus -> mkAtomVal (String $ s1 <> s2)
    _ -> mismatch op a1 a2
 where
  ri = mkAtomVal . Int
  rf = mkAtomVal . Float

  regIntOps = [(Token.Plus, (+)), (Token.Minus, (-)), (Token.Multiply, (*))]
  floatOps = [(Token.Plus, (+)), (Token.Minus, (-)), (Token.Multiply, (*)), (Token.Divide, (/))]
calc op x@(R, _) y = calc op y x

mismatch :: (Show a, Show b) => TokenType -> a -> b -> Val
mismatch op x y = mkBottomVal $ printf "%s can not be used for %s and %s" (show op) (show x) (show y)

reduceList :: List -> RM ()
reduceList l = do
  r <-
    foldM
      ( \acc (i, origElem) -> do
          r <- inSubTM (mkListStoreIdxFeature i) (reduce >> getTMVal)
          case origElem of
            -- If the element is a comprehension and the result of the comprehension is a list, per the spec, we insert
            -- the elements of the list into the list at the current index.
            IsValMutable (Op (Compreh cph))
              | cph.isListCompreh
              , Just rList <- rtrList r ->
                  return $ acc ++ toList rList.final
            _ -> return $ acc ++ [r]
      )
      []
      (zip [0 ..] (toList l.store))
  t <- getTMVal
  case t of
    IsList lst -> do
      let newList = lst{final = V.fromList r}
      setTMVN (VNList newList)
    _ -> return ()

-- | Closes a struct when the tree has struct.
resolveCloseFunc :: [Val] -> VCur -> RM (Maybe Val)
resolveCloseFunc args _
  | length args /= 1 = throwFatal $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      let arg = head args
      return $ Just $ closeTree arg

-- | Close a struct when the tree has struct.
closeTree :: Val -> Val
closeTree a =
  case valNode a of
    VNStruct s -> setVN (VNStruct $ s{stcClosed = True}) a
    VNDisj dj ->
      let
        ds = Seq.mapWithIndex (\_ t -> closeTree t) (dsjDisjuncts dj)
       in
        setVN (VNDisj (dj{dsjDisjuncts = ds})) a
    -- TODO: SOp should be closed.
    -- TNMutable _ -> throwFatal "TODO"
    _ -> mkBottomVal $ printf "cannot use %s as struct in argument 1 to close" (show a)

resolveInterpolation :: Interpolation -> [Val] -> RM (Maybe Val)
resolveInterpolation l args = do
  r <-
    foldM
      ( \accRes seg -> case seg of
          IplSegExpr j -> do
            let r = args !! j
            if
              | Just s <- rtrString r -> return $ (`T.append` s) <$> accRes
              | Just i <- rtrInt r -> return $ (`T.append` (T.pack $ show i)) <$> accRes
              | Just b <- rtrBool r -> return $ (`T.append` (T.pack $ show b)) <$> accRes
              | Just f <- rtrFloat r -> return $ (`T.append` (T.pack $ show f)) <$> accRes
              | Just _ <- rtrStruct r ->
                  return $
                    Left $
                      mkBottomVal $
                        printf "can not use struct in interpolation: %s" (showValSymbol r)
              | Just _ <- rtrList r ->
                  return $
                    Left $
                      mkBottomVal $
                        printf "can not use list in interpolation: %s" (showValSymbol r)
              | otherwise -> throwFatal $ printf "unsupported interpolation expression: %s" (showValSymbol r)
          IplSegStr s -> return $ (`T.append` s) <$> accRes
      )
      (Right T.empty)
      (itpSegs l)
  case r of
    Left err -> return $ Just err
    Right res -> return $ Just $ mkAtomVal (String res)
