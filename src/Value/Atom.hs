{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}

module Value.Atom where

import qualified AST
import Common (BuildASTExpr (..), Env)

data Atom
  = String String
  | Int Integer
  | Float Double
  | Bool Bool
  | Null
  deriving (Ord)

-- | Show is only used for debugging.
instance Show Atom where
  show (String s) = s
  show (Int i) = show i
  show (Float f) = show f
  show (Bool b) = show b
  show Null = "null"

instance Eq Atom where
  (==) (String s1) (String s2) = s1 == s2
  (==) (Int i1) (Int i2) = i1 == i2
  (==) (Int i1) (Float i2) = fromIntegral i1 == i2
  (==) (Float i1) (Int i2) = i1 == fromIntegral i2
  (==) (Float f1) (Float f2) = f1 == f2
  (==) (Bool b1) (Bool b2) = b1 == b2
  (==) Null Null = True
  (==) _ _ = False

instance BuildASTExpr Atom where
  buildASTExpr :: (Env r s m) => Bool -> Atom -> m AST.Expression
  buildASTExpr _ a = return $ (AST.litCons . aToLiteral) a

aToLiteral :: Atom -> AST.Literal
aToLiteral a = pure $ case a of
  String s -> AST.wpVal $ AST.strToLit s
  Int i -> AST.IntLit i
  Float f -> AST.FloatLit f
  Bool b -> AST.BoolLit b
  Null -> AST.NullLit

newtype AtomV = AtomV
  { amvAtom :: Atom
  }

instance Show AtomV where
  show (AtomV v) = show v

instance Eq AtomV where
  (==) (AtomV v1) (AtomV v2) = v1 == v2

instance BuildASTExpr AtomV where
  buildASTExpr c (AtomV v) = buildASTExpr c v

getStringFromAtom :: Atom -> Maybe String
getStringFromAtom a = case a of
  String s -> Just s
  _ -> Nothing

getStringFromAtomV :: AtomV -> Maybe String
getStringFromAtomV (AtomV a) = getStringFromAtom a

getIntFromAtom :: Atom -> Maybe Int
getIntFromAtom a = case a of
  Int i -> Just (fromIntegral i)
  _ -> Nothing

getIntFromAtomV :: AtomV -> Maybe Int
getIntFromAtomV (AtomV a) = getIntFromAtom a
