{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Atom where

import qualified AST
import Control.DeepSeq (NFData (..))
import qualified Data.Text as T
import GHC.Generics (Generic)

data Atom
  = String T.Text
  | Int Integer
  | Float Double
  | Bool Bool
  | Null
  deriving (Ord, Generic, NFData)

-- | Show is only used for debugging.
instance Show Atom where
  show (String s) = show s
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

aToLiteral :: Atom -> AST.Literal
aToLiteral a = pure $ case a of
  String s -> AST.anVal $ AST.strToLit s
  Int i -> AST.IntLit i
  Float f -> AST.FloatLit f
  Bool b -> AST.BoolLit b
  Null -> AST.NullLit
