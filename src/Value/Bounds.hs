{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Value.Bounds where

import qualified AST
import Control.DeepSeq (NFData (..))
import qualified Data.Text as T
import GHC.Generics (Generic)
import Value.Atom (Atom)

newtype Bounds = Bounds {bdsList :: [Bound]}
  deriving (Show, Eq, Generic, NFData)

data Bound
  = BdNE Atom
  | BdNumCmp BdNumCmp
  | BdStrMatch BdStrMatch
  | BdType BdType
  | BdIsAtom Atom -- helper type
  deriving (Show, Eq, Generic, NFData)

data BdNumCmpOp
  = BdLT
  | BdLE
  | BdGT
  | BdGE
  deriving (Eq, Enum, Ord, Generic, NFData)

data Number = NumInt Integer | NumFloat Double
  deriving (Show, Eq, Generic, NFData)

data BdNumCmp = BdNumCmpCons BdNumCmpOp Number
  deriving (Show, Eq, Generic, NFData)

data BdStrMatch
  = BdReMatch T.Text
  | BdReNotMatch T.Text
  deriving (Show, Eq, Generic, NFData)

data BdType
  = BdBool
  | BdInt
  | BdFloat
  | BdNumber
  | BdString
  deriving (Eq, Enum, Bounded, Generic, NFData)

instance Show BdNumCmpOp where
  show o = show $ case o of
    BdLT -> AST.LT
    BdLE -> AST.LE
    BdGT -> AST.GT
    BdGE -> AST.GE

instance Show BdType where
  show BdBool = "bool"
  show BdInt = "int"
  show BdFloat = "float"
  show BdNumber = "number"
  show BdString = "string"

instance Ord Number where
  compare (NumInt i1) (NumInt i2) = compare i1 i2
  compare (NumFloat f1) (NumFloat f2) = compare f1 f2
  compare (NumInt i) (NumFloat f) = compare (fromIntegral i) f
  compare (NumFloat f) (NumInt i) = compare f (fromIntegral i)
