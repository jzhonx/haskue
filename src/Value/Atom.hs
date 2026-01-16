{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Atom where

import Control.DeepSeq (NFData (..))
import Data.Aeson (ToJSON (..))
import qualified Data.Aeson
import qualified Data.ByteString.Char8 as BC
import qualified Data.Text as T
import GHC.Generics (Generic)
import Syntax.AST (textToMultiLineLiteral, textToSimpleStrLiteral)
import qualified Syntax.AST as AST
import Syntax.Token (mkToken)
import qualified Syntax.Token as Token

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

instance ToJSON Atom where
  toJSON (String s) = toJSON s
  toJSON (Int i) = toJSON i
  toJSON (Float f) = toJSON f
  toJSON (Bool b) = toJSON b
  toJSON Null = Data.Aeson.Null

aToLiteral :: Atom -> AST.Literal
aToLiteral a = case a of
  String s -> let f = if T.elem '\n' s then textToMultiLineLiteral else textToSimpleStrLiteral in f s
  Int i -> AST.LitBasic $ AST.IntLit (mkToken Token.Int (BC.pack (show i)))
  Float f -> AST.LitBasic $ AST.FloatLit (mkToken Token.Float (BC.pack (show f)))
  Bool b -> AST.LitBasic $ AST.BoolLit (mkToken Token.Bool (if b then "true" else "false"))
  Null -> AST.LitBasic $ AST.NullLit (mkToken Token.Null "null")
