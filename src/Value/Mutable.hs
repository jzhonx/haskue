{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Mutable where

import qualified AST
import Control.DeepSeq (NFData (..))
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import Value.Comprehension
import Value.DisjoinOp
import Value.Interpolation
import Value.Reference
import {-# SOURCE #-} Value.Tree
import Value.UnifyOp

-- | Mutable is a tree node whose value can be changed.
data Mutable
  = RegOp RegularOp
  | Ref Reference
  | Compreh Comprehension
  | DisjOp DisjoinOp
  | UOp UnifyOp
  | Itp Interpolation
  deriving (Generic)

data OpType
  = UnaryOpType AST.UnaryOp
  | BinOpType AST.BinaryOp
  | CloseFunc
  | InvalidOpType
  deriving (Eq, Show, Generic, NFData)

getRefFromMutable :: Mutable -> Maybe Reference
getRefFromMutable mut = case mut of
  Ref ref -> Just ref
  _ -> Nothing

getSFuncFromMutable :: Mutable -> Maybe RegularOp
getSFuncFromMutable mut = case mut of
  RegOp s -> Just s
  _ -> Nothing

requireMutableConcrete :: RegularOp -> Bool
requireMutableConcrete mut = ropName mut `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]

getMutName :: Mutable -> (Tree -> Maybe String) -> String
getMutName (RegOp mut) _ = ropName mut
getMutName (Ref ref) f = "ref_" ++ showRefArg (refArg ref) f
getMutName (Compreh _) _ = "comprehend"
getMutName (DisjOp _) _ = "disjoin"
getMutName (UOp _) _ = "unify"
getMutName (Itp _) _ = "inter"

getMutVal :: Mutable -> Maybe Tree
getMutVal (RegOp mut) = ropValue mut
getMutVal (Ref ref) = refValue ref
getMutVal (Compreh c) = cphValue c
getMutVal (DisjOp d) = djoValue d
getMutVal (UOp u) = ufValue u
getMutVal (Itp i) = itpValue i

setMutVal :: Maybe Tree -> Mutable -> Mutable
setMutVal m (RegOp mut) = RegOp $ mut{ropValue = m}
setMutVal m (Ref ref) = Ref $ ref{refValue = m}
setMutVal m (Compreh c) = Compreh $ c{cphValue = m}
setMutVal m (DisjOp d) = DisjOp $ d{djoValue = m}
setMutVal m (UOp u) = UOp $ u{ufValue = m}
setMutVal m (Itp i) = Itp $ i{itpValue = m}

getMutArgs :: Mutable -> Seq.Seq Tree
getMutArgs (RegOp rop) = ropArgs rop
getMutArgs (Ref ref) = subRefArgs $ refArg ref
getMutArgs (Compreh _) = Seq.empty
getMutArgs (DisjOp d) = fmap dstValue (djoTerms d)
getMutArgs (UOp u) = ufConjuncts u
getMutArgs (Itp itp) = itpExprs itp

updateMutArg :: Int -> Tree -> Mutable -> Mutable
updateMutArg i t (RegOp mut) = RegOp $ mut{ropArgs = Seq.update i t (ropArgs mut)}
updateMutArg i t (Ref ref) = Ref $ ref{refArg = modifySubRefArgs (Seq.update i t) (refArg ref)}
updateMutArg _ _ (Compreh c) = Compreh c
updateMutArg i t (DisjOp d) = DisjOp $ d{djoTerms = Seq.adjust (\term -> term{dstValue = t}) i (djoTerms d)}
updateMutArg i t (UOp u) = UOp $ u{ufConjuncts = Seq.update i t (ufConjuncts u)}
updateMutArg i t (Itp itp) = Itp $ itp{itpExprs = Seq.update i t (itpExprs itp)}

modifyRegMut :: (RegularOp -> RegularOp) -> Mutable -> Mutable
modifyRegMut f (RegOp m) = RegOp $ f m
modifyRegMut _ r = r

-- | RegularOp is a tree node that represents a function.
data RegularOp = RegularOp
  { ropName :: String
  , ropOpType :: OpType
  , ropArgs :: Seq.Seq Tree
  -- ^ Args stores the arguments that may or may not need to be evaluated.
  , ropValue :: Maybe Tree
  -- ^ ropValue stores the non-atom, non-Mutable (isTreeValue true) value.
  }
  deriving (Generic)

emptyRegularOp :: RegularOp
emptyRegularOp =
  RegularOp
    { ropName = ""
    , ropOpType = InvalidOpType
    , ropArgs = Seq.empty
    , ropValue = Nothing
    }

mkUnaryOp :: AST.UnaryOp -> Tree -> Mutable
mkUnaryOp op n =
  RegOp $
    RegularOp
      { ropName = show op
      , ropOpType = UnaryOpType op
      , ropArgs = Seq.fromList [n]
      , ropValue = Nothing
      }

mkBinaryOp :: AST.BinaryOp -> Tree -> Tree -> Mutable
mkBinaryOp op l r =
  RegOp $
    RegularOp
      { ropName = show op
      , ropOpType = BinOpType op
      , ropArgs = Seq.fromList [l, r]
      , ropValue = Nothing
      }

mkDisjoinOp :: Seq.Seq DisjTerm -> Mutable
mkDisjoinOp ts = DisjOp $ DisjoinOp{djoTerms = ts, djoValue = Nothing}

mkUnifyOp :: [Tree] -> Mutable
mkUnifyOp ts = UOp $ emptyUnifyOp{ufConjuncts = Seq.fromList ts}

mkItpMutable :: [IplSeg] -> [Tree] -> Mutable
mkItpMutable segs exprs = Itp $ emptyInterpolation{itpSegs = segs, itpExprs = Seq.fromList exprs}
