{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
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
data Mutable = Mutable MutOp MutFrame
  deriving (Generic)

setMutOp :: MutOp -> Mutable -> Mutable
setMutOp op (Mutable _ frame) = Mutable op frame

data MutOp
  = RegOp RegularOp
  | Ref Reference
  | Compreh Comprehension
  | DisjOp DisjoinOp
  | UOp UnifyOp
  | Itp Interpolation
  deriving (Generic)

pattern MutOp :: MutOp -> Mutable
pattern MutOp op <- Mutable op _

newtype MutFrame = MutFrame
  { mfValue :: Maybe Tree
  -- ^ Mutable value in general should not be another mutable, especially during notifying a reference to take a
  -- concrete value to update itself.
  }
  deriving (Generic)

emptyMutFrame :: MutFrame
emptyMutFrame = MutFrame{mfValue = Nothing}

withEmptyMutFrame :: MutOp -> Mutable
withEmptyMutFrame op = Mutable op emptyMutFrame

getMutVal :: Mutable -> Maybe Tree
getMutVal (Mutable _ (MutFrame v)) = v

setMutVal :: Maybe Tree -> Mutable -> Mutable
setMutVal m (Mutable (Ref rf) frame) = Mutable (Ref rf{refVers = treeVersion <$> m}) (frame{mfValue = m})
setMutVal m (Mutable op frame) = Mutable op (frame{mfValue = m})

getMutArgs :: Mutable -> Seq.Seq Tree
getMutArgs (Mutable op _) = mutOpArgs op

mutOpArgs :: MutOp -> Seq.Seq Tree
mutOpArgs (RegOp rop) = ropArgs rop
mutOpArgs (Ref ref) = subRefArgs $ refArg ref
mutOpArgs (Compreh c) = fmap getValFromIterClause (cphClauses c)
mutOpArgs (DisjOp d) = fmap dstValue (djoTerms d)
mutOpArgs (UOp u) = ufConjuncts u
mutOpArgs (Itp itp) = itpExprs itp

updateMutArg :: Int -> Tree -> Mutable -> Mutable
updateMutArg i t (Mutable op frame) = Mutable (updateMutOpArg i t op) frame

updateMutOpArg :: Int -> Tree -> MutOp -> MutOp
updateMutOpArg i t (RegOp mut) = RegOp $ mut{ropArgs = Seq.update i t (ropArgs mut)}
updateMutOpArg i t (Ref ref) = Ref $ ref{refArg = modifySubRefArgs (Seq.update i t) (refArg ref)}
updateMutOpArg i t (Compreh c) = Compreh $ c{cphClauses = Seq.adjust (setValInIterClause t) i (cphClauses c)}
updateMutOpArg i t (DisjOp d) = DisjOp $ d{djoTerms = Seq.adjust (\term -> term{dstValue = t}) i (djoTerms d)}
updateMutOpArg i t (UOp u) = UOp $ u{ufConjuncts = Seq.update i t (ufConjuncts u)}
updateMutOpArg i t (Itp itp) = Itp $ itp{itpExprs = Seq.update i t (itpExprs itp)}

modifyRegMut :: (RegularOp -> RegularOp) -> Mutable -> Mutable
modifyRegMut f (Mutable (RegOp m) frame) = Mutable (RegOp $ f m) frame
modifyRegMut _ r = r

-- | RegularOp is a tree node that represents a function.
data RegularOp = RegularOp
  { ropName :: String
  , ropOpType :: RegOpType
  , ropArgs :: Seq.Seq Tree
  -- ^ Args stores the arguments that may or may not need to be evaluated.
  }
  deriving (Generic)

data RegOpType
  = UnaryOpType AST.UnaryOp
  | BinOpType AST.BinaryOp
  | CloseFunc
  | InvalidOpType
  deriving (Eq, Show, Generic, NFData)

emptyRegularOp :: RegularOp
emptyRegularOp =
  RegularOp
    { ropName = ""
    , ropOpType = InvalidOpType
    , ropArgs = Seq.empty
    }

requireMutableConcrete :: RegularOp -> Bool
requireMutableConcrete mut = ropName mut `elem` map show [AST.Add, AST.Sub, AST.Mul, AST.Div]

mkUnaryOp :: AST.UnaryOp -> Tree -> Mutable
mkUnaryOp op n =
  withEmptyMutFrame $
    RegOp $
      RegularOp
        { ropName = show op
        , ropOpType = UnaryOpType op
        , ropArgs = Seq.fromList [n]
        }

mkBinaryOp :: AST.BinaryOp -> Tree -> Tree -> Mutable
mkBinaryOp op l r =
  withEmptyMutFrame $
    RegOp $
      RegularOp
        { ropName = show op
        , ropOpType = BinOpType op
        , ropArgs = Seq.fromList [l, r]
        }

mkDisjoinOp :: Seq.Seq DisjTerm -> Mutable
mkDisjoinOp ts = withEmptyMutFrame $ DisjOp $ DisjoinOp{djoTerms = ts}

mkDisjoinOpFromList :: [DisjTerm] -> Mutable
mkDisjoinOpFromList ts = mkDisjoinOp (Seq.fromList ts)

mkUnifyOp :: [Tree] -> Mutable
mkUnifyOp ts = withEmptyMutFrame $ UOp $ emptyUnifyOp{ufConjuncts = Seq.fromList ts}

mkItpMutable :: [IplSeg] -> [Tree] -> Mutable
mkItpMutable segs exprs = withEmptyMutFrame $ Itp $ emptyInterpolation{itpSegs = segs, itpExprs = Seq.fromList exprs}
