{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Op where

import Control.DeepSeq (NFData (..))
import Data.Foldable (Foldable (toList))
import qualified Data.Sequence as Seq
import Feature (Feature, mkMutArgFeature)
import GHC.Generics (Generic)
import qualified Syntax.AST as AST
import Syntax.Token as Token
import Value.Comprehension
import Value.DisjoinOp
import Value.Interpolation
import Value.Reference
import Value.UnifyOp
import {-# SOURCE #-} Value.Val

-- | SOp is an operation with stateful information.
data SOp = SOp Op OpFrame
  deriving (Generic)

setOpInSOp :: Op -> SOp -> SOp
setOpInSOp op (SOp _ frame) = SOp op frame

data Op
  = RegOp RegularOp
  | Ref Reference
  | Compreh Comprehension
  | DisjOp DisjoinOp
  | UOp UnifyOp
  | Itp Interpolation
  deriving (Generic)

pattern Op :: Op -> SOp
pattern Op op <- SOp op _

data OpFrame = OpFrame {}
  deriving (Generic)

emptyOpFrame :: OpFrame
emptyOpFrame = OpFrame{}

withEmptyOpFrame :: Op -> SOp
withEmptyOpFrame op = SOp op emptyOpFrame

getSOpArgs :: SOp -> Seq.Seq (Feature, Val)
getSOpArgs (SOp op _) =
  let (xs, isUnify) = getOpArgs op
   in Seq.fromList $ zip (map (`mkMutArgFeature` isUnify) [0 ..]) (toList xs)

getOpArgs :: Op -> (Seq.Seq Val, Bool)
getOpArgs (RegOp rop) = (ropArgs rop, False)
getOpArgs (Ref ref) = (subRefArgs $ refArg ref, False)
getOpArgs (Compreh c) = (fmap getValFromIterClause c.args, False)
getOpArgs (DisjOp d) = (fmap dstValue (djoTerms d), False)
getOpArgs (UOp u) = (conjs u, True)
getOpArgs (Itp itp) = (itpExprs itp, False)

updateSOpArg :: Int -> Val -> SOp -> SOp
updateSOpArg i t (SOp op frame) = SOp (updateOpArg i t op) frame

updateOpArg :: Int -> Val -> Op -> Op
updateOpArg i t (RegOp r) = RegOp $ r{ropArgs = Seq.update i t (ropArgs r)}
updateOpArg i t (Ref ref) = Ref $ ref{refArg = modifySubRefArgs (Seq.update i t) (refArg ref)}
updateOpArg i t (Compreh c) = Compreh $ c{args = Seq.adjust (setValInIterClause t) i c.args}
updateOpArg i t (DisjOp d) = DisjOp $ d{djoTerms = Seq.adjust (\term -> term{dstValue = t}) i (djoTerms d)}
updateOpArg i t (UOp u) = UOp $ u{conjs = Seq.update i t (conjs u)}
updateOpArg i t (Itp itp) = Itp $ itp{itpExprs = Seq.update i t (itpExprs itp)}

modifyRegSOp :: (RegularOp -> RegularOp) -> SOp -> SOp
modifyRegSOp f (SOp (RegOp m) frame) = SOp (RegOp $ f m) frame
modifyRegSOp _ r = r

-- | RegularOp is a tree node that represents a function.
data RegularOp = RegularOp
  { ropName :: String
  , ropOpType :: RegOpType
  , ropArgs :: Seq.Seq Val
  -- ^ Args stores the arguments that may or may not need to be evaluated.
  }
  deriving (Generic)

data RegOpType
  = UnaryOpType TokenType
  | BinOpType TokenType
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

mkUnaryOp :: TokenType -> Val -> SOp
mkUnaryOp op n =
  withEmptyOpFrame $
    RegOp $
      RegularOp
        { ropName = show op
        , ropOpType = UnaryOpType op
        , ropArgs = Seq.fromList [n]
        }

mkBinaryOp :: TokenType -> Val -> Val -> SOp
mkBinaryOp op l r =
  withEmptyOpFrame $
    RegOp $
      RegularOp
        { ropName = show op
        , ropOpType = BinOpType op
        , ropArgs = Seq.fromList [l, r]
        }

mkDisjoinOp :: Seq.Seq DisjTerm -> SOp
mkDisjoinOp ts = withEmptyOpFrame $ DisjOp $ DisjoinOp{djoTerms = ts}

mkDisjoinOpFromList :: [DisjTerm] -> SOp
mkDisjoinOpFromList ts = mkDisjoinOp (Seq.fromList ts)

mkUnifyOp :: [Val] -> SOp
mkUnifyOp ts = withEmptyOpFrame $ UOp $ UnifyOp{conjs = Seq.fromList ts, hasEmbeds = False}

mkEmbedUnifyOp :: [Val] -> SOp
mkEmbedUnifyOp ts = withEmptyOpFrame $ UOp $ UnifyOp{conjs = Seq.fromList ts, hasEmbeds = True}

mkItpSOp :: [IplSeg] -> [Val] -> SOp
mkItpSOp segs exprs = withEmptyOpFrame $ Itp $ emptyInterpolation{itpSegs = segs, itpExprs = Seq.fromList exprs}

showOpType :: Op -> String
showOpType op = case op of
  RegOp _ -> "fn"
  Ref _ -> "ref"
  Compreh _ -> "compreh"
  DisjOp _ -> "disjoin"
  UOp _ -> "unify"
  Itp _ -> "inter"