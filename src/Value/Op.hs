{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Op where

import Control.DeepSeq (NFData (..))
import Data.Foldable (Foldable (toList))
import qualified Data.Sequence as Seq
import Feature (Feature, mkOpArgFeature)
import GHC.Generics (Generic)
import Syntax.Token as Token
import Value.Comprehension
import Value.DisjoinOp
import Value.Func
import Value.Interpolation
import Value.Reference
import {-# SOURCE #-} Value.Val

data Op
  = RegOp RegularOp
  | Ref Reference
  | VSelect ValueSelect
  | Compreh Comprehension
  | DisjOp DisjoinOp
  | Itp Interpolation
  | FCall FuncCall
  deriving (Generic)

getOpFArgs :: Op -> Seq.Seq (Feature, VNode)
getOpFArgs op =
  let xs = getOpArgs op
   in Seq.fromList $ zip (map mkOpArgFeature [0 ..]) (toList xs)

getOpArgs :: Op -> Seq.Seq VNode
getOpArgs (RegOp rop) = ropArgs rop
getOpArgs (Ref ref) = selectors ref
getOpArgs (VSelect vs) = iSelectors vs
getOpArgs (Compreh c) = fmap getValFromIterClause c.args
getOpArgs (DisjOp d) = fmap dstValue (djoTerms d)
getOpArgs (Itp itp) = itpExprs itp
getOpArgs (FCall f) = fnFrame f

-- | RegularOp is a tree node that represents a function.
data RegularOp = RegularOp
  { ropName :: String
  , ropOpType :: RegOpType
  , ropArgs :: Seq.Seq VNode
  -- ^ Args stores the arguments that may or may not need to be evaluated.
  }
  deriving (Generic)

data RegOpType
  = UnaryOpType TokenType
  | BinOpType TokenType
  | InvalidOpType
  deriving (Eq, Show, Generic, NFData)

emptyRegularOp :: RegularOp
emptyRegularOp =
  RegularOp
    { ropName = ""
    , ropOpType = InvalidOpType
    , ropArgs = Seq.empty
    }

mkUnaryOp :: TokenType -> VNode -> Op
mkUnaryOp op n =
  RegOp $
    RegularOp
      { ropName = show op
      , ropOpType = UnaryOpType op
      , ropArgs = Seq.fromList [n]
      }

mkBinaryOp :: TokenType -> VNode -> VNode -> Op
mkBinaryOp op l r =
  RegOp $
    RegularOp
      { ropName = show op
      , ropOpType = BinOpType op
      , ropArgs = Seq.fromList [l, r]
      }

mkDisjoinOp :: Seq.Seq DisjTerm -> Op
mkDisjoinOp ts = DisjOp $ DisjoinOp{djoTerms = ts}

mkDisjoinOpFromList :: [DisjTerm] -> Op
mkDisjoinOpFromList ts = mkDisjoinOp (Seq.fromList ts)

mkItpSOp :: [IplSeg] -> [VNode] -> Op
mkItpSOp segs exprs = Itp $ emptyInterpolation{itpSegs = segs, itpExprs = Seq.fromList exprs}

showOpType :: Op -> String
showOpType op = case op of
  RegOp _ -> "op"
  Ref _ -> "ref"
  VSelect _ -> "index"
  Compreh _ -> "compreh"
  DisjOp _ -> "disjoin"
  Itp _ -> "inter"
  FCall _ -> "funcall"