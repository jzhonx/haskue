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
import Feature (Feature, mkOpArgFeature)
import GHC.Generics (Generic)
import Syntax.Token as Token
import Value.Comprehension
import Value.DisjoinOp
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
  deriving (Generic)

getOpFArgs :: Op -> Seq.Seq (Feature, VNode)
getOpFArgs op =
  let xs = getOpArgs op
   in Seq.fromList $ zip (map mkOpArgFeature [0 ..]) (toList xs)

getOpArgs :: Op -> Seq.Seq VNode
getOpArgs (RegOp rop) = ropArgs rop
getOpArgs (Ref ref) = selectors ref
getOpArgs (VSelect (ValueSelect _ _ xs)) = xs
getOpArgs (Compreh c) = fmap getValFromIterClause c.args
getOpArgs (DisjOp d) = fmap dstValue (djoTerms d)
getOpArgs (Itp itp) = itpExprs itp

-- updateOpArg :: Int -> VNode -> Op -> Op
-- updateOpArg i t (RegOp r) = RegOp $ r{ropArgs = Seq.update i t (ropArgs r)}
-- updateOpArg i t (Ref ref) = Ref $ mapRefSels (Seq.update i t) ref
-- updateOpArg i t (VSelect (ValueSelect bvid b xs)) = VSelect $ ValueSelect bvid b $ Seq.update i t xs
-- updateOpArg i t (Compreh c) = Compreh $ c{args = Seq.adjust (setValInIterClause t) i c.args}
-- updateOpArg i t (DisjOp d) = DisjOp $ d{djoTerms = Seq.adjust (\term -> term{dstValue = t}) i (djoTerms d)}
-- updateOpArg i t (Itp itp) = Itp $ itp{itpExprs = Seq.update i t (itpExprs itp)}

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

-- modifyRefInSOp :: (Reference -> Reference) -> SOp -> SOp
-- modifyRefInSOp f (SOp (Ref r) frame) = SOp (Ref $ f r) frame
-- modifyRefInSOp _ r = r

showOpType :: Op -> String
showOpType op = case op of
  RegOp _ -> "fn"
  Ref _ -> "ref"
  VSelect _ -> "index"
  Compreh _ -> "compreh"
  DisjOp _ -> "disjoin"
  Itp _ -> "inter"