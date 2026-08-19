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
import EvalAddr (TermStep, mkOpArgTermStep)
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

getOpFArgs :: Op -> Seq.Seq (TermStep, VNode)
getOpFArgs op =
  let xs = getOpArgs op
   in Seq.fromList $ zip (map mkOpArgTermStep [0 ..]) (toList xs)

getOpArgs :: Op -> Seq.Seq VNode
getOpArgs (RegOp rop) = ropArgs rop
getOpArgs (Ref ref) = selectors ref
getOpArgs (VSelect vs) = iSelectors vs
getOpArgs (Compreh c) = fmap getValFromIterClause c.args
getOpArgs (DisjOp d) = fmap dstValue (djoTerms d)
getOpArgs (Itp itp) = itpExprs itp
getOpArgs (FCall f) = fnFrame f

{- | Update one of the child nodes exposed by 'getOpArgs'.

Returns 'Nothing' when the index is out of bounds.  Every constructor keeps
its non-argument metadata unchanged.
-}
updateOpArg :: Int -> VNode -> Op -> Maybe Op
updateOpArg index child op = case op of
  RegOp regular -> RegOp . (\args' -> regular{ropArgs = args'}) <$> updateSeq index child regular.ropArgs
  Ref ref -> Ref . (\args' -> ref{selectors = args'}) <$> updateSeq index child ref.selectors
  VSelect select -> VSelect . (\args' -> select{iSelectors = args'}) <$> updateSeq index child select.iSelectors
  Compreh compreh -> do
    argument <- compreh.args Seq.!? index
    let argument' = setValInIterClause child argument
    return $ Compreh compreh{args = Seq.update index argument' compreh.args}
  DisjOp disjoin -> do
    term <- disjoin.djoTerms Seq.!? index
    let term' = term{dstValue = child}
    return $ DisjOp disjoin{djoTerms = Seq.update index term' disjoin.djoTerms}
  Itp interpolation -> Itp . (\args' -> interpolation{itpExprs = args'}) <$> updateSeq index child interpolation.itpExprs
  FCall function -> FCall . (\args' -> function{fnFrame = args'}) <$> updateSeq index child function.fnFrame

updateSeq :: Int -> a -> Seq.Seq a -> Maybe (Seq.Seq a)
updateSeq index child children = do
  _ <- children Seq.!? index
  return $ Seq.update index child children

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

mkItpSOpBytes :: [IplSeg] -> [VNode] -> Op
mkItpSOpBytes segs exprs = Itp $ emptyInterpolation{itpSegs = segs, itpExprs = Seq.fromList exprs, itpIsBytes = True}

showOpType :: Op -> String
showOpType op = case op of
  RegOp _ -> "op"
  Ref _ -> "ref"
  VSelect _ -> "index"
  Compreh _ -> "compreh"
  DisjOp _ -> "disjoin"
  Itp _ -> "inter"
  FCall _ -> "funcall"
