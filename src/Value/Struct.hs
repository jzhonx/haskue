{-# LANGUAGE FlexibleContexts #-}

module Value.Struct where

import qualified AST
import Control.Monad.Except (throwError)
import qualified Data.Map.Strict as Map
import qualified Path
import Value.Bounds
import Value.Class
import Value.Env

data Struct t = Struct
  { stcOrdLabels :: [Path.StructSelector] -- Should only contain string labels.
  , stcSubs :: Map.Map Path.StructSelector (StaticStructField t)
  , stcPatterns :: [PatternStructField t]
  , stcPendSubs :: [PendingStructElem t]
  }

data LabelAttr = LabelAttr
  { lbAttrType :: StructLabelType
  , lbAttrIsVar :: Bool
  }
  deriving (Show, Eq)

data StructLabelType = SLRegular | SLRequired | SLOptional
  deriving (Eq, Ord, Enum, Show)

data StaticStructField t = StaticStructField
  { ssfField :: t
  , ssfAttr :: LabelAttr
  }
  deriving (Show)

data DynamicStructField t = DynamicStructField
  { -- For pattern constraint, this is omitted.
    dsfAttr :: LabelAttr
  , dsfLabel :: t
  , dsfLabelExpr :: AST.Expression
  , dsfValue :: t
  }
  deriving (Show)

data PatternStructField t = PatternStructField
  { psfPattern :: Bounds
  , psfValue :: t
  }
  deriving (Show)

data PendingStructElem t
  = DynamicField (DynamicStructField t)
  | PatternField t t
  deriving (Show, Eq)

data StructElemAdder t
  = Static Path.StructSelector (StaticStructField t)
  | Dynamic (DynamicStructField t)
  | Pattern t t
  deriving (Show)

instance (Eq t) => Eq (Struct t) where
  (==) s1 s2 =
    stcOrdLabels s1 == stcOrdLabels s2
      && stcSubs s1 == stcSubs s2
      && stcPatterns s1 == stcPatterns s2
      && stcPendSubs s1 == stcPendSubs s2

instance (BuildASTExpr t) => BuildASTExpr (Struct t) where
  -- Patterns are not included in the AST.
  buildASTExpr concrete s =
    let
      processStaticField :: (Env m c, BuildASTExpr t) => (Path.StructSelector, StaticStructField t) -> m AST.Declaration
      processStaticField (label, sf) = case label of
        Path.StringSelector sel -> do
          e <- buildASTExpr concrete (ssfField sf)
          return $
            AST.FieldDecl $
              AST.Field
                [ labelCons (ssfAttr sf) $
                    if lbAttrIsVar (ssfAttr sf)
                      then AST.LabelID sel
                      else AST.LabelString sel
                ]
                e
        _ -> throwError "Only StringSelector is allowed in static fields."

      processDynField :: (Env m c, BuildASTExpr t) => DynamicStructField t -> m AST.Declaration
      processDynField sf = do
        e <- buildASTExpr concrete (dsfValue sf)
        return $
          AST.FieldDecl $
            AST.Field
              [ labelCons (dsfAttr sf) $ AST.LabelNameExpr (dsfLabelExpr sf)
              ]
              e

      labelCons :: LabelAttr -> AST.LabelName -> AST.Label
      labelCons attr ln =
        AST.Label $
          AST.LabelName
            ln
            ( case lbAttrType attr of
                SLRegular -> AST.RegularLabel
                SLRequired -> AST.RequiredLabel
                SLOptional -> AST.OptionalLabel
            )
     in
      do
        stcs <- sequence [processStaticField (l, stcSubs s Map.! l) | l <- structStaticLabels s]
        dyns <-
          sequence $
            foldr
              ( \x acc -> case x of
                  DynamicField dsf -> processDynField dsf : acc
                  _ -> acc
              )
              []
              (stcPendSubs s)
        return $ AST.litCons $ AST.StructLit (stcs ++ dyns)

instance (Eq t) => Eq (PatternStructField t) where
  (==) f1 f2 = psfPattern f1 == psfPattern f2 && psfValue f1 == psfValue f2

instance (Eq t) => Eq (DynamicStructField t) where
  (==) f1 f2 =
    dsfValue f1 == dsfValue f2
      && dsfAttr f1 == dsfAttr f2
      && dsfLabel f1 == dsfLabel f2
      && dsfLabelExpr f1 == dsfLabelExpr f2

instance (Eq t) => Eq (StaticStructField t) where
  (==) f1 f2 = ssfField f1 == ssfField f2 && ssfAttr f1 == ssfAttr f2

structStaticLabels :: Struct t -> [Path.StructSelector]
structStaticLabels = filter (\x -> Path.viewStructSelector x == 0) . stcOrdLabels

structPendIndexes :: Struct t -> [Int]
structPendIndexes s = [0 .. length (stcPendSubs s) - 1]

modifyPSEValue :: (t -> t) -> PendingStructElem t -> PendingStructElem t
modifyPSEValue f pse = case pse of
  DynamicField dsf -> DynamicField dsf{dsfValue = f (dsfValue dsf)}
  PatternField pattern val -> PatternField pattern (f val)

defaultLabelAttr :: LabelAttr
defaultLabelAttr = LabelAttr SLRegular True

mergeAttrs :: LabelAttr -> LabelAttr -> LabelAttr
mergeAttrs a1 a2 =
  LabelAttr
    { lbAttrType = min (lbAttrType a1) (lbAttrType a2)
    , lbAttrIsVar = lbAttrIsVar a1 || lbAttrIsVar a2
    }

mkStructFromAdders :: [StructElemAdder t] -> Struct t
mkStructFromAdders as =
  Struct
    { stcOrdLabels = ordLabels
    , stcSubs = Map.fromList statics
    , stcPatterns = []
    , stcPendSubs = pendings
    }
 where
  ordLabels = [l | Static l _ <- as]
  statics = [(s, sf) | Static s sf <- as]
  pendings =
    foldr
      ( \x acc ->
          case x of
            Dynamic dsf -> DynamicField dsf : acc
            Pattern pattern val -> PatternField pattern val : acc
            _ -> acc
      )
      []
      as

emptyStruct :: Struct t
emptyStruct =
  Struct
    { stcOrdLabels = []
    , stcSubs = Map.empty
    , stcPendSubs = []
    , stcPatterns = []
    }
