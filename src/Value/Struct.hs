{-# LANGUAGE FlexibleContexts #-}

module Value.Struct where

import qualified AST
import Class
import Control.Monad.Except (MonadError)
import qualified Data.Map.Strict as Map
import Env
import Error
import qualified Path
import Value.Bounds

data Struct t = Struct
  { stcOrdLabels :: [Path.StructSelector]
  -- ^ Should only contain StringSelector labels, meaning it contains all regular fields, hidden fields and
  -- definitions. The length of this list should be equal to the size of the stcSubs map.
  , stcSubs :: Map.Map Path.StructSelector (StaticStructField t)
  , stcPatterns :: [PatternStructField t]
  , stcPendSubs :: [PendingStructElem t]
  , stcClosed :: Bool
  }

data LabelAttr = LabelAttr
  { lbAttrCnstr :: StructFieldCnstr
  , lbAttrIsVar :: Bool
  }
  deriving (Show, Eq)

data StructFieldCnstr = SFCRegular | SFCRequired | SFCOptional
  deriving (Eq, Ord, Show)

data StructFieldType = SFTRegular | SFTHidden | SFTDefinition
  deriving (Eq, Ord, Show)

data StaticStructField t = StaticStructField
  { ssfField :: t
  , ssfAttr :: LabelAttr
  }
  deriving (Show)

{- | DynamicStructField would only be evaluated into a field. Definitions (#field) or hidden (_field)fields are not
possible.
-}
data DynamicStructField t = DynamicStructField
  { dsfAttr :: LabelAttr
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
      && stcClosed s1 == stcClosed s2

instance (BuildASTExpr t) => BuildASTExpr (Struct t) where
  -- Patterns are not included in the AST.
  buildASTExpr concrete s =
    let
      processStaticField :: (Env m, BuildASTExpr t) => (Path.StructSelector, StaticStructField t) -> m AST.Declaration
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
        _ -> throwErrSt "Only StringSelector is allowed in static fields."

      processDynField :: (Env m, BuildASTExpr t) => DynamicStructField t -> m AST.Declaration
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
            ( case lbAttrCnstr attr of
                SFCRegular -> AST.RegularLabel
                SFCRequired -> AST.RequiredLabel
                SFCOptional -> AST.OptionalLabel
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
defaultLabelAttr = LabelAttr SFCRegular True

mergeAttrs :: LabelAttr -> LabelAttr -> LabelAttr
mergeAttrs a1 a2 =
  LabelAttr
    { lbAttrCnstr = min (lbAttrCnstr a1) (lbAttrCnstr a2)
    , lbAttrIsVar = lbAttrIsVar a1 || lbAttrIsVar a2
    }

mkStructFromAdders :: [StructElemAdder t] -> Struct t
mkStructFromAdders as =
  Struct
    { stcOrdLabels = ordLabels
    , stcSubs = Map.fromList statics
    , stcPatterns = []
    , stcPendSubs = pendings
    , stcClosed = False
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
    , stcClosed = False
    }

addStatic :: Struct t -> String -> StaticStructField t -> Struct t
addStatic struct s sf =
  struct
    { stcSubs = Map.insert (Path.StringSelector s) sf (stcSubs struct)
    , stcOrdLabels =
        if Path.StringSelector s `elem` stcOrdLabels struct
          then stcOrdLabels struct
          else stcOrdLabels struct ++ [Path.StringSelector s]
    }

-- | Update the value of a static field in the struct.
updateStatic :: (MonadError String m) => Struct t -> String -> t -> m (Struct t)
updateStatic struct s t =
  case Map.lookup (Path.StringSelector s) (stcSubs struct) of
    Just sf -> return $ addStatic struct s (sf{ssfField = t})
    Nothing -> throwErrSt "the static field is not found"

-- | Determines whether the struct has empty fields, including both static and dynamic fields.
hasEmptyFields :: Struct t -> Bool
hasEmptyFields s = Map.null (stcSubs s) && not (any isDynamicField (stcPendSubs s))
 where
  isDynamicField (DynamicField _) = True
  isDynamicField _ = False

getFieldType :: String -> Maybe StructFieldType
getFieldType [] = Nothing
getFieldType ident
  | head ident == '#' || length ident >= 2 && take 2 ident == "_#" = Just SFTDefinition
  | head ident == '_' = Just SFTHidden
  | otherwise = Just SFTRegular
