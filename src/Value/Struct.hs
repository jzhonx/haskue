{-# LANGUAGE FlexibleContexts #-}

module Value.Struct where

import qualified AST
import Class
import qualified Data.Map.Strict as Map
import Env
import Error
import qualified Path
import Value.Bounds

data Struct t = Struct
  { stcOrdLabels :: [Path.StructSelector]
  -- ^ stcOrdLabels should only contain StringSelector labels, meaning it contains all regular fields, hidden fields and
  -- definitions. The length of this list should be equal to the size of the stcSubs map.
  , stcSubs :: Map.Map Path.StructSelector (StructVal t)
  , stcPatterns :: [StructPattern t]
  , stcPendSubs :: [PendingSElem t]
  , -- , stcLocals :: Map.Map String (LocalBinding t)
    stcClosed :: Bool
  }

data LabelAttr = LabelAttr
  { lbAttrCnstr :: StructFieldCnstr
  , lbAttrIsVar :: Bool
  }
  deriving (Show, Eq)

data StructFieldCnstr = SFCRegular | SFCRequired | SFCOptional
  deriving (Eq, Ord, Show)

data StructFieldType = SFTRegular | SFTHidden | SFTDefinition | SFTLet
  deriving (Eq, Ord, Show)

data StructVal t
  = SField (Field t)
  | SLocal (LocalBinding t)
  deriving (Show, Eq)

data Field t = Field
  { ssfField :: t
  , ssfAttr :: LabelAttr
  }
  deriving (Show)

{- | DynamicField would only be evaluated into a field. Definitions (#field) or hidden (_field)fields are not
possible.
-}
data DynamicField t = DynamicField
  { dsfAttr :: LabelAttr
  , dsfLabel :: t
  , dsfLabelExpr :: AST.Expression
  , dsfValue :: t
  }
  deriving (Show)

data StructPattern t = StructPattern
  { psfPattern :: Bounds
  , psfValue :: t
  }
  deriving (Show)

{- | LocalPend is needed because the existence of the local binding is dependent on whether its scope has not defined
it.
-}
data PendingSElem t
  = DynamicPend (DynamicField t)
  | PatternPend t t
  | LocalPend String t
  deriving (Show, Eq)

data StructElemAdder t
  = Static String (Field t)
  | Dynamic (DynamicField t)
  | Pattern t t
  | Local String t
  deriving (Show)

data LocalBinding t = LocalBinding
  { lbReferred :: Bool
  , lbValue :: t
  -- ^ The value is needed because if the value is a struct, then the fields of the struct could be referred.
  }
  deriving (Show, Eq)

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
      processSVal :: (Env m, BuildASTExpr t) => (Path.StructSelector, StructVal t) -> m AST.Declaration
      processSVal (Path.StringSelector sel, SField sf) = do
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
      processSVal _ = throwErrSt "invalid struct selector or struct value"

      processDynField :: (Env m, BuildASTExpr t) => DynamicField t -> m AST.Declaration
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
        stcs <- mapM processSVal [(l, stcSubs s Map.! l) | l <- structStrLabels s]
        dyns <-
          sequence $
            foldr
              ( \x acc -> case x of
                  DynamicPend dsf -> processDynField dsf : acc
                  _ -> acc
              )
              []
              (stcPendSubs s)
        return $ AST.litCons $ AST.StructLit (stcs ++ dyns)

instance (Eq t) => Eq (StructPattern t) where
  (==) f1 f2 = psfPattern f1 == psfPattern f2 && psfValue f1 == psfValue f2

instance (Eq t) => Eq (DynamicField t) where
  (==) f1 f2 =
    dsfValue f1 == dsfValue f2
      && dsfAttr f1 == dsfAttr f2
      && dsfLabel f1 == dsfLabel f2
      && dsfLabelExpr f1 == dsfLabelExpr f2

instance (Eq t) => Eq (Field t) where
  (==) f1 f2 = ssfField f1 == ssfField f2 && ssfAttr f1 == ssfAttr f2

structStrLabels :: Struct t -> [Path.StructSelector]
structStrLabels = filter (\x -> Path.viewStructSelector x == 0) . stcOrdLabels

structPendIndexes :: Struct t -> [Int]
structPendIndexes s = [0 .. length (stcPendSubs s) - 1]

modifyPendElemVal :: (t -> t) -> PendingSElem t -> PendingSElem t
modifyPendElemVal f pse = case pse of
  DynamicPend dsf -> DynamicPend dsf{dsfValue = f (dsfValue dsf)}
  PatternPend pattern val -> PatternPend pattern (f val)
  LocalPend s val -> LocalPend s (f val)

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
  emptyStruct
    { stcOrdLabels = ordLabels
    , stcSubs = Map.fromList vals
    , stcPendSubs = pendings
    }
 where
  ordLabels = [Path.StringSelector l | Static l _ <- as]
  vals =
    [(Path.StringSelector s, SField sf) | Static s sf <- as]
      ++ [(Path.StringSelector s, SLocal $ LocalBinding{lbReferred = False, lbValue = v}) | Local s v <- as]
  pendings =
    foldr
      ( \x acc ->
          case x of
            Dynamic dsf -> DynamicPend dsf : acc
            Pattern pattern val -> PatternPend pattern val : acc
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
    , -- , stcLocals = Map.empty
      stcClosed = False
    }

addStructField :: Struct t -> String -> Field t -> Struct t
addStructField struct s sf =
  struct
    { stcSubs = Map.insert (Path.StringSelector s) (SField sf) (stcSubs struct)
    , stcOrdLabels =
        if Path.StringSelector s `elem` stcOrdLabels struct
          then stcOrdLabels struct
          else stcOrdLabels struct ++ [Path.StringSelector s]
    }

addStructLocal :: Struct t -> String -> t -> Struct t
addStructLocal struct s t =
  struct
    { stcSubs =
        Map.insert
          (Path.StringSelector s)
          (SLocal $ LocalBinding{lbValue = t, lbReferred = False})
          (stcSubs struct)
    }

-- -- | Update the value of a static field in the struct.
-- updateStatic :: (MonadError String m) => Struct t -> String -> t -> m (Struct t)
-- updateStatic struct s t =
--   case Map.lookup (Path.StringSelector s) (stcSubs struct) of
--     Just sf -> return $ addStructField struct s (sf{ssfField = t})
--     Nothing -> throwErrSt "the static field is not found"

-- | Determines whether the struct has empty fields, including both static and dynamic fields.
hasEmptyFields :: Struct t -> Bool
hasEmptyFields s = Map.null (stcSubs s) && not (any isDynamicField (stcPendSubs s))
 where
  isDynamicField (DynamicPend _) = True
  isDynamicField _ = False

getFieldType :: String -> Maybe StructFieldType
getFieldType [] = Nothing
getFieldType ident
  | head ident == '#' || length ident >= 2 && take 2 ident == "_#" = Just SFTDefinition
  | head ident == '_' = Just SFTHidden
  | otherwise = Just SFTRegular
