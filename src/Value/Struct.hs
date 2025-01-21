{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Value.Struct where

import qualified AST
import Class
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, listToMaybe)
import Env
import Error
import qualified Path
import Value.Bounds

data Struct t = Struct
  { stcID :: Int
  -- ^ The ID is used to identify the struct. It will not be used in the comparison of structs.
  , stcOrdLabels :: [Path.StructTASeg]
  -- ^ stcOrdLabels should only contain StringTASeg labels, meaning it contains all regular fields, hidden fields and
  -- definitions. The length of this list should be equal to the size of the stcSubs map.
  , stcSubs :: Map.Map Path.StructTASeg (StructVal t)
  , stcPatterns :: [StructPattern t]
  , stcPendSubs :: [PendingSElem t]
  , stcClosed :: Bool
  -- ^ The closed flag is used to indicate that the struct is closed, but the fields may not be closed.
  , stcRecurClosed :: Bool
  -- ^ The recur closed flag is used to indicate that the struct is closed and all the fields are closed as well.
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

data StructVal t
  = SField (Field t)
  | SLet (LetBinding t)
  deriving (Show, Eq, Functor)

data Field t = Field
  { ssfField :: t
  , ssfAttr :: LabelAttr
  }
  deriving (Show, Functor)

data LetBinding t = LetBinding
  { lbReferred :: Bool
  , lbValue :: t
  -- ^ The value is needed because if the value is a struct, then the fields of the struct could be referred.
  }
  deriving (Show, Eq, Functor)

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
  deriving (Show, Eq)

data StructElemAdder t
  = Static String (Field t)
  | Dynamic (DynamicField t)
  | Pattern t t
  | Local String t
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
      processSVal :: (Env m, BuildASTExpr t) => (Path.StructTASeg, StructVal t) -> m AST.Declaration
      processSVal (Path.StringTASeg sel, SField sf) = do
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
      processSVal _ = throwErrSt "invalid struct segment or struct value"

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
        stcs <- mapM processSVal [(l, stcSubs s Map.! l) | l <- stcOrdLabels s]
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

-- | Returns both static fields and let bindings.
structStrLabels :: Struct t -> [Path.StructTASeg]
structStrLabels struct = stcOrdLabels struct ++ Map.keys (Map.filter isLocal (stcSubs struct))
 where
  isLocal (SLet _) = True
  isLocal _ = False

structPendIndexes :: Struct t -> [Int]
structPendIndexes s = [0 .. length (stcPendSubs s) - 1]

modifyPendElemVal :: (t -> t) -> PendingSElem t -> PendingSElem t
modifyPendElemVal f pse = case pse of
  DynamicPend dsf -> DynamicPend dsf{dsfValue = f (dsfValue dsf)}
  PatternPend pattern val -> PatternPend pattern (f val)

defaultLabelAttr :: LabelAttr
defaultLabelAttr = LabelAttr SFCRegular True

mergeAttrs :: LabelAttr -> LabelAttr -> LabelAttr
mergeAttrs a1 a2 =
  LabelAttr
    { lbAttrCnstr = min (lbAttrCnstr a1) (lbAttrCnstr a2)
    , lbAttrIsVar = lbAttrIsVar a1 || lbAttrIsVar a2
    }

mkStructFromAdders :: Int -> [StructElemAdder t] -> Struct t
mkStructFromAdders sid as =
  emptyStruct
    { stcID = sid
    , stcOrdLabels = ordLabels
    , stcSubs = Map.fromList vals
    , stcPendSubs = pendings
    }
 where
  ordLabels = [Path.StringTASeg l | Static l _ <- as]
  vals =
    [(Path.StringTASeg s, SField sf) | Static s sf <- as]
      ++ [(Path.StringTASeg s, SLet $ LetBinding{lbReferred = False, lbValue = v}) | Local s v <- as]
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
    { stcID = 0
    , stcOrdLabels = []
    , stcSubs = Map.empty
    , stcPendSubs = []
    , stcPatterns = []
    , stcClosed = False
    , stcRecurClosed = False
    }

addStructField :: Struct t -> String -> Field t -> Struct t
addStructField struct s sf =
  struct
    { stcSubs = Map.insert (Path.StringTASeg s) (SField sf) (stcSubs struct)
    , stcOrdLabels =
        if Path.StringTASeg s `elem` stcOrdLabels struct
          then stcOrdLabels struct
          else stcOrdLabels struct ++ [Path.StringTASeg s]
    }

addStructLocal :: Struct t -> String -> t -> Struct t
addStructLocal struct s t =
  struct
    { stcSubs =
        Map.insert
          (Path.StringTASeg s)
          (SLet $ LetBinding{lbValue = t, lbReferred = False})
          (stcSubs struct)
    }

markLocalReferred :: String -> Struct t -> Struct t
markLocalReferred name struct =
  case lookupStructVal name struct of
    Just (SLet lb) ->
      struct
        { stcSubs = Map.insert seg (SLet lb{lbReferred = True}) (stcSubs struct)
        }
    _ -> struct
 where
  seg = Path.LetTASeg name

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

lookupStructVal :: String -> Struct t -> Maybe (StructVal t)
lookupStructVal name struct =
  listToMaybe $
    catMaybes
      [ Map.lookup (Path.StringTASeg name) (stcSubs struct)
      , -- The original seg could be either StringTASeg or LetTASeg. Since StringTASeg can be used to query both types,
        -- we need to explicitly check for LetTASeg.
        Map.lookup (Path.LetTASeg name) (stcSubs struct)
      ]
