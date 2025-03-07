{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Struct where

import qualified AST
import Class
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, listToMaybe)
import qualified Data.Set as Set
import Exception
import qualified Path

data Struct t = Struct
  { stcID :: Int
  -- ^ The ID is used to identify the struct. It will not be used in the comparison of structs.
  , stcOrdLabels :: [Path.StructTASeg]
  -- ^ stcOrdLabels should only contain StringTASeg labels, meaning it contains all regular fields, hidden fields and
  -- definitions. The length of this list should be equal to the size of the stcSubs map.
  , stcSubs :: Map.Map Path.StructTASeg (StructVal t)
  -- ^ The raws map is used to store the raw values of the static fields, excluding the let bindings.
  , stcCnstrs :: IntMap.IntMap (StructCnstr t)
  , stcPendSubs :: IntMap.IntMap (DynamicField t)
  -- ^ We should not shrink the list as it is a heap list.
  , stcClosed :: Bool
  -- ^ The closed flag is used to indicate that the struct is closed, but the fields may not be closed.
  , stcPerms :: [PermItem]
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
  { ssfValue :: t
  , ssfAttr :: LabelAttr
  , ssfCnstrs :: [Int]
  -- ^ Which constraints are applied to the field.
  , ssfPends :: [Int]
  -- ^ Which dynamic fields are applied to the field.
  , ssfNoStatic :: Bool
  -- ^ Whether the field is created only by dynamic fields.
  }
  deriving (Show, Functor)

data LetBinding t = LetBinding
  { lbReferred :: Bool
  , lbValue :: t
  -- ^ The value is needed because if the value is a struct, then the fields of the struct could be referred.
  }
  deriving (Show, Eq, Functor)

{- | DynamicField would only be evaluated into a field. Definitions (#field) or hidden (_field) fields are not
possible.
-}
data DynamicField t = DynamicField
  { dsfID :: Int
  , dsfAttr :: LabelAttr
  , dsfLabel :: t
  , dsfLabelExpr :: AST.Expression
  , dsfValue :: t
  -- ^ The value is only for the storage purpose. It will not be reduced during reducing pending elements.
  }
  deriving (Show)

{- | StructCnstr is in the form of {[pattern]: value}.

The first element is the pattern, the second element is the value.
-}
data StructCnstr t = StructCnstr
  { scsID :: Int
  , scsPattern :: t
  , scsValue :: t
  -- ^ The value is only for the storage purpose. It is still raw. It will not be reduced during reducing pending
  -- elements.
  }
  deriving (Show)

data StructElemAdder t
  = StaticSAdder String (Field t)
  | DynamicSAdder Int (DynamicField t)
  | CnstrSAdder Int t t
  | LetSAdder String t
  deriving (Show)

data PermItem = PermItem
  { piCnstrs :: Set.Set Int
  , piLabels :: Set.Set Path.StructTASeg
  , piDyns :: Set.Set Int
  , piOpLabels :: Set.Set Path.StructTASeg
  , piOpDyns :: Set.Set Int
  }
  deriving (Show)

instance (Eq t) => Eq (Struct t) where
  (==) s1 s2 =
    stcOrdLabels s1 == stcOrdLabels s2
      && stcSubs s1 == stcSubs s2
      && stcCnstrs s1 == stcCnstrs s2
      && stcPendSubs s1 == stcPendSubs s2
      && stcClosed s1 == stcClosed s2

instance (BuildASTExpr t) => BuildASTExpr (Struct t) where
  buildASTExpr _ _ = throwErrSt "not implemented"

instance (Eq t) => Eq (StructCnstr t) where
  (==) f1 f2 = scsPattern f1 == scsPattern f2 && scsValue f1 == scsValue f2

instance (Eq t) => Eq (DynamicField t) where
  (==) f1 f2 =
    dsfValue f1 == dsfValue f2
      && dsfAttr f1 == dsfAttr f2
      && dsfLabel f1 == dsfLabel f2
      && dsfLabelExpr f1 == dsfLabelExpr f2

instance (Eq t) => Eq (Field t) where
  (==) f1 f2 = ssfValue f1 == ssfValue f2 && ssfAttr f1 == ssfAttr f2

-- | Returns both static fields and let bindings.
structStrLabels :: Struct t -> [Path.StructTASeg]
structStrLabels struct = stcOrdLabels struct ++ Map.keys (Map.filter isLet (stcSubs struct))
 where
  isLet (SLet _) = True
  isLet _ = False

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
    , stcCnstrs = cnstrs
    }
 where
  ordLabels = [Path.StringTASeg l | StaticSAdder l _ <- as]
  vals =
    [(Path.StringTASeg s, SField sf) | StaticSAdder s sf <- as]
      ++ [(Path.StringTASeg s, SLet $ LetBinding{lbReferred = False, lbValue = v}) | LetSAdder s v <- as]
  pendings =
    IntMap.fromList $
      foldr
        ( \x acc ->
            case x of
              DynamicSAdder oid dsf -> (oid, dsf) : acc
              _ -> acc
        )
        []
        as
  cnstrs =
    IntMap.fromList $
      foldr
        ( \x acc ->
            case x of
              CnstrSAdder oid pattern val -> (oid, StructCnstr oid pattern val) : acc
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
    , stcPendSubs = IntMap.empty
    , stcCnstrs = IntMap.empty
    , stcClosed = False
    , stcPerms = []
    }

emptyFieldMker :: t -> LabelAttr -> Field t
emptyFieldMker t a =
  Field
    { ssfValue = t
    , ssfAttr = a
    , ssfCnstrs = []
    , ssfPends = []
    , ssfNoStatic = False
    }

{- | Convert a pending dynamic field to a field.

It marks the pending dynamic field as deleted.
-}
convertPendDyn ::
  Struct t -> String -> Field t -> Struct t
convertPendDyn struct s sf =
  struct
    { stcSubs = Map.insert (Path.StringTASeg s) (SField sf) (stcSubs struct)
    , stcOrdLabels =
        stcOrdLabels struct
          -- TODO: use Map to lookup
          ++ ( if Path.StringTASeg s `elem` stcOrdLabels struct
                then []
                else [Path.StringTASeg s]
             )
             -- , stcPendSubs = IntMap.insert dynIdx Nothing (stcPendSubs struct)
    }

dynToField ::
  DynamicField t ->
  Maybe (StructVal t) ->
  (t -> t -> t) ->
  Field t
dynToField df sfM unifier = case sfM of
  -- Only when the field of the identifier exists, we merge the dynamic field with the existing field.
  -- If the identifier is a let binding, then no need to merge. The limit that there should only be one identifier
  -- in a scope can be ignored.
  Just (SField sf) ->
    -- If the dynamic field is already applied to the field, then we do not apply it again.
    if dsfID df `elem` ssfPends sf
      then sf
      else
        Field
          { ssfValue = unifier (ssfValue sf) (dsfValue df)
          , ssfAttr = mergeAttrs (ssfAttr sf) (dsfAttr df)
          , -- The dynamic field just turns into a regular field. No constraints are applied.
            ssfCnstrs = []
          , ssfPends = ssfPends sf ++ [dsfID df]
          , ssfNoStatic = False
          }
  _ ->
    Field
      { ssfValue = dsfValue df
      , ssfAttr = dsfAttr df
      , -- Same as above.
        ssfCnstrs = []
      , ssfPends = [dsfID df]
      , ssfNoStatic = True
      }

addStructLetBind :: Struct t -> String -> t -> Struct t
addStructLetBind struct s t =
  struct
    { stcSubs =
        Map.insert
          (Path.StringTASeg s)
          (SLet $ LetBinding{lbValue = t, lbReferred = False})
          (stcSubs struct)
    }

markLetBindReferred :: String -> Struct t -> Struct t
markLetBindReferred name struct =
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
hasEmptyFields s = Map.null (stcSubs s) && null (stcPendSubs s)

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

-- | Returns the field value and whether the field is a let binding.
getSubFromSV :: StructVal t -> Maybe (t, Bool)
getSubFromSV (SField f) = Just (ssfValue f, False)
getSubFromSV (SLet lb) = Just (lbValue lb, True)

getFieldFromSV :: StructVal t -> Maybe (Field t)
getFieldFromSV sv = case sv of
  SField f -> Just f
  _ -> Nothing

{- | Update the struct with the given segment and value.

The segment should already exist in the struct.
-}
updateStructSub :: Path.StructTASeg -> StructVal t -> Struct t -> Struct t
updateStructSub seg sub struct =
  struct
    { stcSubs = Map.insert seg sub (stcSubs struct)
    }

{- | Given a struct and the index of a dynamic field, return the permission information to check if the dynamic
field is allowed or whether the dynamic field allows other fields.
-}
getPermInfoForDyn :: Struct t -> Int -> [PermItem]
getPermInfoForDyn struct i =
  foldr
    ( \p acc ->
        if i `Set.member` piDyns p || i `Set.member` piOpDyns p then p : acc else acc
    )
    []
    (stcPerms struct)

{- | Given a struct and the index of a constraint, return the permission information to check whether the constraint
allows other fields.
-}
getPermInfoForPattern :: Struct t -> Int -> [PermItem]
getPermInfoForPattern struct i =
  foldr (\p acc -> if i `Set.member` piCnstrs p then p : acc else acc) [] (stcPerms struct)
