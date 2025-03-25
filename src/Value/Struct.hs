{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Struct where

import qualified AST
import Common (BuildASTExpr (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Exception (throwErrSt)

data Struct t = Struct
  { stcID :: Int
  -- ^ The ID is used to identify the struct. It will not be used in the comparison of structs.
  , stcOrdLabels :: [String]
  -- ^ stcOrdLabels should only contain string labels, meaning it contains all regular fields, hidden fields and
  -- definitions. It should not contain let bindings.
  , stcFields :: Map.Map String (Field t)
  -- ^ It is the fields, excluding the let bindings.
  , stcLets :: Map.Map String (LetBinding t)
  -- ^ Let bindings are read-only. They are not reduced.
  , stcCnstrs :: IntMap.IntMap (StructCnstr t)
  , stcPendSubs :: IntMap.IntMap (DynamicField t)
  -- ^ We should not shrink the list as it is a heap list.
  , stcEmbeds :: IntMap.IntMap t
  -- ^ The embedded structs are not reduced.
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
  deriving (Show, Eq)

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
  -- ^ The value is only for the storage purpose.
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
  | EmbedSAdder Int t
  deriving (Show)

data PermItem = PermItem
  { piCnstrs :: Set.Set Int
  , piLabels :: Set.Set String
  , piDyns :: Set.Set Int
  , piOpLabels :: Set.Set String
  , piOpDyns :: Set.Set Int
  }
  deriving (Show)

instance (Eq t) => Eq (Struct t) where
  (==) s1 s2 =
    stcOrdLabels s1 == stcOrdLabels s2
      && stcFields s1 == stcFields s2
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

-- | Returns keys of both static fields and let bindings.
structFieldsAndLets :: Struct t -> [String]
structFieldsAndLets struct = stcOrdLabels struct ++ Map.keys (stcLets struct)

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
    , stcFields = Map.fromList vals
    , stcLets = Map.fromList lets
    , stcPendSubs = pendings
    , stcCnstrs = cnstrs
    }
 where
  ordLabels = [l | StaticSAdder l _ <- as]
  vals = [(s, sf) | StaticSAdder s sf <- as]
  lets = [(s, LetBinding{lbReferred = False, lbValue = v}) | LetSAdder s v <- as]
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
    , stcFields = Map.empty
    , stcLets = Map.empty
    , stcPendSubs = IntMap.empty
    , stcCnstrs = IntMap.empty
    , stcEmbeds = IntMap.empty
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
    { stcFields = Map.insert s sf (stcFields struct)
    , stcOrdLabels =
        stcOrdLabels struct
          -- TODO: use Map to lookup
          ++ ( if s `elem` stcOrdLabels struct
                then []
                else [s]
             )
             -- , stcPendSubs = IntMap.insert dynIdx Nothing (stcPendSubs struct)
    }

dynToField ::
  DynamicField t ->
  Maybe (Field t) ->
  (t -> t -> t) ->
  Field t
dynToField df sfM unifier = case sfM of
  -- Only when the field of the identifier exists, we merge the dynamic field with the existing field.
  -- If the identifier is a let binding, then no need to merge. The limit that there should only be one identifier
  -- in a scope can be ignored.
  Just sf ->
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
  -- No existing field, so we just turn the dynamic field into a field.
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
    { stcLets =
        Map.insert
          s
          (LetBinding{lbValue = t, lbReferred = False})
          (stcLets struct)
    }

markLetBindReferred :: String -> Struct t -> Struct t
markLetBindReferred name struct =
  case Map.lookup name lets of
    Just lb ->
      struct
        { stcLets = Map.insert name (lb{lbReferred = True}) lets
        }
    _ -> struct
 where
  lets = stcLets struct

-- | Determines whether the struct has empty fields, including both static and dynamic fields.
hasEmptyFields :: Struct t -> Bool
hasEmptyFields s = Map.null (stcFields s) && null (stcPendSubs s)

getFieldType :: String -> Maybe StructFieldType
getFieldType [] = Nothing
getFieldType ident
  | head ident == '#' || length ident >= 2 && take 2 ident == "_#" = Just SFTDefinition
  | head ident == '_' = Just SFTHidden
  | otherwise = Just SFTRegular

{- | Look up the struct value in the struct.

The name could be in both the fields and let bindings, or either.
-}
lookupStructVal :: String -> Struct t -> [StructVal t]
lookupStructVal name struct =
  catMaybes
    [ SField <$> Map.lookup name (stcFields struct)
    , SLet <$> Map.lookup name (stcLets struct)
    ]

lookupStructField :: String -> Struct t -> Maybe (Field t)
lookupStructField name struct = Map.lookup name (stcFields struct)

lookupStructLet :: String -> Struct t -> Maybe (LetBinding t)
lookupStructLet name struct = Map.lookup name (stcLets struct)

-- | Returns the field value and whether the field is a let binding.
getSubFromSV :: StructVal t -> Maybe (t, Bool)
getSubFromSV (SField f) = Just (ssfValue f, False)
getSubFromSV (SLet lb) = Just (lbValue lb, True)

getFieldFromSV :: StructVal t -> Maybe (Field t)
getFieldFromSV sv = case sv of
  SField f -> Just f
  _ -> Nothing

{- | Update the struct with the given label name and field.

The segment should already exist in the struct.
-}
updateStructField :: String -> Field t -> Struct t -> Struct t
updateStructField name sub struct =
  struct
    { stcFields = Map.insert name sub (stcFields struct)
    }

updateStructLet :: String -> LetBinding t -> Struct t -> Struct t
updateStructLet name sub struct =
  struct
    { stcLets = Map.insert name sub (stcLets struct)
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
