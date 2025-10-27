{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Block where

import Control.DeepSeq (NFData (..))
import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import qualified Data.Text as T
import GHC.Generics (Generic)
import Value.Reference (RefIdent (..))
import {-# SOURCE #-} Value.Tree

-- | A struct has concrete field labels and constraints that have no mutable patterns.
data Struct = Struct
  { stcID :: !Int
  , stcClosed :: !Bool
  -- ^ The closed flag is used to indicate that the struct is closed, but the fields may not be closed, if directly
  -- referenced. Should be directly copied from the block.
  , stcFields :: Map.Map T.Text Field
  -- ^ It is the fields.
  , stcBindings :: Map.Map RefIdent Binding
  , stcDynFields :: IntMap.IntMap DynamicField
  , stcCnstrs :: IntMap.IntMap StructCnstr
  , stcStaticFieldBases :: Map.Map T.Text Field
  -- ^ The un-evaluated fields that defined in this block. They shold be copied to the struct when building the struct.
  , stcOrdLabels :: [StructFieldLabel]
  , stcIsConcrete :: !Bool
  , stcEmbedVal :: Maybe Tree
  , stcPermErr :: Maybe Tree
  , stcPerms :: [PermItem]
  }
  deriving (Generic)

data StructFieldLabel = StructStaticFieldLabel T.Text | StructDynFieldOID !Int
  deriving (Eq, Generic, NFData, Ord)

instance Show StructFieldLabel where
  show (StructStaticFieldLabel n) = T.unpack n
  show (StructDynFieldOID i) = show i

data LabelAttr = LabelAttr
  { lbAttrCnstr :: StructFieldCnstr
  , lbAttrIsIdent :: !Bool
  }
  deriving (Show, Eq, Generic, NFData)

defaultLabelAttr :: LabelAttr
defaultLabelAttr =
  LabelAttr
    { lbAttrCnstr = SFCRegular
    , lbAttrIsIdent = True
    }

data StructFieldCnstr = SFCRegular | SFCRequired | SFCOptional
  deriving (Eq, Ord, Show, Generic, NFData)

data StructFieldType = SFTRegular | SFTHidden | SFTDefinition
  deriving (Eq, Ord, Show)

data StructStubVal
  = StructStubField Field
  | StructStubLet Tree

data Field = Field
  { ssfValue :: Tree
  , ssfAttr :: LabelAttr
  , ssfObjects :: Set.Set Int
  -- ^ A set of object IDs that have been unified with base raw value.
  }
  deriving (Generic)

mkdefaultField :: Tree -> Field
mkdefaultField t =
  Field
    { ssfValue = t
    , ssfAttr = defaultLabelAttr
    , ssfObjects = Set.empty
    }

{- | DynamicField would only be evaluated into a field. Definitions (#field) or hidden (_field) fields are not
possible.
-}
data DynamicField = DynamicField
  { dsfID :: !Int
  , dsfAttr :: LabelAttr
  , dsfLabel :: Tree
  , dsfLabelIsInterp :: !Bool
  -- ^ Whether the label is an interpolated label.
  , dsfValue :: Tree
  -- ^ The value is only for the storage purpose. It will not be reduced during reducing dynamic fields.
  }
  deriving (Generic)

{- | StructCnstr is in the form of [pattern]: value.

According to sepc,
> A pattern constraint, denoted [pattern]: value, defines a pattern, which is a value of type string, and a value to
> unify with fields whose label unifies with the pattern.
-}
data StructCnstr = StructCnstr
  { scsID :: !Int
  , scsPattern :: Tree
  , scsValue :: Tree
  }
  deriving (Generic)

{- | Permission item stores permission information for the static fields and dynamic fields of a struct.

The permission information is used to check if the opposite labels and dynamic fields are allowed when the base struct
is closed and neither of the structs is embedded.

Because structs can be merged and constraints can be changed, we need to store the permission information of the
original struct.
-}
data PermItem = PermItem
  { piCnstrs :: Set.Set Int
  , piLabels :: Set.Set StructFieldLabel
  , piOpLabels :: Set.Set StructFieldLabel
  }
  deriving (Eq, Generic, NFData)

instance Show PermItem where
  show p =
    "PermItem{"
      ++ "cnstrs="
      ++ show (Set.toList $ piCnstrs p)
      ++ ",labels="
      ++ show (Set.toList $ piLabels p)
      ++ ",opLabels="
      ++ show (Set.toList $ piOpLabels p)
      ++ "}"

mergeAttrs :: LabelAttr -> LabelAttr -> LabelAttr
mergeAttrs a1 a2 =
  LabelAttr
    { lbAttrCnstr = min (lbAttrCnstr a1) (lbAttrCnstr a2)
    , lbAttrIsIdent = lbAttrIsIdent a1 || lbAttrIsIdent a2
    }

emptyStruct :: Struct
emptyStruct =
  Struct
    { stcID = 0
    , stcFields = Map.empty
    , stcBindings = Map.empty
    , stcStaticFieldBases = Map.empty
    , stcDynFields = IntMap.empty
    , stcCnstrs = IntMap.empty
    , stcClosed = False
    , stcOrdLabels = []
    , stcIsConcrete = False
    , stcEmbedVal = Nothing
    , stcPermErr = Nothing
    , stcPerms = []
    }

updateFieldValue :: Tree -> Field -> Field
updateFieldValue t field = field{ssfValue = t}

staticFieldMker :: Tree -> LabelAttr -> Field
staticFieldMker t a =
  Field
    { ssfValue = t
    , ssfAttr = a
    , ssfObjects = Set.empty
    }

dynToField :: DynamicField -> Maybe Field -> (Tree -> Tree -> Tree) -> Field
dynToField df sfM unifier = case sfM of
  -- Only when the field of the identifier exists, we merge the dynamic field with the existing field.
  -- If the identifier is a let binding, then no need to merge. The limit that there should only be one identifier
  -- in a scope can be ignored.
  Just sf ->
    -- If the dynamic field is already applied to the field, then we do not apply it again.
    if dsfID df `Set.member` ssfObjects sf
      then sf
      else
        sf
          { ssfValue = unifier (ssfValue sf) (dsfValue df)
          , ssfAttr = mergeAttrs (ssfAttr sf) (dsfAttr df)
          , ssfObjects = Set.insert (dsfID df) (ssfObjects sf)
          }
  -- No existing field, so we just turn the dynamic field into a field.
  _ ->
    Field
      { ssfValue = dsfValue df
      , ssfAttr = dsfAttr df
      , ssfObjects = Set.fromList [dsfID df]
      }

lookupStructLet :: RefIdent -> Struct -> Maybe Tree
lookupStructLet name s = value <$> Map.lookup name (stcBindings s)

{- | Insert a new let binding into the block.

Caller should ensure that the name is not already in the block.
-}
insertStructLet :: T.Text -> Tree -> Struct -> Struct
insertStructLet s t struct =
  struct
    { stcBindings = Map.insert (RefIdent s) (Binding t False) (stcBindings struct)
    }

-- | Determines whether the block has empty fields, including both static and dynamic fields.
hasEmptyFields :: Struct -> Bool
hasEmptyFields struct = Map.null (stcStaticFieldBases struct) && null (stcDynFields struct)

getFieldType :: String -> Maybe StructFieldType
getFieldType [] = Nothing
getFieldType ident
  | head ident == '#' || length ident >= 2 && take 2 ident == "_#" = Just SFTDefinition
  | head ident == '_' = Just SFTHidden
  | otherwise = Just SFTRegular

{- | Look up the stub value in the block.

The name could be in both the fields and let bindings, or either.
-}
lookupStructStubVal :: T.Text -> Struct -> [StructStubVal]
lookupStructStubVal name struct =
  catMaybes
    [ StructStubField <$> Map.lookup name (stcStaticFieldBases struct)
    , StructStubLet . value <$> Map.lookup (RefIdent name) struct.stcBindings
    ]

lookupStructDynField :: Int -> Struct -> Maybe DynamicField
lookupStructDynField oid struct = IntMap.lookup oid (stcDynFields struct)

lookupStructField :: T.Text -> Struct -> Maybe Field
lookupStructField name struct = Map.lookup name (stcFields struct)

lookupStructStaticFieldBase :: T.Text -> Struct -> Maybe Field
lookupStructStaticFieldBase name struct = Map.lookup name (stcStaticFieldBases struct)

lookupStructIdentField :: T.Text -> Struct -> Maybe Field
lookupStructIdentField name struct =
  case Map.lookup name (stcFields struct) of
    Just field ->
      if lbAttrIsIdent (ssfAttr field)
        then Just field
        else Nothing
    Nothing -> Nothing

-- | Update the struct with the given label name and field.
updateStructField :: T.Text -> Field -> Struct -> Struct
updateStructField name sub struct = struct{stcFields = Map.insert name sub (stcFields struct)}

updateStructWithFields :: [(T.Text, Field)] -> Struct -> Struct
updateStructWithFields fields struct = foldr (\(k, field) acc -> updateStructField k field acc) struct fields

-- | Remove the static fields by names from the struct.
removeStructFieldsByNames :: [T.Text] -> Struct -> Struct
removeStructFieldsByNames names struct = struct{stcFields = foldr Map.delete (stcFields struct) names}

updateStructCnstrByID :: Int -> Bool -> Tree -> Struct -> Struct
updateStructCnstrByID cid isPattern sub struct =
  struct
    { stcCnstrs =
        IntMap.update
          ( \sc ->
              Just
                ( if isPattern
                    then sc{scsPattern = sub}
                    else sc{scsValue = sub}
                )
          )
          cid
          (stcCnstrs struct)
    }

updateStructDynFieldByID :: Int -> Bool -> Tree -> Struct -> Struct
updateStructDynFieldByID oid isLabel sub struct =
  struct
    { stcDynFields =
        IntMap.update
          ( \df ->
              Just
                ( if isLabel
                    then df{dsfLabel = sub}
                    else df{dsfValue = sub}
                )
          )
          oid
          (stcDynFields struct)
    }

updateStructStaticFieldBase :: T.Text -> Tree -> Struct -> Struct
updateStructStaticFieldBase name sub struct =
  struct{stcStaticFieldBases = Map.update (\sf -> Just sf{ssfValue = sub}) name (stcStaticFieldBases struct)}

updateStructLetBinding :: RefIdent -> Tree -> Struct -> Struct
updateStructLetBinding name sub struct =
  struct
    { stcBindings = Map.update (\b -> Just (b{value = sub})) name (stcBindings struct)
    }

buildStructOrdLabels :: (Tree -> Maybe T.Text) -> Struct -> Maybe [T.Text]
buildStructOrdLabels rtrString struct =
  let
    r :: Maybe ([T.Text], Set.Set T.Text)
    r =
      foldM
        ( \(revAcc, seen) blkLabel -> do
            newLabel <- case blkLabel of
              StructStaticFieldLabel n -> return n
              StructDynFieldOID i -> do
                dsf <- lookupStructDynField i struct
                rtrString (dsfLabel dsf)
            return $
              if Set.member newLabel seen
                then (revAcc, seen)
                else (newLabel : revAcc, Set.insert newLabel seen)
        )
        ([], Set.empty)
        (stcOrdLabels struct)
   in
    reverse . fst <$> r

{- | Update the stub static field that has already existed with the given name.

Also update the field.

It is used in parsing the AST to a struct.
-}
updateStubAndField :: T.Text -> Field -> Struct -> Struct
updateStubAndField name field struct =
  struct
    { stcStaticFieldBases = Map.insert name field (stcStaticFieldBases struct)
    , stcFields = Map.insert name field (stcFields struct)
    }

-- | Insert a new static field into the stub struct.
insertNewStubAndField :: T.Text -> Field -> Struct -> Struct
insertNewStubAndField name field struct =
  struct
    { stcStaticFieldBases = Map.insert name field (stcStaticFieldBases struct)
    , stcOrdLabels = stcOrdLabels struct ++ [StructStaticFieldLabel name]
    , stcFields = Map.insert name field (stcFields struct)
    }

-- | Insert a new dynamic field into the block stub struct.
insertStructNewDynField :: Int -> DynamicField -> Struct -> Struct
insertStructNewDynField oid df struct =
  struct
    { stcDynFields = IntMap.insert oid df (stcDynFields struct)
    , stcOrdLabels = stcOrdLabels struct ++ [StructDynFieldOID oid]
    }

-- | Insert a new constraint into the block stub struct.
insertStructNewCnstr :: Int -> Tree -> Tree -> Struct -> Struct
insertStructNewCnstr cid pat val struct =
  struct{stcCnstrs = IntMap.insert cid (StructCnstr cid pat val) (stcCnstrs struct)}

{- | Deduplicate the block labels by removing the static that have the same label or dynamic field that is evaluated to
the same label.
-}
dedupStructFieldLabels ::
  (Tree -> Maybe T.Text) -> IntMap.IntMap DynamicField -> [StructFieldLabel] -> [StructFieldLabel]
dedupStructFieldLabels rtrString dynFields labels =
  reverse . fst $ foldl go ([], Set.empty) labels
 where
  go (acc, seen) (StructStaticFieldLabel n)
    | Set.member n seen = (acc, seen)
    | otherwise = (StructStaticFieldLabel n : acc, Set.insert n seen)
  go (acc, seen) (StructDynFieldOID i) =
    case do
      df <- IntMap.lookup i dynFields
      rtrString (dsfLabel df) of
      -- The dynamic field label is a string so that we should examine it.
      Just s
        | Set.member s seen -> (acc, seen)
        | otherwise -> (StructDynFieldOID i : acc, Set.insert s seen)
      Nothing -> (StructDynFieldOID i : acc, seen)

data Binding = Binding
  { value :: Tree
  , isIterVar :: !Bool
  }
  deriving (Generic)
