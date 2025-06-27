{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Struct where

import Control.DeepSeq (NFData (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import qualified Data.Text as T
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

{- | A block is a structure that contains a struct and a set of embeddings.

Reduction of a block is not necessarily a struct.
-}
data Block = Block
  { blkStruct :: Struct
  , blkEmbeds :: IntMap.IntMap Embedding
  , blkNonStructValue :: Maybe Tree
  }
  deriving (Generic)

-- instance (Eq t) => Eq (Block t) where
--   (==) s1 s2 = blkStruct s1 == blkStruct s2 && blkNonStructValue s1 == blkNonStructValue s2

emptyBlock :: Block
emptyBlock =
  Block
    { blkStruct = emptyStruct
    , blkEmbeds = IntMap.empty
    , blkNonStructValue = Nothing
    }

modifyBlockStruct :: (Struct -> Struct) -> Block -> Block
modifyBlockStruct f blk = blk{blkStruct = f (blkStruct blk)}

setBlockStruct :: Struct -> Block -> Block
setBlockStruct s blk = blk{blkStruct = s}

data Struct = Struct
  { stcID :: !Int
  -- ^ The ID is used to identify the struct. It will not be used in the comparison of structs.
  , stcOrdLabels :: [T.Text]
  -- ^ stcOrdLabels should only contain string labels, meaning it contains all regular fields, hidden fields and
  -- definitions. It should not contain let bindings.
  , stcBlockIdents :: Set.Set T.Text
  -- ^ The original identifiers declared in the block. It is used to validate identifiers.
  -- It includes both static fields and let bindings.
  -- It is needed because new static fields of embeddings can be merged into the struct.
  -- Once the struct is created, the static identifiers are fixed. The let identifiers can be rewritten with the scope
  -- id.
  , stcLets :: Map.Map T.Text LetBinding
  -- ^ Let bindings are read-only. They are not reduced.
  , stcCnstrs :: IntMap.IntMap StructCnstr
  , stcDynFields :: IntMap.IntMap DynamicField
  -- ^ We should not shrink the list as it is a heap list.
  -- | == Results start
  , stcClosed :: !Bool
  -- ^ The closed flag is used to indicate that the struct is closed, but the fields may not be closed.
  , stcPerms :: [PermItem]
  , stcFields :: Map.Map T.Text Field
  -- ^ It is the fields, excluding the let bindings.
  , stcIsConcrete :: !Bool
  }
  deriving (Generic)

data LabelAttr = LabelAttr
  { lbAttrCnstr :: StructFieldCnstr
  , lbAttrIsIdent :: !Bool
  }
  deriving (Show, Eq, Generic, NFData)

data StructFieldCnstr = SFCRegular | SFCRequired | SFCOptional
  deriving (Eq, Ord, Show, Generic, NFData)

data StructFieldType = SFTRegular | SFTHidden | SFTDefinition
  deriving (Eq, Ord, Show)

data StructStubVal
  = SStubField Field
  | SStubLet LetBinding

data Field = Field
  { ssfValue :: Tree
  , ssfBaseRaw :: Maybe Tree
  -- ^ It is the raw parsed value of the field before any dynamic fields or constraints are applied.
  -- It can be None if the field is created from a dynamic field.
  , ssfAttr :: LabelAttr
  , ssfObjects :: Set.Set Int
  -- ^ A set of object IDs that have been unified with base raw value.
  }
  deriving (Generic)

data LetBinding = LetBinding
  { lbReferred :: Bool
  , lbValue :: Tree
  -- ^ The value is only for the storage purpose.
  }
  deriving (Generic)

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

{- | StructCnstr is in the form of {[pattern]: value}.

The first element is the pattern, the second element is the value.
-}
data StructCnstr = StructCnstr
  { scsID :: !Int
  , scsPattern :: Tree
  , scsValue :: Tree
  -- ^ The value is only for the storage purpose. It is still raw. It will not be reduced during reducing.
  }
  deriving (Generic)

data Embedding = Embedding
  { embID :: !Int
  , embValue :: Tree
  }
  deriving (Generic)

data BlockElemAdder
  = StaticSAdder T.Text Field
  | DynamicSAdder !Int DynamicField
  | CnstrSAdder !Int Tree Tree
  | LetSAdder T.Text Tree
  | EmbedSAdder !Int Tree

-- instance (Eq t) => Eq (Struct) where
--   (==) :: (Eq t) => Struct -> Struct -> Bool
--   (==) s1 s2 =
--     stcOrdLabels s1 == stcOrdLabels s2
--       && stcFields s1 == stcFields s2
--       -- && stcCnstrs s1 == stcCnstrs s2
--       -- && stcDynFields s1 == stcDynFields s2
--       && stcClosed s1 == stcClosed s2

-- instance (Show t) => Show (Struct) where
--   show s =
--     "Struct {"
--       ++ "stcID="
--       ++ show (stcID s)
--       ++ ", stcOrdLabels="
--       ++ show (stcOrdLabels s)
--       ++ "}"

-- instance (Eq t) => Eq (StructCnstr t) where
--   (==) f1 f2 = scsPattern f1 == scsPattern f2 && scsValue f1 == scsValue f2

-- instance (Eq t) => Eq (DynamicField) where
--   (==) f1 f2 =
--     dsfValue f1 == dsfValue f2
--       && dsfAttr f1 == dsfAttr f2
--       && dsfLabel f1 == dsfLabel f2
--       && dsfLabelIsInterp f1 == dsfLabelIsInterp f2

-- instance (Eq t) => Eq (Field) where
--   (==) f1 f2 = ssfValue f1 == ssfValue f2 && ssfAttr f1 == ssfAttr f2

{- | Permission item stores permission information for the static fields and dynamic fields of a struct.

The permission information is used to check if the opposite labels and dynamic fields are allowed when the base struct
is closed and neither of the structs is embedded.

Because structs can be merged and constraints can be changed, we need to store the permission information of the
original struct.
-}
data PermItem = PermItem
  { piCnstrs :: Set.Set Int
  , piLabels :: Set.Set T.Text
  , piDyns :: Set.Set Int
  , piOpLabels :: Set.Set T.Text
  -- ^ The static fields to be checked.
  , piOpDyns :: Set.Set Int
  -- ^ The dynamic fields to be checked.
  }
  deriving (Eq, Generic, NFData)

instance Show PermItem where
  show p =
    "PermItem{"
      ++ "cnstrs="
      ++ show (Set.toList $ piCnstrs p)
      ++ ",labels="
      ++ show (Set.toList $ piLabels p)
      ++ ",dyns="
      ++ show (Set.toList $ piDyns p)
      ++ ",opLabels="
      ++ show (Set.toList $ piOpLabels p)
      ++ ",opDyns="
      ++ show (Set.toList $ piOpDyns p)
      ++ "}"

mergeAttrs :: LabelAttr -> LabelAttr -> LabelAttr
mergeAttrs a1 a2 =
  LabelAttr
    { lbAttrCnstr = min (lbAttrCnstr a1) (lbAttrCnstr a2)
    , lbAttrIsIdent = lbAttrIsIdent a1 || lbAttrIsIdent a2
    }

mkStructFromAdders :: Int -> [BlockElemAdder] -> Struct
mkStructFromAdders sid as =
  emptyStruct
    { stcID = sid
    , stcOrdLabels = ordLabels
    , stcBlockIdents = Set.fromList ordLabels `Set.union` Set.fromList (map fst lets)
    , stcFields = Map.fromList statics
    , stcLets = Map.fromList lets
    , stcDynFields = dyns
    , stcCnstrs = cnstrs
    }
 where
  ordLabels = [l | StaticSAdder l _ <- as]
  statics = [(s, sf) | StaticSAdder s sf <- as]
  lets = [(s, LetBinding{lbReferred = False, lbValue = v}) | LetSAdder s v <- as]
  dyns =
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

emptyStruct :: Struct
emptyStruct =
  Struct
    { stcID = 0
    , stcOrdLabels = []
    , stcFields = Map.empty
    , stcBlockIdents = Set.empty
    , stcLets = Map.empty
    , stcDynFields = IntMap.empty
    , stcCnstrs = IntMap.empty
    , stcClosed = False
    , stcPerms = []
    , stcIsConcrete = False
    }

updateFieldValue :: Tree -> Field -> Field
updateFieldValue t field = field{ssfValue = t}

staticFieldMker :: Tree -> LabelAttr -> Field
staticFieldMker t a =
  Field
    { ssfValue = t
    , ssfBaseRaw = Just t
    , ssfAttr = a
    , ssfObjects = Set.empty
    }

dynToField ::
  DynamicField ->
  Maybe Field ->
  (Tree -> Tree -> Tree) ->
  Field
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
      , ssfBaseRaw = Nothing
      , ssfAttr = dsfAttr df
      , ssfObjects = Set.fromList [dsfID df]
      }

mkEmbedding :: Int -> Tree -> Embedding
mkEmbedding eid t =
  Embedding
    { embID = eid
    , embValue = t
    }

addStructLetBind :: Struct -> T.Text -> Tree -> Struct
addStructLetBind struct s t =
  struct
    { stcLets =
        Map.insert
          s
          (LetBinding{lbValue = t, lbReferred = False})
          (stcLets struct)
    }

markLetBindReferred :: T.Text -> Struct -> Struct
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
hasEmptyFields :: Struct -> Bool
hasEmptyFields s = Map.null (stcFields s) && null (stcDynFields s)

getFieldType :: String -> Maybe StructFieldType
getFieldType [] = Nothing
getFieldType ident
  | head ident == '#' || length ident >= 2 && take 2 ident == "_#" = Just SFTDefinition
  | head ident == '_' = Just SFTHidden
  | otherwise = Just SFTRegular

{- | Look up the struct stub value in the struct.

The name could be in both the fields and let bindings, or either.
-}
lookupStructStubVal :: T.Text -> Struct -> [StructStubVal]
lookupStructStubVal name struct =
  catMaybes
    [ SStubField <$> Map.lookup name (stcFields struct)
    , SStubLet <$> Map.lookup name (stcLets struct)
    ]

lookupStructLet :: T.Text -> Struct -> Maybe LetBinding
lookupStructLet name struct = Map.lookup name (stcLets struct)

updateStructLet :: T.Text -> LetBinding -> Struct -> Struct
updateStructLet name sub struct =
  struct
    { stcLets = Map.insert name sub (stcLets struct)
    }

lookupStructField :: T.Text -> Struct -> Maybe Field
lookupStructField name struct = Map.lookup name (stcFields struct)

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
updateStructField name sub struct =
  _appendOrdLabelIfNeeded
    name
    ( struct
        { stcFields = Map.insert name sub (stcFields struct)
        }
    )

_appendOrdLabelIfNeeded :: T.Text -> Struct -> Struct
_appendOrdLabelIfNeeded name struct =
  if name `elem` stcOrdLabels struct
    then struct
    else struct{stcOrdLabels = stcOrdLabels struct ++ [name]}

updateStructWithFields :: [(T.Text, Field)] -> Struct -> Struct
updateStructWithFields fields struct = foldr (\(k, field) acc -> updateStructField k field acc) struct fields

removeStructFields :: [T.Text] -> Struct -> Struct
removeStructFields names struct =
  struct
    { stcOrdLabels = filter (`notElem` names) (stcOrdLabels struct)
    , stcFields = foldr Map.delete (stcFields struct) names
    }

{- | Given a struct and a list of static field names, return the permission information to check if the static fields
are allowed
-}
getPermInfoForFields :: Struct -> [T.Text] -> [PermItem]
getPermInfoForFields struct = foldr go []
 where
  go name ext =
    foldr
      ( \p acc ->
          if name `Set.member` piLabels p || name `Set.member` piOpLabels p then p : acc else acc
      )
      ext
      (stcPerms struct)

{- | Given a struct and the index of a dynamic field, return the permission information to check if the dynamic
field is allowed or whether the dynamic field allows other fields.
-}
getPermInfoForDyn :: Struct -> Int -> [PermItem]
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
getPermInfoForPattern :: Struct -> Int -> [PermItem]
getPermInfoForPattern struct i =
  foldr (\p acc -> if i `Set.member` piCnstrs p then p : acc else acc) [] (stcPerms struct)
