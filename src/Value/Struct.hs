{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}

module Value.Struct where

import qualified AST
import Common (BuildASTExpr (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Exception (throwErrSt)

{- | A block is a structure that contains a struct and a set of embeddings.

Reduction of a block is not necessarily a struct.
-}
data Block t = Block
  { blkStruct :: Struct t
  , blkEmbeds :: IntMap.IntMap (Embedding t)
  , blkNonStructValue :: Maybe t
  }

instance (Eq t) => Eq (Block t) where
  (==) s1 s2 = blkStruct s1 == blkStruct s2 && blkNonStructValue s1 == blkNonStructValue s2

instance (BuildASTExpr t) => BuildASTExpr (Block t) where
  buildASTExpr _ _ = throwErrSt "not implemented"

emptyBlock :: Block t
emptyBlock =
  Block
    { blkStruct = emptyStruct
    , blkEmbeds = IntMap.empty
    , blkNonStructValue = Nothing
    }

modifyBlockStruct :: (Struct t -> Struct t) -> Block t -> Block t
modifyBlockStruct f blk = blk{blkStruct = f (blkStruct blk)}

setBlockStruct :: Struct t -> Block t -> Block t
setBlockStruct s blk = blk{blkStruct = s}

data Struct t = Struct
  { stcID :: Int
  -- ^ The ID is used to identify the struct. It will not be used in the comparison of structs.
  , stcOrdLabels :: [String]
  -- ^ stcOrdLabels should only contain string labels, meaning it contains all regular fields, hidden fields and
  -- definitions. It should not contain let bindings.
  , stcBlockIdents :: Set.Set String
  -- ^ The original identifiers declared in the block. It is used to validate identifiers.
  -- It includes both static fields and let bindings.
  -- It is needed because new static fields of embeddings can be merged into the struct.
  -- Once the struct is created, the static identifiers are fixed. The let identifiers can be rewritten with the scope
  -- id.
  , stcLets :: Map.Map String (LetBinding t)
  -- ^ Let bindings are read-only. They are not reduced.
  , stcCnstrs :: IntMap.IntMap (StructCnstr t)
  , stcDynFields :: IntMap.IntMap (DynamicField t)
  -- ^ We should not shrink the list as it is a heap list.
  -- | == Results start
  , stcClosed :: Bool
  -- ^ The closed flag is used to indicate that the struct is closed, but the fields may not be closed.
  , stcPerms :: [PermItem]
  , stcFields :: Map.Map String (Field t)
  -- ^ It is the fields, excluding the let bindings.
  , stcIsConcrete :: Bool
  }

data LabelAttr = LabelAttr
  { lbAttrCnstr :: StructFieldCnstr
  , lbAttrIsIdent :: Bool
  }
  deriving (Show, Eq)

data StructFieldCnstr = SFCRegular | SFCRequired | SFCOptional
  deriving (Eq, Ord, Show)

data StructFieldType = SFTRegular | SFTHidden | SFTDefinition
  deriving (Eq, Ord, Show)

data StructStubVal t
  = SStubField (Field t)
  | SStubLet (LetBinding t)
  deriving (Show, Eq)

data Field t = Field
  { ssfValue :: t
  , ssfBaseRaw :: Maybe t
  -- ^ It is the raw parsed value of the field before any dynamic fields or constraints are applied.
  -- It can be None if the field is created from a dynamic field.
  , ssfAttr :: LabelAttr
  , ssfObjects :: Set.Set Int
  -- ^ A set of object IDs that have been unified with base raw value.
  }
  deriving (Show)

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
  , dsfLabelIsInterp :: Bool
  -- ^ Whether the label is an interpolated label.
  , dsfValue :: t
  -- ^ The value is only for the storage purpose. It will not be reduced during reducing dynamic fields.
  }
  deriving (Show)

{- | StructCnstr is in the form of {[pattern]: value}.

The first element is the pattern, the second element is the value.
-}
data StructCnstr t = StructCnstr
  { scsID :: Int
  , scsPattern :: t
  , scsValue :: t
  -- ^ The value is only for the storage purpose. It is still raw. It will not be reduced during reducing.
  }
  deriving (Show)

data Embedding t = Embedding
  { embID :: Int
  , embValue :: t
  }
  deriving (Show, Functor)

data BlockElemAdder t
  = StaticSAdder String (Field t)
  | DynamicSAdder Int (DynamicField t)
  | CnstrSAdder Int t t
  | LetSAdder String t
  | EmbedSAdder Int t
  deriving (Show)

instance (Eq t) => Eq (Struct t) where
  (==) :: (Eq t) => Struct t -> Struct t -> Bool
  (==) s1 s2 =
    stcOrdLabels s1 == stcOrdLabels s2
      && stcFields s1 == stcFields s2
      -- && stcCnstrs s1 == stcCnstrs s2
      -- && stcDynFields s1 == stcDynFields s2
      && stcClosed s1 == stcClosed s2

instance (Show t) => Show (Struct t) where
  show s =
    "Struct {"
      ++ "stcID="
      ++ show (stcID s)
      ++ ", stcOrdLabels="
      ++ show (stcOrdLabels s)
      ++ "}"

instance (BuildASTExpr t) => BuildASTExpr (Struct t) where
  buildASTExpr _ _ = throwErrSt "not implemented"

instance (Eq t) => Eq (StructCnstr t) where
  (==) f1 f2 = scsPattern f1 == scsPattern f2 && scsValue f1 == scsValue f2

instance (Eq t) => Eq (DynamicField t) where
  (==) f1 f2 =
    dsfValue f1 == dsfValue f2
      && dsfAttr f1 == dsfAttr f2
      && dsfLabel f1 == dsfLabel f2
      && dsfLabelIsInterp f1 == dsfLabelIsInterp f2

instance (Eq t) => Eq (Field t) where
  (==) f1 f2 = ssfValue f1 == ssfValue f2 && ssfAttr f1 == ssfAttr f2

{- | Permission item stores permission information for the static fields and dynamic fields of a struct.

The permission information is used to check if the opposite labels and dynamic fields are allowed when the base struct
is closed and neither of the structs is embedded.

Because structs can be merged and constraints can be changed, we need to store the permission information of the
original struct.
-}
data PermItem = PermItem
  { piCnstrs :: Set.Set Int
  , piLabels :: Set.Set String
  , piDyns :: Set.Set Int
  , piOpLabels :: Set.Set String
  -- ^ The static fields to be checked.
  , piOpDyns :: Set.Set Int
  -- ^ The dynamic fields to be checked.
  }

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

mkStructFromAdders :: Int -> [BlockElemAdder t] -> Struct t
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

emptyStruct :: Struct t
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

updateFieldValue :: t -> Field t -> Field t
updateFieldValue t field = field{ssfValue = t}

staticFieldMker :: (Show t) => t -> LabelAttr -> Field t
staticFieldMker t a =
  Field
    { ssfValue = t
    , ssfBaseRaw = Just t
    , ssfAttr = a
    , ssfObjects = Set.empty
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

mkEmbedding :: Int -> t -> Embedding t
mkEmbedding eid t =
  Embedding
    { embID = eid
    , embValue = t
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
lookupStructStubVal :: String -> Struct t -> [StructStubVal t]
lookupStructStubVal name struct =
  catMaybes
    [ SStubField <$> Map.lookup name (stcFields struct)
    , SStubLet <$> Map.lookup name (stcLets struct)
    ]

lookupStructLet :: String -> Struct t -> Maybe (LetBinding t)
lookupStructLet name struct = Map.lookup name (stcLets struct)

updateStructLet :: String -> LetBinding t -> Struct t -> Struct t
updateStructLet name sub struct =
  struct
    { stcLets = Map.insert name sub (stcLets struct)
    }

lookupStructField :: String -> Struct t -> Maybe (Field t)
lookupStructField name struct = Map.lookup name (stcFields struct)

lookupStructIdentField :: String -> Struct t -> Maybe (Field t)
lookupStructIdentField name struct =
  case Map.lookup name (stcFields struct) of
    Just field ->
      if lbAttrIsIdent (ssfAttr field)
        then Just field
        else Nothing
    Nothing -> Nothing

-- | Update the struct with the given label name and field.
updateStructField :: String -> Field t -> Struct t -> Struct t
updateStructField name sub struct =
  _appendOrdLabelIfNeeded
    name
    ( struct
        { stcFields = Map.insert name sub (stcFields struct)
        }
    )

_appendOrdLabelIfNeeded :: String -> Struct t -> Struct t
_appendOrdLabelIfNeeded name struct =
  if name `elem` stcOrdLabels struct
    then struct
    else struct{stcOrdLabels = stcOrdLabels struct ++ [name]}

updateStructWithFields :: [(String, Field t)] -> Struct t -> Struct t
updateStructWithFields fields struct = foldr (\(k, field) acc -> updateStructField k field acc) struct fields

removeStructFields :: [String] -> Struct t -> Struct t
removeStructFields names struct =
  struct
    { stcOrdLabels = filter (`notElem` names) (stcOrdLabels struct)
    , stcFields = foldr Map.delete (stcFields struct) names
    }

{- | Given a struct and a list of static field names, return the permission information to check if the static fields
are allowed
-}
getPermInfoForFields :: Struct t -> [String] -> [PermItem]
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
