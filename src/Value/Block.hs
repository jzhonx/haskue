{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

module Value.Block where

import Control.DeepSeq (NFData (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import qualified Data.Text as T
import GHC.Generics (Generic)
import {-# SOURCE #-} Value.Tree

{- | A block is a structure that contains a set of fields and a set of embeddings.

Reduction of a block is not necessarily a struct.
-}
data Block = Block
  { blkID :: !Int
  -- ^ The ID is used to identify the block. It will not be used in the comparison of structs.
  , blkOrdLabels :: [BlockLabel]
  -- ^ blkOrdLabels is a list of ordered field labels. It does not contain let bindings.
  , blkStaticFields :: Map.Map T.Text Field
  -- ^ The un-evaluated fields that defined in this block. Note that fields defined in the embedding are not included.
  , blkBindings :: Map.Map T.Text LetBinding
  -- ^ Let bindings are read-only. They are not reduced.
  , blkDynFields :: IntMap.IntMap DynamicField
  -- ^ We should not shrink the list as it is a heap list.
  , blkCnstrs :: IntMap.IntMap StructCnstr
  , blkEmbeds :: IntMap.IntMap Embedding
  , blkValue :: BlockValue
  }
  deriving (Generic)

data BlockLabel = BlockFieldLabel T.Text | BlockDynFieldOID !Int
  deriving (Eq, Generic, NFData, Ord)

instance Show BlockLabel where
  show (BlockFieldLabel n) = T.unpack n
  show (BlockDynFieldOID i) = show i

data BlockValue
  = BlockStruct Struct
  | BlockEmbed Tree
  deriving (Generic)

pattern IsBlockStruct :: Struct -> Block
pattern IsBlockStruct s <- Block{blkValue = BlockStruct s}

pattern IsBlockEmbed :: Tree -> Block
pattern IsBlockEmbed t <- Block{blkValue = BlockEmbed t}

emptyBlock :: Block
emptyBlock =
  Block
    { blkID = 0
    , blkStaticFields = Map.empty
    , blkOrdLabels = []
    , blkBindings = Map.empty
    , blkDynFields = IntMap.empty
    , blkCnstrs = IntMap.empty
    , blkEmbeds = IntMap.empty
    , blkValue = BlockStruct emptyStruct
    }

modifyBlockStruct :: (Struct -> Struct) -> Block -> Block
modifyBlockStruct f blk@(IsBlockStruct s) = blk{blkValue = BlockStruct (f s)}
modifyBlockStruct _ blk = blk

setBlockStruct :: Struct -> Block -> Block
setBlockStruct s blk@(IsBlockStruct _) = blk{blkValue = BlockStruct s}
setBlockStruct _ blk = blk

data Struct = Struct
  { stcClosed :: !Bool
  -- ^ == Results start
  , -- \^ The closed flag is used to indicate that the struct is closed, but the fields may not be closed.
    stcPerms :: [PermItem]
  , stcFields :: Map.Map T.Text Field
  -- ^ It is the fields.
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

data BlockStubVal
  = BlkStubField Field
  | BlkStubLet LetBinding

data Field = Field
  { ssfValue :: Tree
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

{- | Permission item stores permission information for the static fields and dynamic fields of a struct.

The permission information is used to check if the opposite labels and dynamic fields are allowed when the base struct
is closed and neither of the structs is embedded.

Because structs can be merged and constraints can be changed, we need to store the permission information of the
original struct.
-}
data PermItem = PermItem
  { piCnstrs :: Set.Set Int
  , piLabels :: Set.Set BlockLabel
  , piOpLabels :: Set.Set BlockLabel
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

mkBlockFromAdder :: Int -> BlockElemAdder -> Block
mkBlockFromAdder bid adder
  | StaticSAdder s sf <- adder =
      block
        { blkStaticFields = Map.singleton s sf
        , blkOrdLabels = [BlockFieldLabel s]
        , blkValue =
            BlockStruct $
              emptyStruct
                { stcFields = Map.singleton s sf
                }
        }
  | DynamicSAdder oid dsf <- adder =
      block
        { blkOrdLabels = [BlockDynFieldOID oid]
        , blkDynFields = IntMap.singleton oid dsf
        }
  | CnstrSAdder oid pat val <- adder =
      block
        { blkCnstrs = IntMap.singleton oid (StructCnstr oid pat val)
        }
  | LetSAdder s v <- adder =
      block{blkBindings = Map.singleton s LetBinding{lbReferred = False, lbValue = v}}
  | EmbedSAdder eid t <- adder =
      block{blkEmbeds = IntMap.singleton eid (mkEmbedding eid t)}
 where
  block = emptyBlock{blkID = bid}

emptyStruct :: Struct
emptyStruct =
  Struct
    { stcFields = Map.empty
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
      , ssfAttr = dsfAttr df
      , ssfObjects = Set.fromList [dsfID df]
      }

mkEmbedding :: Int -> Tree -> Embedding
mkEmbedding eid t =
  Embedding
    { embID = eid
    , embValue = t
    }

lookupBlockLet :: T.Text -> Block -> Maybe LetBinding
lookupBlockLet name block = Map.lookup name (blkBindings block)

{- | Insert a new let binding into the block.

Caller should ensure that the name is not already in the block.
-}
insertBlockLet :: T.Text -> Tree -> Block -> Block
insertBlockLet s t block =
  block
    { blkBindings =
        Map.insert
          s
          LetBinding
            { lbReferred = False
            , lbValue = t
            }
          (blkBindings block)
    }

updateBlockLet :: T.Text -> Tree -> Block -> Block
updateBlockLet name t block =
  block
    { blkBindings =
        Map.update (\lb -> Just lb{lbValue = t}) name (blkBindings block)
    }

markLetBindReferred :: T.Text -> Block -> Block
markLetBindReferred name block =
  block
    { blkBindings =
        Map.update (\lb -> Just lb{lbReferred = True}) name (blkBindings block)
    }

-- | Determines whether the block has empty fields, including both static and dynamic fields.
hasEmptyFields :: Block -> Bool
hasEmptyFields blk = Map.null (blkStaticFields blk) && null (blkDynFields blk)

getFieldType :: String -> Maybe StructFieldType
getFieldType [] = Nothing
getFieldType ident
  | head ident == '#' || length ident >= 2 && take 2 ident == "_#" = Just SFTDefinition
  | head ident == '_' = Just SFTHidden
  | otherwise = Just SFTRegular

{- | Look up the stub value in the block.

The name could be in both the fields and let bindings, or either.
-}
lookupBlockStubVal :: T.Text -> Block -> [BlockStubVal]
lookupBlockStubVal name blk@(IsBlockStruct struct) =
  catMaybes
    [ BlkStubField <$> Map.lookup name (stcFields struct)
    , BlkStubLet <$> Map.lookup name (blkBindings blk)
    ]
lookupBlockStubVal name blk = catMaybes [BlkStubLet <$> Map.lookup name (blkBindings blk)]

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
updateStructField name sub struct = struct{stcFields = Map.insert name sub (stcFields struct)}

updateStructWithFields :: [(T.Text, Field)] -> Struct -> Struct
updateStructWithFields fields struct = foldr (\(k, field) acc -> updateStructField k field acc) struct fields

-- | Remove the static fields by names from the struct.
removeStructFieldsByNames :: [T.Text] -> Struct -> Struct
removeStructFieldsByNames names struct = struct{stcFields = foldr Map.delete (stcFields struct) names}

{- | Given a struct and a list of static field names, return the permission information to check if the static fields
are allowed
-}
getPermInfoForFields :: Struct -> [T.Text] -> [PermItem]
getPermInfoForFields struct = foldr go []
 where
  go name ext =
    foldr
      ( \p acc ->
          if BlockFieldLabel name `Set.member` piLabels p || BlockFieldLabel name `Set.member` piOpLabels p then p : acc else acc
      )
      ext
      (stcPerms struct)

{- | Given a struct and the id of a dynamic field, return the permission information to check if the dynamic
field is allowed or whether the dynamic field allows other fields.
-}
getPermInfoForDyn :: Struct -> Int -> [PermItem]
getPermInfoForDyn struct i =
  foldr
    ( \p acc ->
        if BlockDynFieldOID i `Set.member` piLabels p || BlockDynFieldOID i `Set.member` piOpLabels p then p : acc else acc
    )
    []
    (stcPerms struct)

{- | Given a struct and the index of a constraint, return the permission information to check whether the constraint
allows other fields.
-}
getPermInfoForPattern :: Struct -> Int -> [PermItem]
getPermInfoForPattern struct i =
  foldr (\p acc -> if i `Set.member` piCnstrs p then p : acc else acc) [] (stcPerms struct)

{- | Deduplicate the block labels by removing the static that have the same label or dynamic field that is evaluated to
the same label.
-}
dedupBlockLabels :: (Tree -> Maybe T.Text) -> IntMap.IntMap DynamicField -> [BlockLabel] -> [BlockLabel]
dedupBlockLabels rtrString dynFields labels =
  reverse . fst $ foldl go ([], Set.empty) labels
 where
  go (acc, seen) (BlockFieldLabel n)
    | Set.member n seen = (acc, seen)
    | otherwise = (BlockFieldLabel n : acc, Set.insert n seen)
  go (acc, seen) (BlockDynFieldOID i) =
    case do
      df <- IntMap.lookup i dynFields
      rtrString (dsfLabel df) of
      -- The dynamic field label is a string so that we should examine it.
      Just s
        | Set.member s seen -> (acc, seen)
        | otherwise -> (BlockDynFieldOID i : acc, Set.insert s seen)
      Nothing -> (BlockDynFieldOID i : acc, seen)