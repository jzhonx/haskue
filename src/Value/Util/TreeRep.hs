{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Util.TreeRep where

import Data.Aeson (ToJSON, object, toJSON, (.=))
import qualified Data.Aeson.Key as Key
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isJust, listToMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import Path (
  BlockTASeg (..),
  TASeg (..),
  textToStringSeg,
  textToStringTASeg,
 )
import Text.Printf (printf)
import Value.Atom
import Value.Block
import Value.Constraint
import Value.Disj
import Value.DisjoinOp
import Value.List
import Value.Mutable
import Value.Reference
import Value.Tree

data TreeRep = TreeRep
  { trInfo :: [String]
  , trExtraMetas :: [(String, String)]
  , trFields :: [TreeRepField]
  }

instance ToJSON TreeRep where
  toJSON (TreeRep info [] []) = toJSON $ mergeInfo info
  toJSON (TreeRep info em []) = object ["__t" .= mergeInfo info, "__tmetas" .= mergeExtraMetas em]
  toJSON (TreeRep info em fields) =
    object
      ( ["__t" .= mergeInfo info]
          ++ ["__tmetas" .= mergeExtraMetas em | not (null em)]
          ++ [ Key.fromString (trfLabel f <> trfAttr f) .= case trfValue f of
              TreeRepFieldValueSimple s -> toJSON s
              TreeRepFieldValueRegular r -> toJSON r
             | f <- fields
             ]
      )

mergeInfo :: [String] -> String
mergeInfo info = intercalate "," (filter (not . null) info)

mergeExtraMetas :: [(String, String)] -> String
mergeExtraMetas metas =
  intercalate ", " [k <> ":" <> v | (k, v) <- metas]

treeToRepString :: Tree -> String
treeToRepString t = repToString 0 (buildRepTree t defaultTreeRepBuildOption)

treeToFullRepString :: Tree -> String
treeToFullRepString t = repToString 0 (buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = True}))

repToString :: Int -> TreeRep -> String
repToString toff (TreeRep info extraMetas fields) =
  "("
    <> mergeInfo info
    <> ( if null fields
          then mempty
          else
            -- we need to add a newline for the fields block.
            "\n"
              <> foldl
                ( \acc (TreeRepField label a sub) ->
                    let pre = replicate (toff + 1) ' ' <> "(" <> label <> a <> " "
                     in acc
                          <> pre
                          <> ( case sub of
                                TreeRepFieldValueSimple s -> s
                                TreeRepFieldValueRegular r ->
                                  repToString
                                    (length pre)
                                    r
                             )
                          <> ")"
                          <> "\n"
                )
                mempty
                fields
              -- reserve spaces for the closing parenthesis.
              <> replicate toff ' '
       )
    <> ( if null extraMetas
          then mempty
          else
            "\n"
              <> foldl
                ( \acc (label, lmeta) ->
                    let pre = replicate (toff + 1) ' ' <> "(" <> label <> " "
                     in acc
                          <> pre
                          <> lmeta
                          <> ")"
                          <> "\n"
                )
                mempty
                extraMetas
              <> replicate toff ' '
       )
    <> ")"

data TreeRepField = TreeRepField
  { trfLabel :: String
  , trfAttr :: String
  , trfValue :: TreeRepFieldValue
  }

data TreeRepFieldValue = TreeRepFieldValueRegular TreeRep | TreeRepFieldValueSimple String

data TreeRepBuildOption = TreeRepBuildOption
  { trboShowMutArgs :: Bool
  , trboRepSubFields :: Bool
  }

defaultTreeRepBuildOption :: TreeRepBuildOption
defaultTreeRepBuildOption = TreeRepBuildOption{trboShowMutArgs = True, trboRepSubFields = False}

buildRepTree :: Tree -> TreeRepBuildOption -> TreeRep
buildRepTree t opt =
  let
    commonInfo =
      [ case t of
          IsAtom a -> show a
          _ -> showTreeSymbol t
      , if isRecurClosed t then "%#" else ""
      , if isJust (treeExpr t) then "" else "N"
      , if isRootOfSubTree t then "R" else ""
      , if isUnifiedWithRC t then "UWC" else ""
      , if isSCyclic t then "SC" else ""
      , case t.embType of
          ETNone -> ""
          ETEnclosing -> "EC"
          ETEmbedded i -> "EM_" ++ show i
      , case valGenEnv t of
          TGenOp _ -> "TO"
          TGenImmutable -> ""
      ]

    trf = buildRepTreeTN t opt
    mutRF = buildRepTreeMutable t opt
   in
    trf
      { trInfo = commonInfo ++ trInfo trf
      , trExtraMetas = trExtraMetas trf ++ trExtraMetas mutRF -- ++ trExtraMetas blkRF
      , trFields = trFields trf ++ trFields mutRF -- ++ trFields blkRF
      }

buildRepTreeTN :: Tree -> TreeRepBuildOption -> TreeRep
buildRepTreeTN Tree{treeNode = tn} opt = case tn of
  TNAtom _ -> consRep ([], [], [])
  TNBounds b -> consRep ([show b], [], [])
  TNStruct struct -> buildRepTreeStruct struct opt
  TNList vs ->
    let fields = zipWith (\j v -> (show (IndexTASeg j), mempty, v)) [0 ..] (lstSubs vs)
     in consRep ([], [], consFields fields opt)
  TNDisj d ->
    let djFields = zipWith (\j v -> (show $ DisjTASeg j, mempty, v)) [0 ..] (dsjDisjuncts d)
     in consRep ([printf "dis:%s" (show $ dsjDefIndexes d)], [], consFields djFields opt)
  TNAtomCnstr c ->
    consRep
      ( []
      , []
      , consFields
          [ ("atom", mempty, mkAtomTree c.value)
          , ("validator", mempty, mkAtomTree $ String (T.pack $ show $ cnsValidator c))
          ]
          opt
      )
  TNRefCycle -> consRep ([], [], [])
  TNRefSubCycle _ -> consRep ([], [], [])
  TNBottom b -> consRep ([show b], [], [])
  TNTop -> consRep ([], [], [])
  TNNoVal -> consRep ([], [], [])

buildRepTreeMutable :: Tree -> TreeRepBuildOption -> TreeRep
buildRepTreeMutable (IsTGenOp mut@(Mutable op mf)) opt =
  let
    args =
      if trboShowMutArgs opt
        then zipWith (\j v -> (show (MutArgTASeg j), mempty, v)) [0 ..] (toList $ getMutArgs mut)
        else []
    metas = [("tgen", showOpType op), ("ridxes", show $ Set.toList $ mfArgsReduced mf)]
   in
    case op of
      RegOp rop -> consTGenRep (("op", ropName rop) : metas, consFields args opt)
      Ref ref ->
        consTGenRep
          ( ( "ref"
            , showRefArg
                (refArg ref)
                (\x -> listToMaybe $ catMaybes [T.unpack <$> rtrString x, show <$> rtrInt x])
            )
              : metas
          , []
          )
      Compreh _ -> consTGenRep (metas, consFields args opt)
      DisjOp d ->
        let
          terms =
            if trboShowMutArgs opt
              then
                zipWith
                  ( \j v ->
                      (show (MutArgTASeg j), if dstMarked v then ",*" else "", dstValue v)
                  )
                  [0 ..]
                  (toList $ djoTerms d)
              else []
         in
          consTGenRep (metas, consFields terms opt)
      _ -> consTGenRep (metas, consFields args opt)
buildRepTreeMutable _ _ = consTGenRep ([], [])

buildRepTreeStruct :: Struct -> TreeRepBuildOption -> TreeRep
buildRepTreeStruct struct opt =
  let
    phFields :: [TreeRepField]
    phFields =
      foldr
        ( \(j, dsf) acc ->
            TreeRepField
              (show (BlockTASeg $ DynFieldTASeg j 0))
              (dlabelAttr dsf)
              (buildFieldRepValue (dsfLabel dsf) opt)
              : acc
        )
        []
        (IntMap.toList $ stcDynFields struct)
        ++ map
          ( \(j, k) ->
              TreeRepField
                (show (BlockTASeg $ PatternTASeg j 0))
                (",cns_val:" ++ showTreeSymbol (scsValue k))
                (buildFieldRepValue (scsPattern k) opt)
          )
          (IntMap.toList $ stcCnstrs struct)
        ++ foldr
          ( \(l, ssf) acc ->
              TreeRepField
                (show (BlockTASeg $ StubFieldTASeg (textToStringSeg l)))
                (staticlFieldAttr ssf)
                (buildFieldRepValue (ssfValue ssf) opt)
                : acc
          )
          []
          (Map.toList $ stcStaticFieldBases struct)
        ++ foldr
          ( \(l, ssf) acc ->
              TreeRepField
                (show (textToStringTASeg l))
                (staticlFieldAttr ssf)
                (buildFieldRepValue (ssfValue ssf) opt)
                : acc
          )
          []
          (Map.toList $ stcFields struct)

    metas :: Struct -> [(String, String)]
    metas s =
      [ ("id", show s.stcID)
      , ("isConc", show $ stcIsConcrete s)
      , ("isClosed", show $ stcClosed s)
      , ("ord", intercalate ", " (map show $ stcOrdLabels s))
      , ("orig_fs", show $ Map.keys $ stcStaticFieldBases s)
      , ("lets", show $ Map.keys $ stcBindings s)
      , ("perms", show $ stcPerms s)
      , ("ev", show $ stcEmbedVal s)
      , ("perm", show $ stcPermErr s)
      ]
   in
    consRep
      ( []
      , metas struct
      , phFields
      )

consRep :: ([String], [(String, String)], [TreeRepField]) -> TreeRep
consRep (m, em, f) = TreeRep m em f

consTGenRep :: ([(String, String)], [TreeRepField]) -> TreeRep
consTGenRep (em, f) = TreeRep [] em f

consFields :: [(String, String, Tree)] -> TreeRepBuildOption -> [TreeRepField]
consFields xs opt = map (\(l, a, v) -> TreeRepField l a (buildFieldRepValue v opt)) xs

attr :: LabelAttr -> String
attr a = case lbAttrCnstr a of
  SFCRegular -> mempty
  SFCRequired -> "!"
  SFCOptional -> "?"

isVar :: LabelAttr -> String
isVar a =
  if lbAttrIsIdent a
    then ",v"
    else mempty

staticlFieldAttr :: Field -> String
staticlFieldAttr sf = attr (ssfAttr sf) <> isVar (ssfAttr sf)

staticFieldMeta :: Field -> String
staticFieldMeta sf =
  staticlFieldAttr sf
    <> ",objs:"
    <> show (Set.toList $ ssfObjects sf)

dlabelAttr :: DynamicField -> String
dlabelAttr dsf = attr (dsfAttr dsf) <> isVar (dsfAttr dsf) <> ",dynf"

buildFieldRep :: Struct -> T.Text -> TreeRepBuildOption -> TreeRepField
buildFieldRep s label opt =
  case lookupStructField label s of
    Just sf -> TreeRepField (T.unpack label) (staticFieldMeta sf) (buildFieldRepValue (ssfValue sf) opt)
    Nothing -> TreeRepField (T.unpack label) "" (buildFieldRepValue (mkBottomTree "not found") opt)

buildFieldRepValue :: Tree -> TreeRepBuildOption -> TreeRepFieldValue
buildFieldRepValue fv opt@TreeRepBuildOption{trboRepSubFields = recurOnSub} =
  if recurOnSub
    then TreeRepFieldValueRegular (buildRepTree fv opt)
    else TreeRepFieldValueSimple (printf "orig:%s, v: %s" (showTreeSymbol fv) (oneLinerStringOfTree fv))
