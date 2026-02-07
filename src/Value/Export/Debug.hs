{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Export.Debug where

import Control.Monad (foldM)
import Data.Aeson (ToJSON, object, toJSON, (.=))
import qualified Data.Aeson.Key as Key
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import Feature (
  mkDisjFeature,
  mkDynFieldFeature,
  mkListIdxFeature,
  mkListStoreIdxFeature,
  mkMutArgFeature,
  mkPatternFeature,
 )
import StringIndex (ShowWTIndexer (..), TextIndexerMonad)
import Text.Printf (printf)
import Value.Comprehension
import Value.Constraint
import Value.Disj
import Value.DisjoinOp
import Value.Fix
import Value.Instances
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.Val

{- | A representation of a Val for debugging and visualization purposes.

TextIndexes have been resolved to their string labels.
-}
data ValRep = ValRep
  { trInfo :: [String]
  -- ^ General info about the tree node.
  , trExtraMetas :: [(String, String)]
  -- ^ Extra metadata about the tree node.
  , trFields :: [ValRepField]
  -- ^ Fields of the tree node.
  }

instance ToJSON ValRep where
  toJSON (ValRep info [] []) = toJSON $ mergeInfo info
  toJSON (ValRep info em []) = object ["__t" .= mergeInfo info, "__tmetas" .= mergeExtraMetas em]
  toJSON (ValRep info em fields) =
    object
      ( ["__t" .= mergeInfo info]
          ++ ["__tmetas" .= mergeExtraMetas em | not (null em)]
          ++ [ Key.fromString (trfLabel f <> trfAttr f) .= case trfValue f of
              ValRepFieldValueSimple s -> toJSON s
              ValRepFieldValueRegular r -> toJSON r
             | f <- fields
             ]
      )

mergeInfo :: [String] -> String
mergeInfo info = intercalate "," (filter (not . null) info)

mergeExtraMetas :: [(String, String)] -> String
mergeExtraMetas metas = intercalate ", " [k <> ":" <> v | (k, v) <- metas]

treeToRepString :: (TextIndexerMonad s m) => Val -> m String
treeToRepString t = do
  v <- buildRepVal t defaultValRepBuildOption
  return $ repToString 0 v

treeToFullRepString :: (TextIndexerMonad s m) => Val -> m String
treeToFullRepString t = do
  v <- buildRepVal t (defaultValRepBuildOption{trboRepSubFields = True})
  return $ repToString 0 v

repToString :: Int -> ValRep -> String
repToString toff (ValRep info extraMetas fields) =
  "("
    <> mergeInfo info
    <> ( if null fields
          then mempty
          else
            -- we need to add a newline for the fields block.
            "\n"
              <> foldl
                ( \acc (ValRepField label a sub) ->
                    let pre = replicate (toff + 1) ' ' <> "(" <> label <> a <> " "
                     in acc
                          <> pre
                          <> ( case sub of
                                ValRepFieldValueSimple s -> s
                                ValRepFieldValueRegular r ->
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

data ValRepField = ValRepField
  { trfLabel :: String
  , trfAttr :: String
  , trfValue :: ValRepFieldValue
  }

data ValRepFieldValue = ValRepFieldValueRegular ValRep | ValRepFieldValueSimple String

data ValRepBuildOption = ValRepBuildOption
  { trboShowMutArgs :: Bool
  , trboRepSubFields :: Bool
  }

defaultValRepBuildOption :: ValRepBuildOption
defaultValRepBuildOption = ValRepBuildOption{trboShowMutArgs = True, trboRepSubFields = False}

buildRepVal :: (TextIndexerMonad s m) => Val -> ValRepBuildOption -> m ValRep
buildRepVal t opt = do
  commonInfo <- buildCommonInfo t
  trf <- buildRepValVN t opt
  mutRF <- buildRepValMutable t opt
  return $
    trf
      { trInfo = commonInfo ++ trInfo trf
      , trExtraMetas = trExtraMetas trf ++ trExtraMetas mutRF -- ++ trExtraMetas blkRF
      , trFields = trFields trf ++ trFields mutRF -- ++ trFields blkRF
      }

buildCommonInfo :: (TextIndexerMonad s m) => Val -> m [String]
buildCommonInfo t = do
  tStr <- case t of
    IsFix r -> do
      addrsStr <- mapM tshow r.conjs
      valRep <- showSimpleVal (mkNewVal r.val)
      return $ printf "inner:%s,addrs:%s" valRep (show addrsStr)
    _ -> showSimpleVal t
  return
    [ tStr
    , case t.wrappedBy of
        VNNoVal -> ""
        _ -> "wrappedby:" ++ showValSymbol (mkNewVal t.wrappedBy)
    , if isRecurClosed t then "%#" else ""
    , if isJust (origExpr t) then "" else "N"
    , if isRootOfSubVal t then "R" else ""
    , -- , case t.embType of
      --     ETNone -> ""
      --     ETEnclosing -> "EC"
      --     ETEmbedded i -> "EM_" ++ show i
      case t.op of
        Just _ -> "TO"
        _ -> ""
    ]

buildRepValVN :: (TextIndexerMonad s m) => Val -> ValRepBuildOption -> m ValRep
buildRepValVN Val{valNode = tn} opt = case tn of
  VNAtom _ -> return $ consRep ([], [], [])
  VNBounds b -> return $ consRep ([show b], [], [])
  VNStruct struct -> buildRepValStruct struct opt
  VNList vs ->
    let
      sfields = zipWith (\j v -> (show (mkListStoreIdxFeature j), mempty, v)) [0 ..] (toList vs.store)
      ffields = zipWith (\j v -> (show (mkListIdxFeature j), mempty, v)) [0 ..] (toList vs.final)
     in
      do
        fields <- consFields (sfields ++ ffields) opt
        return $ consRep ([], [], fields)
  VNDisj d ->
    let djFields = zipWith (\j v -> (show $ mkDisjFeature j, mempty, v)) [0 ..] (toList $ dsjDisjuncts d)
     in do
          fields <- consFields djFields opt
          return $ consRep ([printf "dis:%s" (show $ dsjDefIndexes d)], [], fields)
  VNAtomCnstr c -> do
    fields <-
      consFields
        [ ("atom", mempty, mkAtomVal c.value)
        , ("validator", mempty, c.cnsValidator)
        ]
        opt
    return $ consRep ([], [], fields)
  VNBottom b -> return $ consRep ([show b], [], [])
  _ -> return $ consRep ([], [], [])

buildRepValMutable :: (TextIndexerMonad s m) => Val -> ValRepBuildOption -> m ValRep
buildRepValMutable (IsValMutable mut@(SOp op _)) opt = do
  args <-
    if trboShowMutArgs opt
      then
        mapM
          ( \(i, (f, v)) -> do
              fT <- tshow f
              meta <- case op of
                Compreh c -> case c.args `Seq.index` i of
                  ComprehArgLet j _ -> do
                    jT <- tshow j
                    return $ ",let," ++ T.unpack jT
                  ComprehArgIf _ -> return ",if"
                  ComprehArgFor p q _ -> do
                    pT <- tshow p
                    qT <- case q of
                      Just qIdx -> tshow qIdx
                      Nothing -> return ""
                    return $ ",for," ++ T.unpack pT ++ (if T.null qT then "" else "," ++ T.unpack qT)
                  ComprehArgTmpl _ -> return "tmpl"
                  ComprehArgIterVal _ -> return "iterval"
                _ -> return ""
              return
                ( T.unpack fT
                , meta
                , v
                )
          )
          ( zip
              [0 ..]
              (toList $ getSOpArgs mut)
          )
      else return []
  let metas = [("tgen", showOpType op)]
  case op of
    RegOp rop -> do
      fields <- consFields args opt
      return $ consTGenRep (("op", ropName rop) : metas, fields)
    Ref ref -> do
      fields <- consFields args opt
      ra <- do
        sStr <- tshow ref.ident
        return $ T.unpack sStr
      return $ consTGenRep (("ref", ra) : metas, fields)
    Compreh c -> do
      fields <- consFields args opt
      bindings <-
        mapM
          ( \(k, v) -> do
              kstr <- tshow k
              vstr <- tshow v
              return $ T.unpack kstr ++ ":" ++ T.unpack vstr
          )
          (Map.toList c.iterBindings)
      return $ consTGenRep (metas ++ [("bindings", show bindings)], fields)
    DisjOp d ->
      let
        terms =
          if trboShowMutArgs opt
            then
              zipWith
                ( \j v ->
                    (show (mkMutArgFeature j False), if dstMarked v then ",*" else "", dstValue v)
                )
                [0 ..]
                (toList $ djoTerms d)
            else []
       in
        do
          fields <- consFields terms opt
          return $ consTGenRep (metas, fields)
    _ -> do
      fields <- consFields args opt
      return $ consTGenRep (metas, fields)
buildRepValMutable _ _ = return $ consTGenRep ([], [])

buildRepValStruct :: (TextIndexerMonad s m) => Struct -> ValRepBuildOption -> m ValRep
buildRepValStruct struct opt =
  let
    buildPHFields :: (TextIndexerMonad s m) => m [ValRepField]
    buildPHFields = do
      as <-
        foldM
          ( \acc (j, dsf) -> do
              tfv <- buildFieldRepValue (dsfLabel dsf) opt
              dsfValRep <- showSimpleVal (dsfValue dsf)
              return $
                ValRepField
                  (show (mkDynFieldFeature j 0))
                  (dlabelAttr dsf <> ",dynf_val:" ++ dsfValRep)
                  tfv
                  : acc
          )
          []
          (IntMap.toList $ stcDynFields struct)
      bs <-
        mapM
          ( \(j, k) -> do
              tfv <- buildFieldRepValue (scsPattern k) opt
              scsValRep <- showSimpleVal (scsValue k)
              return $
                ValRepField
                  (show (mkPatternFeature j 0))
                  (",cns_val:" ++ scsValRep)
                  tfv
          )
          (IntMap.toList $ stcCnstrs struct)
      cs <-
        foldM
          ( \acc (l, ssf) -> do
              lstr <- tshow l
              tfv <- buildFieldRepValue (ssfValue ssf) opt
              return $
                ValRepField
                  (T.unpack lstr)
                  (staticlFieldAttr ssf)
                  tfv
                  : acc
          )
          []
          (Map.toList $ stcStaticFieldBases struct)
      ds <-
        foldM
          ( \acc (l, ssf) -> do
              lstr <- tshow l
              tfv <- buildFieldRepValue (ssfValue ssf) opt
              return $
                ValRepField
                  (T.unpack lstr)
                  (staticlFieldAttr ssf)
                  tfv
                  : acc
          )
          []
          (Map.toList $ stcFields struct)
      es <-
        foldM
          ( \acc (l, bind) -> do
              lstr <- tshow l
              tfv <- buildFieldRepValue bind.value opt
              return $
                ValRepField
                  (T.unpack lstr)
                  (if bind.isIterVar then ",itervar" else ",regvar")
                  tfv
                  : acc
          )
          []
          (Map.toList $ stcBindings struct)
      return $ as ++ bs ++ cs ++ ds ++ es

    buildMetas :: (TextIndexerMonad s m) => Struct -> m [(String, String)]
    buildMetas s =
      mapM
        ( \(k, v) -> do
            vstr <- v
            return (k, T.unpack vstr)
        )
        [ ("id", tshow s.stcID)
        , ("isConc", tshow $ stcIsConcrete s)
        , ("isClosed", tshow $ stcClosed s)
        ,
          ( "ord"
          , do
              xs <-
                mapM
                  ( \k -> do
                      x <- tshow k
                      return $ T.unpack x
                  )
                  $ stcOrdLabels s
              return $ T.pack $ intercalate ", " xs
          )
        , ("orig_fs", tshow $ Map.keys $ stcStaticFieldBases s)
        , ("lets", tshow $ Map.keys $ stcBindings s)
        , ("perms", tshow $ stcPerms s)
        , ("ev", fromMaybe "Nothing" <$> mapM tshow (stcEmbedVal s))
        , ("perm", tshow $ stcPermErr s)
        ]
   in
    do
      metas <- buildMetas struct
      phFields <- buildPHFields
      return $ consRep ([], metas, phFields)

consRep :: ([String], [(String, String)], [ValRepField]) -> ValRep
consRep (m, em, f) = ValRep m em f

consTGenRep :: ([(String, String)], [ValRepField]) -> ValRep
consTGenRep (em, f) = ValRep [] em f

consFields :: (TextIndexerMonad s m) => [(String, String, Val)] -> ValRepBuildOption -> m [ValRepField]
consFields xs opt =
  mapM
    ( \(l, a, v) -> do
        tfv <- buildFieldRepValue v opt
        return $ ValRepField l a tfv
    )
    xs

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

buildFieldRepValue :: (TextIndexerMonad s m) => Val -> ValRepBuildOption -> m ValRepFieldValue
buildFieldRepValue fv opt@ValRepBuildOption{trboRepSubFields = recurOnSub} =
  if recurOnSub
    then ValRepFieldValueRegular <$> buildRepVal fv opt
    else do
      origVal <- showOrigVal fv
      curVal <- showSimpleVal fv
      return $ ValRepFieldValueSimple (printf "orig:%s, v: %s" origVal curVal)

showSimpleVal :: (TextIndexerMonad s m) => Val -> m String
showSimpleVal t = case t of
  IsAtom a -> return $ show a
  _ -> return $ showValSymbol t

showOrigVal :: (TextIndexerMonad s m) => Val -> m String
showOrigVal t = case t of
  IsRef _ ref -> do
    sStr <- tshow ref.ident
    return $ T.unpack sStr
  IsValMutable (SOp mutop _) -> return $ showOpType mutop
  _ -> return $ showValSymbol t