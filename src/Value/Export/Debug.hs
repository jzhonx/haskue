{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Value.Export.Debug where

import Control.Monad (foldM)
import Data.Aeson (ToJSON, Value, object, toJSON, (.=))
import qualified Data.Aeson.Key as Key
import qualified Data.DList as DList
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Feature (
  ValAddr,
  fileTopValAddr,
  mkDisjFeature,
  mkDynFieldFeature,
  mkLetFeature,
  mkListIdxFeature,
  mkListStoreIdxFeature,
  mkOpArgFeature,
  mkPatternFeature,
  mkRegCnstrFeature,
  mkStringFeature,
 )
import StringIndex (ShowWTIndexer (..), TextIndexerMonad)
import Text.Printf (printf)
import Value.Comprehension
import Value.Disj
import Value.DisjoinOp
import Value.Instances
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.Val

class TermsRepShow a where
  toTermsRep :: (TextIndexerMonad s m) => a -> TermsRepOption -> m TermsRep

instance TermsRepShow VNode where
  toTermsRep = vnToTermsRep

instance TermsRepShow Val where
  toTermsRep = valToTermsRep

instance TermsRepShow Op where
  toTermsRep = opToTermsRep

instance TermsRepShow () where
  toTermsRep _ _ = return emptyTermsRep

instance TermsRepShow Constraint where
  toTermsRep = cnstrToTermsRep

instance TermsRepShow ConstraintSeq where
  toTermsRep cs = cnstrsToTermsRep (toList cs)

newtype TermsRepOption = TermsRepOption
  { troptRecur :: Bool
  }

defaultTermsRepOption :: TermsRepOption
defaultTermsRepOption = TermsRepOption{troptRecur = False}

recurShowTermsRepOption :: TermsRepOption
recurShowTermsRepOption = TermsRepOption{troptRecur = True}

toTermsRepWithAddr :: (TextIndexerMonad s m, TermsRepShow a) => ValAddr -> a -> m TermsRep
toTermsRepWithAddr addr a = do
  let isRoot = addr == fileTopValAddr
  toTermsRep a (defaultTermsRepOption{troptRecur = isRoot})

termsRepToJSONWithAddr :: (TextIndexerMonad s m, TermsRepShow a) => ValAddr -> a -> m Value
termsRepToJSONWithAddr addr a = do
  rep <- toTermsRepWithAddr addr a
  return $ toJSON rep

termsRepToFullJSON :: (TextIndexerMonad s m, TermsRepShow a) => a -> m Value
termsRepToFullJSON a = do
  rep <- toTermsRep a recurShowTermsRepOption
  return $ toJSON rep

{- | A representation of a VNode for debugging and visualization purposes.

TextIndexes have been resolved to their string labels.
-}
data TermsRep = TermsRep
  { trInfo :: [String]
  -- ^ General info about the tree node.
  , trExtraMetas :: [(String, String)]
  -- ^ Extra metadata about the tree node.
  , trTerms :: [TermRep]
  -- ^ Fields of the tree node.
  }

instance ToJSON TermsRep where
  toJSON (TermsRep info [] []) = toJSON $ mergeInfo info
  toJSON (TermsRep info em []) = object ["__t" .= mergeInfo info, "__tmetas" .= mergeExtraMetas em]
  toJSON (TermsRep info em fields) =
    object
      ( ["__t" .= mergeInfo info]
          ++ ["__tmetas" .= mergeExtraMetas em | not (null em)]
          ++ [ Key.fromString (trfLabel f <> trfAttr f) .= case trfContent f of
              TermRepContentScalar s -> toJSON s
              TermRepContentRegular r -> toJSON r
             | f <- fields
             ]
      )

instance Show TermsRep where
  show = termsRepToStringWIdent 0

emptyTermsRep :: TermsRep
emptyTermsRep = TermsRep{trInfo = [], trExtraMetas = [], trTerms = []}

mergeInfo :: [String] -> String
mergeInfo info = intercalate "," (filter (not . null) info)

mergeExtraMetas :: [(String, String)] -> String
mergeExtraMetas metas = intercalate ", " [k <> ":" <> v | (k, v) <- metas]

vnToStringTermsRep :: (TextIndexerMonad s m) => VNode -> m String
vnToStringTermsRep t = do
  v <- vnToTermsRep t defaultTermsRepOption
  return $ show v

valToStringTermsRep :: (TextIndexerMonad s m) => Val -> m String
valToStringTermsRep t = do
  v <- valToTermsRep t defaultTermsRepOption
  return $ show v

vnToFullStringTermsRep :: (TextIndexerMonad s m) => VNode -> m String
vnToFullStringTermsRep t = do
  v <- vnToTermsRep t (defaultTermsRepOption{troptRecur = True})
  return $ show v

termsRepToStringWIdent :: Int -> TermsRep -> String
termsRepToStringWIdent toff (TermsRep info extraMetas fields) =
  "("
    <> mergeInfo info
    <> ( if null fields
          then mempty
          else
            -- we need to add a newline for the fields block.
            "\n"
              <> foldl
                ( \acc (TermRep label a sub) ->
                    let pre = replicate (toff + 1) ' ' <> "(" <> label <> a <> " "
                     in acc
                          <> pre
                          <> ( case sub of
                                TermRepContentScalar s -> s
                                TermRepContentRegular r ->
                                  termsRepToStringWIdent
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

data TermRep = TermRep
  { trfLabel :: String
  , trfAttr :: String
  , trfContent :: TermRepContent
  }

data TermRepContent = TermRepContentRegular TermsRep | TermRepContentScalar String

vnToTermsRep :: (TextIndexerMonad s m) => VNode -> TermsRepOption -> m TermsRep
vnToTermsRep v@VNode{constraints} opt = do
  commonInfo <- buildCommonInfo v
  cnstrs <- cnstrsToTermsRep (toList constraints.static) opt
  vntr <- valToTermsRep (value v) opt
  return $
    vntr
      { trInfo = commonInfo ++ trInfo vntr
      , trExtraMetas = trExtraMetas vntr
      , trTerms = cnstrs.trTerms ++ trTerms vntr
      }

buildCommonInfo :: (TextIndexerMonad s m) => VNode -> m [String]
buildCommonInfo t = do
  tStr <- showSimpleVal t
  return
    [ tStr
    , "vers=" ++ show (version t)
    , if t.constraints.allResolved then "" else "U"
    ]

valToTermsRep :: (TextIndexerMonad s m) => Val -> TermsRepOption -> m TermsRep
valToTermsRep vn opt = case vn of
  VAtom a -> return $ consRep ([show a], [], [])
  VBounds b -> return $ consRep ([show b], [], [])
  VStruct struct -> buildRepValStruct struct opt
  VList vs ->
    let
      sfields = zipWith (\j v -> (show (mkListStoreIdxFeature j), mempty, v)) [0 ..] (toList vs.store)
      ffields = zipWith (\j v -> (show (mkListIdxFeature j), mempty, mkValVN v)) [0 ..] (toList vs.final)
     in
      do
        fields <- valPairsToTermRepList (sfields ++ ffields) opt
        return $ consRep ([], [], fields)
  VDisj d ->
    let djFields = zipWith (\j x -> (show $ mkDisjFeature j, mempty, mkValVN x)) [0 ..] (toList $ dsjDisjuncts d)
     in do
          fields <- valPairsToTermRepList djFields opt
          return $ consRep ([printf "dis:%s" (show $ dsjDefIndexes d)], [], fields)
  VBottom b -> return $ consRep ([show b], [], [])
  _ -> return $ consRep ([], [], [])

cnstrToTermsRep :: (TextIndexerMonad s m) => Constraint -> TermsRepOption -> m TermsRep
cnstrToTermsRep c opt = case c of
  ValCnstr vc -> valToTermsRep vc.vcVal opt
  OpCnstr oc -> opToTermsRep oc.ocOp opt
  StructEmbedCnstr xs -> cnstrsToTermsRep (toList xs) opt

cnstrsToTermsRep :: (TextIndexerMonad s m) => [Constraint] -> TermsRepOption -> m TermsRep
cnstrsToTermsRep constraints opt = do
  l <-
    mapM
      ( \(i, c) -> do
          fT <- T.unpack <$> tshow (mkRegCnstrFeature i)
          cont <- cnstrToTermsRep c opt
          case c of
            ValCnstr{} ->
              return $ TermRep{trfLabel = fT, trfAttr = "", trfContent = TermRepContentRegular cont}
            OpCnstr{} ->
              return $ TermRep{trfLabel = fT, trfAttr = "", trfContent = TermRepContentRegular cont}
            StructEmbedCnstr _ ->
              return $ TermRep{trfLabel = fT, trfAttr = ",stremb", trfContent = TermRepContentRegular cont}
      )
      (zip [0 ..] constraints)
  return $ TermsRep{trInfo = [], trExtraMetas = [], trTerms = l}

cnstrsToFullTermsRep :: (TextIndexerMonad s m) => Seq.Seq Constraint -> m TermsRep
cnstrsToFullTermsRep constraints = cnstrsToTermsRep (toList constraints) (defaultTermsRepOption{troptRecur = True})

opToTermsRep :: (TextIndexerMonad s m) => Op -> TermsRepOption -> m TermsRep
opToTermsRep op opt = do
  args <-
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
            _ -> return ""
          return (T.unpack fT, meta, v)
      )
      (zip [0 ..] (toList $ getOpFArgs op))
  let metas = [("func", showOpType op)]
  case op of
    RegOp rop -> do
      fields <- valPairsToTermRepList args opt
      return $ consTGenRep (("op", ropName rop) : metas, fields)
    Ref ref -> do
      fields <- valPairsToTermRepList args opt
      ra <- do
        sStr <- tshow ref.ident
        return $ T.unpack sStr
      diffStr <- T.unpack <$> tshow ref.resolvedIdentAddr
      return $
        consTGenRep ([("ref", ra), ("diff", diffStr), ("comprehIdx", show ref.resolvedComprehClauseIdx)] ++ metas, fields)
    Compreh _ -> do
      fields <- valPairsToTermRepList args opt
      return $ consTGenRep (metas, fields)
    DisjOp d ->
      let
        terms =
          zipWith
            ( \j v ->
                (show (mkOpArgFeature j), if dstMarked v then ",*" else "", dstValue v)
            )
            [0 ..]
            (toList $ djoTerms d)
       in
        do
          fields <- valPairsToTermRepList terms opt
          return $ consTGenRep (metas, fields)
    VSelect idx -> do
      fields <- valPairsToTermRepList (("indexVal", "", idx.base) : args) opt
      return $ consTGenRep (metas, fields)
    _ -> do
      fields <- valPairsToTermRepList args opt
      return $ consTGenRep (metas, fields)

buildRepValStruct :: (TextIndexerMonad s m) => Struct -> TermsRepOption -> m TermsRep
buildRepValStruct struct opt =
  let
    buildPHFields :: (TextIndexerMonad s m) => m [TermRep]
    buildPHFields = do
      as <-
        foldM
          ( \acc (j, dsf) -> do
              tfv <- buildValueTermRepNodeContent (dsfLabel dsf) opt
              return $ TermRep{trfLabel = show (mkDynFieldFeature j 0), trfAttr = "", trfContent = tfv} : acc
          )
          []
          (IntMap.toList $ stcDynFields struct)
      as2 <-
        foldM
          ( \acc (j, dsf) -> do
              tfv <- buildCnstrSeqTermRepNodeContent (dsfValue dsf) opt
              return $ TermRep{trfLabel = show (mkDynFieldFeature j 1), trfAttr = "", trfContent = tfv} : acc
          )
          []
          (IntMap.toList $ stcDynFields struct)
      bs <-
        mapM
          ( \(j, k) -> do
              tfv <- buildValueTermRepNodeContent (scsPattern k) opt
              return $
                TermRep
                  (show (mkPatternFeature j 0))
                  ""
                  tfv
          )
          (IntMap.toList $ stcCnstrs struct)
      bs2 <-
        mapM
          ( \(j, k) -> do
              tfv <- buildCnstrSeqTermRepNodeContent (scsValue k) opt
              return $
                TermRep
                  (show (mkPatternFeature j 1))
                  ""
                  tfv
          )
          (IntMap.toList $ stcCnstrs struct)
      ds <-
        foldM
          ( \acc (l, ssf) -> do
              lstr <- tshow (mkStringFeature l)
              tfv <- buildValueTermRepNodeContent (ssfValue ssf) opt
              return $
                TermRep
                  (T.unpack lstr)
                  (staticlFieldAttr ssf)
                  tfv
                  : acc
          )
          []
          (Map.toList $ stcFields struct)
      es <-
        foldM
          ( \acc (l, v) -> do
              lstr <- tshow (mkLetFeature l)
              tfv <- buildValueTermRepNodeContent v opt
              return $
                TermRep
                  (T.unpack lstr)
                  mempty
                  tfv
                  : acc
          )
          []
          (Map.toList $ stcBindings struct)
      return $ as ++ as2 ++ bs ++ bs2 ++ ds ++ es

    buildMetas :: (TextIndexerMonad s m) => Struct -> m [(String, String)]
    buildMetas s =
      mapM
        ( \(k, v) -> do
            vstr <- v
            return (k, T.unpack vstr)
        )
        [ ("id", tshow s.stcID)
        , ("closed", tshow $ stcClosed s)
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
              return $ T.pack $ intercalate ", " (DList.toList xs)
          )
        , ("lets", tshow $ Map.keys $ stcBindings s)
        , ("perms", tshow $ stcPerms s)
        , ("ev", fromMaybe "Nothing" <$> mapM tshow (mkValVN <$> stcEmbedVal s))
        ,
          ( "perm"
          , tshow $ case stcPermErr s of
              Just err -> Just $ VBottom err
              Nothing -> Nothing
          )
        ]
   in
    do
      metas <- buildMetas struct
      phFields <- buildPHFields
      return $ consRep ([], metas, phFields)

consRep :: ([String], [(String, String)], [TermRep]) -> TermsRep
consRep (info, em, f) = TermsRep{trInfo = info, trExtraMetas = em, trTerms = f}

consTGenRep :: ([(String, String)], [TermRep]) -> TermsRep
consTGenRep (em, f) = TermsRep{trInfo = [], trExtraMetas = em, trTerms = f}

valPairsToTermRepList :: (TextIndexerMonad s m) => [(String, String, VNode)] -> TermsRepOption -> m [TermRep]
valPairsToTermRepList xs opt =
  mapM
    ( \(l, a, v) -> do
        tfv <- buildValueTermRepNodeContent v opt
        return $ TermRep{trfLabel = l, trfAttr = a, trfContent = tfv}
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
staticFieldMeta = staticlFieldAttr

dlabelAttr :: DynamicField -> String
dlabelAttr dsf = attr (dsfAttr dsf) <> isVar (dsfAttr dsf) <> ",dynf"

buildValueTermRepNodeContent :: (TextIndexerMonad s m) => VNode -> TermsRepOption -> m TermRepContent
buildValueTermRepNodeContent fv opt@TermsRepOption{troptRecur = recurOnSub} =
  if recurOnSub
    then TermRepContentRegular <$> vnToTermsRep fv opt
    else do
      origVal <- showOrigVal fv
      valT <- oneLinerStringOfVNode fv
      return $ TermRepContentScalar (printf "orig:%s, v: %s" origVal valT)

buildCnstrSeqTermRepNodeContent :: (TextIndexerMonad s m) => Seq.Seq Constraint -> TermsRepOption -> m TermRepContent
buildCnstrSeqTermRepNodeContent sq opt@TermsRepOption{troptRecur = recurOnSub} =
  if recurOnSub
    then TermRepContentRegular <$> cnstrsToTermsRep (toList sq) opt
    else do
      return $ TermRepContentScalar ""

showSimpleVal :: (TextIndexerMonad s m) => VNode -> m String
showSimpleVal t = return $ showValType (value t)

showOrigVal :: (TextIndexerMonad s m) => VNode -> m String
showOrigVal t = case t of
  -- IsRef _ ref -> do
  --   sStr <- tshow ref.ident
  --   return $ T.unpack sStr
  IsValSoleOp op -> return $ showOpType op
  _ -> return $ showValType (value t)