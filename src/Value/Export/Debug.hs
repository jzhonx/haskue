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
import Data.Maybe (fromMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import EvalAddr (
  EvalAddr,
  fileTopEvalAddr,
  mkDisjTermStep,
  mkDynFieldTermStep,
  mkLetFeature,
  mkListIdxFeature,
  mkListStoreIdxTermStep,
  mkOpArgTermStep,
  mkPatternTermStep,
  mkRegCnstrTermStep,
  mkStringFeature,
 )
import StringIndex (ShowWTIndexer (..), TextIndexerMonad)
import Text.Printf (printf)
import Value.Comprehension
import Value.Disj
import Value.DisjoinOp
import Value.Instances ()
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.Val

class ToTermTree a where
  toTermTree :: (TextIndexerMonad s m) => a -> TermTreeOptions -> m TermTree

instance ToTermTree VNode where
  toTermTree = vnToTermTree

instance ToTermTree Val where
  toTermTree = valToTermTree

instance ToTermTree Op where
  toTermTree = opToTermTree

instance ToTermTree () where
  toTermTree _ _ = return emptyTermTree

instance ToTermTree Constraint where
  toTermTree = cnstrToTermTree

instance ToTermTree ConstraintSeq where
  toTermTree cs = cnstrsToTermTree (toList cs)

newtype TermTreeOptions = TermTreeOptions
  { recurseIntoChildren :: Bool
  }

defaultTermTreeOptions :: TermTreeOptions
defaultTermTreeOptions = TermTreeOptions{recurseIntoChildren = False}

recursiveTermTreeOptions :: TermTreeOptions
recursiveTermTreeOptions = TermTreeOptions{recurseIntoChildren = True}

toTermTreeForAddr :: (TextIndexerMonad s m, ToTermTree a) => EvalAddr -> a -> m TermTree
toTermTreeForAddr addr a = do
  let isRoot = addr == fileTopEvalAddr
  toTermTree a (defaultTermTreeOptions{recurseIntoChildren = isRoot})

toTermTreeJSONForAddr :: (TextIndexerMonad s m, ToTermTree a) => EvalAddr -> a -> m Value
toTermTreeJSONForAddr addr a = do
  tree <- toTermTreeForAddr addr a
  return $ toJSON tree

toRecursiveTermTreeJSON :: (TextIndexerMonad s m, ToTermTree a) => a -> m Value
toRecursiveTermTreeJSON a = do
  tree <- toTermTree a recursiveTermTreeOptions
  return $ toJSON tree

{- | A representation of a VNode for debugging and visualization purposes.

TextIndexes have been resolved to their string labels.
-}
data TermTree = TermTree
  { ttInfo :: [String]
  -- ^ General info about the tree node.
  , ttExtraMetas :: [(String, String)]
  -- ^ Extra metadata about the tree node.
  , ttEntries :: [TermEntry]
  -- ^ Entries of the tree node.
  }

instance ToJSON TermTree where
  toJSON (TermTree info [] []) = toJSON $ mergeInfo info
  toJSON (TermTree info em []) = object ["__t" .= mergeInfo info, "__tmetas" .= mergeExtraMetas em]
  toJSON (TermTree info em fields) =
    object
      ( ["__t" .= mergeInfo info]
          ++ ["__tmetas" .= mergeExtraMetas em | not (null em)]
          ++ [ Key.fromString (teLabel f <> teAttr f) .= case teContent f of
                TermContentScalar s -> toJSON s
                TermContentTree r -> toJSON r
             | f <- fields
             ]
      )

instance Show TermTree where
  show = renderTermTreeWithIndent 0

emptyTermTree :: TermTree
emptyTermTree = TermTree{ttInfo = [], ttExtraMetas = [], ttEntries = []}

mergeInfo :: [String] -> String
mergeInfo info = intercalate "," (filter (not . null) info)

mergeExtraMetas :: [(String, String)] -> String
mergeExtraMetas metas = intercalate ", " [k <> ":" <> v | (k, v) <- metas]

vnToTermTreeString :: (TextIndexerMonad s m) => VNode -> m String
vnToTermTreeString t = do
  v <- vnToTermTree t defaultTermTreeOptions
  return $ show v

valToTermTreeString :: (TextIndexerMonad s m) => Val -> m String
valToTermTreeString t = do
  v <- valToTermTree t defaultTermTreeOptions
  return $ show v

vnToRecursiveTermTreeString :: (TextIndexerMonad s m) => VNode -> m String
vnToRecursiveTermTreeString t = do
  v <- vnToTermTree t recursiveTermTreeOptions
  return $ show v

renderTermTreeWithIndent :: Int -> TermTree -> String
renderTermTreeWithIndent toff (TermTree info extraMetas fields) =
  "("
    <> mergeInfo info
    <> ( if null fields
          then mempty
          else
            -- we need to add a newline for the fields block.
            "\n"
              <> foldl
                ( \acc (TermEntry label a sub) ->
                    let pre = replicate (toff + 1) ' ' <> "(" <> label <> a <> " "
                     in acc
                          <> pre
                          <> ( case sub of
                                TermContentScalar s -> s
                                TermContentTree r ->
                                  renderTermTreeWithIndent
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

data TermEntry = TermEntry
  { teLabel :: String
  , teAttr :: String
  , teContent :: TermContent
  }

data TermContent = TermContentTree TermTree | TermContentScalar String

vnToTermTree :: (TextIndexerMonad s m) => VNode -> TermTreeOptions -> m TermTree
vnToTermTree v@VNode{constraints} opt = do
  commonInfo <- buildVNodeInfo v
  cnstrs <- cnstrsToTermTree (toList constraints.static) opt
  vntr <- valToTermTree (value v) opt
  return $
    vntr
      { ttInfo = commonInfo ++ ttInfo vntr
      , ttExtraMetas = ttExtraMetas vntr
      , ttEntries = cnstrs.ttEntries ++ ttEntries vntr
      }

buildVNodeInfo :: (TextIndexerMonad s m) => VNode -> m [String]
buildVNodeInfo t =
  return
    [ showValType (value t)
    , "vers=" ++ show (version t)
    , if t.constraints.allResolved then "" else "U"
    ]

valToTermTree :: (TextIndexerMonad s m) => Val -> TermTreeOptions -> m TermTree
valToTermTree vn opt = case vn of
  VAtom a -> return $ mkTermTree ([show a], [], [])
  VBounds b -> return $ mkTermTree ([show b], [], [])
  VStruct struct -> structToTermTree struct opt
  VList vs ->
    let
      sfields = zipWith (\j v -> (show (mkListStoreIdxTermStep j), mempty, v)) [0 ..] (toList vs.store)
      ffields = zipWith (\j v -> (show (mkListIdxFeature j), mempty, mkValVN v)) [0 ..] (toList vs.final)
     in
      do
        fields <- valueFieldsToTermEntries (sfields ++ ffields) opt
        return $ mkTermTree ([], [], fields)
  VDisj d ->
    let djFields = zipWith (\j x -> (show $ mkDisjTermStep j, mempty, x)) [0 ..] (toList $ dsjDisjuncts d)
     in do
          fields <- valueFieldsToTermEntries djFields opt
          return $ mkTermTree ([printf "dis:%s" (show $ dsjDefIndexes d)], [], fields)
  VBottom b -> return $ mkTermTree ([show b], [], [])
  _ -> return $ mkTermTree ([], [], [])

cnstrToTermTree :: (TextIndexerMonad s m) => Constraint -> TermTreeOptions -> m TermTree
cnstrToTermTree c opt = case c of
  ValCnstr vc -> valToTermTree vc.vcVal opt
  OpCnstr oc -> opToTermTree oc.ocOp opt
  StructEmbedCnstr xs -> cnstrsToTermTree (toList xs) opt

cnstrsToTermTree :: (TextIndexerMonad s m) => [Constraint] -> TermTreeOptions -> m TermTree
cnstrsToTermTree constraints opt = do
  l <-
    mapM
      ( \(i, c) -> do
          fT <- T.unpack <$> tshow (mkRegCnstrTermStep i)
          cont <- cnstrToTermTree c opt
          case c of
            ValCnstr{} ->
              return $ TermEntry{teLabel = fT, teAttr = "", teContent = TermContentTree cont}
            OpCnstr{} ->
              return $ TermEntry{teLabel = fT, teAttr = "", teContent = TermContentTree cont}
            StructEmbedCnstr _ ->
              return $ TermEntry{teLabel = fT, teAttr = ",stremb", teContent = TermContentTree cont}
      )
      (zip [0 ..] constraints)
  return $ TermTree{ttInfo = [], ttExtraMetas = [], ttEntries = l}

cnstrsToRecursiveTermTree :: (TextIndexerMonad s m) => Seq.Seq Constraint -> m TermTree
cnstrsToRecursiveTermTree constraints = cnstrsToTermTree (toList constraints) recursiveTermTreeOptions

opToTermTree :: (TextIndexerMonad s m) => Op -> TermTreeOptions -> m TermTree
opToTermTree op opt = do
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
  let metas = [("kind", showOpKind op)]
  case op of
    RegOp rop -> do
      fields <- valueFieldsToTermEntries args opt
      return $ mkTermTreeWithMetadata (("op", ropName rop) : metas, fields)
    Ref ref -> do
      fields <- valueFieldsToTermEntries args opt
      ra <- do
        sStr <- tshow ref.ident
        return $ T.unpack sStr
      locatorStr <- T.unpack <$> tshow ref.identLocator
      return $
        mkTermTreeWithMetadata
          ([("ref", ra), ("locator", locatorStr), ("comprehIdx", show ref.resolvedComprehClauseIdx)] ++ metas, fields)
    Compreh _ -> do
      fields <- valueFieldsToTermEntries args opt
      return $ mkTermTreeWithMetadata (metas, fields)
    DisjOp d ->
      let
        terms =
          zipWith
            ( \j v ->
                (show (mkOpArgTermStep j), if dstMarked v then ",*" else "", dstValue v)
            )
            [0 ..]
            (toList $ djoTerms d)
       in
        do
          fields <- valueFieldsToTermEntries terms opt
          return $ mkTermTreeWithMetadata (metas, fields)
    VSelect idx -> do
      fields <- valueFieldsToTermEntries (("indexVal", "", idx.base) : args) opt
      return $ mkTermTreeWithMetadata (metas, fields)
    _ -> do
      fields <- valueFieldsToTermEntries args opt
      return $ mkTermTreeWithMetadata (metas, fields)

structToTermTree :: (TextIndexerMonad s m) => Struct -> TermTreeOptions -> m TermTree
structToTermTree struct opt =
  let
    buildStructEntries :: (TextIndexerMonad s m) => m [TermEntry]
    buildStructEntries = do
      as <-
        foldM
          ( \acc (j, dsf) -> do
              tfv <- vnodeToTermContent (dsfLabel dsf) opt
              return $ TermEntry{teLabel = show (mkDynFieldTermStep j 0), teAttr = "", teContent = tfv} : acc
          )
          []
          (IntMap.toList $ stcDynFields struct)
      as2 <-
        foldM
          ( \acc (j, dsf) -> do
              tfv <- constraintsToTermContent (dsfValue dsf) opt
              return $ TermEntry{teLabel = show (mkDynFieldTermStep j 1), teAttr = "", teContent = tfv} : acc
          )
          []
          (IntMap.toList $ stcDynFields struct)
      bs <-
        mapM
          ( \(j, k) -> do
              tfv <- vnodeToTermContent (scsPattern k) opt
              return $
                TermEntry
                  (show (mkPatternTermStep j 0))
                  ""
                  tfv
          )
          (IntMap.toList $ stcCnstrs struct)
      bs2 <-
        mapM
          ( \(j, k) -> do
              tfv <- constraintsToTermContent (scsValue k) opt
              return $
                TermEntry
                  (show (mkPatternTermStep j 1))
                  ""
                  tfv
          )
          (IntMap.toList $ stcCnstrs struct)
      ds <-
        foldM
          ( \acc (l, ssf) -> do
              lstr <- tshow (mkStringFeature l)
              tfv <- vnodeToTermContent (ssfValue ssf) opt
              return $
                TermEntry
                  (T.unpack lstr)
                  (staticFieldAttr ssf)
                  tfv
                  : acc
          )
          []
          (Map.toList $ stcFields struct)
      es <-
        foldM
          ( \acc (l, v) -> do
              lstr <- tshow (mkLetFeature l)
              tfv <- vnodeToTermContent v opt
              return $
                TermEntry
                  (T.unpack lstr)
                  mempty
                  tfv
                  : acc
          )
          []
          (Map.toList $ stcBindings struct)
      return $ as ++ as2 ++ bs ++ bs2 ++ ds ++ es

    buildMetadata :: (TextIndexerMonad s m) => Struct -> m [(String, String)]
    buildMetadata s =
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
      metadata <- buildMetadata struct
      entries <- buildStructEntries
      return $ mkTermTree ([], metadata, entries)

mkTermTree :: ([String], [(String, String)], [TermEntry]) -> TermTree
mkTermTree (info, em, f) = TermTree{ttInfo = info, ttExtraMetas = em, ttEntries = f}

mkTermTreeWithMetadata :: ([(String, String)], [TermEntry]) -> TermTree
mkTermTreeWithMetadata (em, f) = TermTree{ttInfo = [], ttExtraMetas = em, ttEntries = f}

valueFieldsToTermEntries :: (TextIndexerMonad s m) => [(String, String, VNode)] -> TermTreeOptions -> m [TermEntry]
valueFieldsToTermEntries xs opt =
  mapM
    ( \(l, a, v) -> do
        tfv <- vnodeToTermContent v opt
        return $ TermEntry{teLabel = l, teAttr = a, teContent = tfv}
    )
    xs

constraintAttr :: LabelAttr -> String
constraintAttr a = case lbAttrCnstr a of
  SFCRegular -> mempty
  SFCRequired -> "!"
  SFCOptional -> "?"

variableAttr :: LabelAttr -> String
variableAttr a =
  if lbAttrIsIdent a
    then ",v"
    else mempty

staticFieldAttr :: Field -> String
staticFieldAttr sf = constraintAttr (ssfAttr sf) <> variableAttr (ssfAttr sf)

vnodeToTermContent :: (TextIndexerMonad s m) => VNode -> TermTreeOptions -> m TermContent
vnodeToTermContent fv opt@TermTreeOptions{recurseIntoChildren} =
  if recurseIntoChildren
    then TermContentTree <$> vnToTermTree fv opt
    else do
      valT <- tshow (value fv)
      return . TermContentScalar $ case fv of
        IsValSoleStaticOp op -> printf "op: %s, value: %s" (showOpSummary op) valT
        _ -> printf "type: %s, value: %s" (showValType $ value fv) valT

constraintsToTermContent :: (TextIndexerMonad s m) => Seq.Seq Constraint -> TermTreeOptions -> m TermContent
constraintsToTermContent sq opt@TermTreeOptions{recurseIntoChildren} =
  if recurseIntoChildren
    then TermContentTree <$> cnstrsToTermTree (toList sq) opt
    else do
      return $ TermContentScalar ""

showOpSummary :: Op -> String
showOpSummary op = case op of
  RegOp rop -> ropName rop
  _ -> showOpKind op
