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
import qualified Data.Text.Encoding as TE
import Path (
  BlockTASeg (..),
  TASeg (..),
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
  { trInfo :: String
  , trExtraMetas :: [(String, String)]
  , trFields :: [TreeRepField]
  }

instance ToJSON TreeRep where
  toJSON (TreeRep info [] []) = toJSON info
  toJSON (TreeRep info em []) = object ["__t" .= info, "__tmetas" .= mergeExtraMetas em]
  toJSON (TreeRep info em fields) =
    object
      ( ["__t" .= info]
          ++ ["__tmetas" .= mergeExtraMetas em | not (null em)]
          ++ [ Key.fromString (trfLabel f <> trfAttr f) .= case trfValue f of
              TreeRepFieldValueSimple s -> toJSON s
              TreeRepFieldValueRegular r -> toJSON r
             | f <- fields
             ]
      )
mergeExtraMetas :: [(String, String)] -> String
mergeExtraMetas metas =
  intercalate ", " [k <> ":" <> v | (k, v) <- metas]

treeToRepString :: Tree -> String
treeToRepString t = repToString 0 (buildRepTree t defaultTreeRepBuildOption)

treeToFullRepString :: Tree -> String
treeToFullRepString t = repToString 0 (buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = True}))

repToString :: Int -> TreeRep -> String
repToString toff (TreeRep meta extraMetas fields) =
  "("
    <> meta
    <> ( if null fields
          then mempty
          else
            -- we need to add a newline for the fields block.
            "\n"
              <> foldl
                ( \acc (TreeRepField label attr sub) ->
                    let pre = replicate (toff + 1) ' ' <> "(" <> label <> attr <> " "
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
  let trf = buildRepTreeTN t (treeNode t) opt
   in trf
        { trInfo =
            ( case t of
                IsAtom _ -> ""
                _ ->
                  (if treeRecurClosed t then "#," else "")
                    ++ (if isJust (treeExpr t) then "" else "N,")
                    ++ (if treeIsRootOfSubTree t then "R," else "")
                    ++ (if treeIsSCyclic t then "SC," else "")
            )
              ++ trInfo trf
        , trFields = trFields trf
        }

buildRepTreeTN :: Tree -> TreeNode -> TreeRepBuildOption -> TreeRep
buildRepTreeTN t tn opt@TreeRepBuildOption{trboRepSubFields = recurOnSub} = case tn of
  TNAtom leaf -> consRep (show leaf, mempty, [], [])
  -- TODO: segment
  TNBounds b -> consRep (mempty, show b, [], [])
  TNBlock blk ->
    let
      phFields :: [TreeRepField]
      phFields =
        foldr
          ( \(j, dsf) acc ->
              TreeRepField
                (show (BlockTASeg $ DynFieldTASeg j 0))
                (dlabelAttr dsf)
                (buildFieldRepValue (dsfLabel dsf))
                : acc
          )
          []
          (IntMap.toList $ blkDynFields blk)
          ++ map
            ( \(k, lb) ->
                TreeRepField
                  (show (BlockTASeg $ LetTASeg (TE.encodeUtf8 k)))
                  (printf ",r:%s" (show $ lbReferred lb))
                  (buildFieldRepValue (lbValue lb))
            )
            (Map.toList (blkBindings blk))
          ++ map
            ( \(j, k) ->
                TreeRepField
                  (show (BlockTASeg $ PatternTASeg j 0))
                  (",cns_val:" ++ showTreeSymbol (scsValue k))
                  (buildFieldRepValue (scsPattern k))
            )
            (IntMap.toList $ blkCnstrs blk)
          ++ map
            ( \(j, v) ->
                TreeRepField
                  (show (BlockTASeg $ EmbedTASeg j))
                  mempty
                  (buildFieldRepValue (embValue v))
            )
            (IntMap.toList $ blkEmbeds blk)

      metas :: Struct -> [(String, String)]
      metas s =
        [ ("ord", intercalate ", " (map show $ blkOrdLabels blk))
        , ("perms", show $ stcPerms s)
        , ("isConc", show $ stcIsConcrete s)
        , ("orig_fs", show $ Map.keys $ blkStaticFields blk)
        ]
     in
      case blk of
        IsBlockEmbed ev ->
          consRep
            ( symbol
            , "bid:" <> show (blkID blk)
            , []
            , phFields ++ [TreeRepField (show SubValTASeg) mempty (buildFieldRepValue ev)]
            )
        IsBlockStruct s ->
          consRep
            ( (if stcClosed s then "#" else mempty) <> symbol
            , "bid:" <> show (blkID blk)
            , metas s
            , foldr
                ( \label acc -> case label of
                    BlockFieldLabel l -> buildFieldRep s l : acc
                    BlockDynFieldOID oid ->
                      let dsf = blkDynFields blk IntMap.! oid
                       in case rtrString $ dsfLabel dsf of
                            Just l -> buildFieldRep s l : acc
                            Nothing -> acc
                )
                []
                (blkOrdLabels blk)
                ++ phFields
            )
        _ -> error "buildRepTreeTN: unexpected block type"
  TNList vs ->
    let fields = zipWith (\j v -> (show (IndexTASeg j), mempty, v)) [0 ..] (lstSubs vs)
     in consRep (symbol, mempty, [], consFields fields)
  TNDisj d ->
    let dfField = maybe [] (\v -> [(show DisjDefTASeg, mempty, v)]) (dsjDefault d)
        djFields = zipWith (\j v -> (show $ DisjRegTASeg j, mempty, v)) [0 ..] (dsjDisjuncts d)
     in consRep (symbol, printf "dis:%s" (show $ dsjDefIndexes d), [], consFields dfField ++ consFields djFields)
  TNAtomCnstr c ->
    consRep
      ( symbol
      , mempty
      , []
      , consFields
          [ ("atom", mempty, mkAtomTree (cnsAtom c))
          , ("validator", mempty, mkAtomTree $ String (T.pack $ show $ cnsValidator c))
          ]
      )
  TNRefCycle -> consRep (symbol, "", [], [])
  TNRefSubCycle p -> consRep (symbol, printf "ref-sub-cycle %s" (show p), [], [])
  TNMutable mut@(Mutable op mf) ->
    let
      args =
        if trboShowMutArgs opt
          then zipWith (\j v -> (show (MutArgTASeg j), mempty, v)) [0 ..] (toList $ getMutArgs mut)
          else []
      val = maybe [] (\s -> [(show SubValTASeg, mempty, s)]) (getMutVal mut)
      metas = [("ridxes", show $ Set.toList $ mfArgsReduced mf)]
     in
      case op of
        RegOp rop -> consRep (symbol, ropName rop, metas, consFields (args ++ val))
        Ref ref ->
          consRep
            ( symbol
            , showRefArg
                (refArg ref)
                (\x -> listToMaybe $ catMaybes [T.unpack <$> rtrString x, show <$> rtrInt x])
            , metas
            , consFields val
            )
        Compreh _ -> consRep (symbol, "", metas, consFields (args ++ val))
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
            consRep (symbol, mempty, metas, consFields (terms ++ val))
        _ -> consRep (symbol, "", metas, consFields (args ++ val))
  TNBottom b -> consRep (symbol, show b, [], [])
  TNTop -> consRep (symbol, mempty, [], [])
  TNNoValRef -> consRep (symbol, mempty, [], [])
 where
  symbol :: String
  symbol = showTreeSymbol t

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

  buildFieldRep :: Struct -> T.Text -> TreeRepField
  buildFieldRep s label =
    case lookupStructField label s of
      Just sf -> TreeRepField (T.unpack label) (staticFieldMeta sf) (buildFieldRepValue (ssfValue sf))
      Nothing -> TreeRepField (T.unpack label) "" (buildFieldRepValue $ mkBottomTree "not found")

  consRep :: (String, String, [(String, String)], [TreeRepField]) -> TreeRep
  consRep (s, m, em, f) = TreeRep (s <> ", " <> m) em f

  consFields :: [(String, String, Tree)] -> [TreeRepField]
  consFields = map (\(l, a, v) -> TreeRepField l a (buildFieldRepValue v))

  buildFieldRepValue :: Tree -> TreeRepFieldValue
  buildFieldRepValue fv =
    if recurOnSub
      then TreeRepFieldValueRegular (buildRepTree fv opt)
      else TreeRepFieldValueSimple (printf "orig:%s, v: %s" (showTreeSymbol fv) (oneLinerStringOfCurTreeState fv))
