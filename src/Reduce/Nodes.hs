{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.Nodes where

import Common (Config (..), HasConfig (..), HasContext (..), RuntimeParams (..))
import Control.Monad (foldM, unless, void, when)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (modify, runStateT)

import Control.Monad.Reader (local)
import Cursor
import Data.Aeson (ToJSON (..))
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, isJust, listToMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import Path
import Reduce.RMonad (
  RTCState (..),
  ReduceMonad,
  ResolveMonad,
  addRMUnreferredLet,
  debugInstantOpRM,
  debugInstantRM,
  debugInstantTM,
  debugSpanAdaptTM,
  debugSpanArgsAdaptRM,
  debugSpanMTreeArgsRM,
  debugSpanMTreeRM,
  debugSpanSimpleRM,
  debugSpanTM,
  debugSpanTreeRM,
  getRMContext,
  getRMUnreferredLets,
  getTMCursor,
  getTMTree,
  inSubTM,
  modifyTMTN,
  modifyTMTree,
  putTMTree,
 )
import Reduce.RefSys (searchTCIdentInPar)
import {-# SOURCE #-} Reduce.Root (reduce)
import Reduce.UnifyOp (UTree (..), mergeBinUTrees, unifyNormalizedTCs)
import Text.Printf (printf)
import Value
import Value.Util.TreeRep (treeToRepString)

-- ###
-- Reduce tree nodes
-- ###

{- | Reduce the struct.

Most of the heavy work is done in the propUpStructPost function.
-}
reduceBlock :: (ReduceMonad s r m) => m ()
reduceBlock = debugSpanTM "reduceBlock" $ do
  pconjs <- discoverPConjs
  tc <- getTMCursor
  rpconjs <- resolvePendingConjuncts pconjs tc
  mergedM <- handleResolvedPConjsForStruct rpconjs tc
  case mergedM of
    Nothing -> return ()
    Just merged -> reduceUnifiedBlock merged

reduceUnifiedBlock :: (ReduceMonad s r m) => Tree -> m ()
reduceUnifiedBlock unified = do
  tc <- getTMCursor
  case unified of
    IsBlock _ -> do
      putTMTree unified
      reduceStruct
    _ -> do
      -- Set the block value to the unified value of type non-block.
      modifyTMTree $ \x -> case x of
        IsBlock block -> let newBlock = block{blkValue = BlockEmbed unified} in setTN x $ TNBlock newBlock
        _ -> x
      reduce
  handleBlockReducedRes (tcFocus tc)

-- | Handle the resolved pending conjuncts for mutable trees.
handleResolvedPConjsForStruct :: (ResolveMonad s r m) => ResolvedPConjuncts -> TrCur -> m (Maybe Tree)
handleResolvedPConjsForStruct IncompleteConjuncts _ = return Nothing
handleResolvedPConjsForStruct (AtomCnstrConj ac) _ = return $ Just $ mkAtomCnstrTree ac
handleResolvedPConjsForStruct (ResolvedConjuncts [conj]) _ = return $ Just $ tcFocus conj
handleResolvedPConjsForStruct (ResolvedConjuncts conjs) tc = unifyNormalizedTCs conjs tc

{- | Handle the result of the block reduction.

Most importantly, it adds the embeds back to the block if the block is reduced to a struct.
-}
handleBlockReducedRes :: (ReduceMonad s r m) => Tree -> m ()
handleBlockReducedRes (IsBlock origBlock) = do
  tc <- getTMCursor
  case tcFocus tc of
    IsBottom _ -> return ()
    IsBlock block ->
      -- Add back the embeds which are removed in the unify step.
      modifyTMTN (TNBlock (block{blkEmbeds = blkEmbeds origBlock}))
    _ ->
      -- If the focus is not a struct, it means the struct has been reduced to an embedded value.
      modifyTMTN (TNBlock (origBlock{blkValue = BlockEmbed (tcFocus tc)}))
handleBlockReducedRes _ = throwErrSt "handleBlockReducedRes: original tree is not a block"

{- | Reduce the struct.

It is guanranteed that the focus of the tree is a block that only contains a struct with no embedded values.

Embedded values have been applied to the fields of the struct.
-}
reduceStruct :: (ReduceMonad s r m) => m ()
reduceStruct = do
  whenBlock
    ( \(block, s) -> do
        -- Close the struct if the tree is closed.
        t <- getTMTree
        let
          isClosed = treeRecurClosed t
        when isClosed $
          -- Use modifyTMTN instead of mkNewTree because tree attributes need to be preserved, such as
          -- treeRecurClosed.
          modifyTMTN (TNBlock $ modifyBlockStruct (const s{stcClosed = True}) block)
    )
  whenBlock (\(blk, _) -> mapM_ validateLetName (Map.keys $ blkBindings blk))
  -- reduce the labels of the dynamic fields first. If the dynfields become actual fields, later they will be
  -- reduced.
  whenBlock
    ( \(blk, _) ->
        mapM_
          ( \(i, _) -> do
              -- Inserting reduced dynamic field element into the struct is handled by propUpStructPost.
              inSubTM (BlockTASeg (DynFieldTASeg i 0)) reduce
              -- we will reduce every fields, so no need to return affected labels.
              void $ handleStructMutObjChange (DynFieldTASeg i 0)
          )
          (IntMap.toList $ blkDynFields blk)
    )
  whenBlock
    ( \(blk, _) ->
        mapM_
          ( \(i, _) -> do
              -- pattern value should never be reduced because the references inside the pattern value should only
              -- be resolved in the unification node of the static field.
              -- See unify for more details.
              -- reduced constraint will constrain fields, which is done in the propUpStructPost.
              inSubTM (BlockTASeg (PatternTASeg i 0)) reduce
              void $ handleStructMutObjChange (PatternTASeg i 0)
          )
          (IntMap.toList $ blkCnstrs blk)
    )
  -- Add the unreferred let bindings to the unreferred let bindings.
  whenBlock
    ( \(blk, _) -> do
        tc <- getTMCursor
        mapM_
          ( \(k, lb) ->
              unless (lbReferred lb) $
                addRMUnreferredLet (appendSeg (tcCanAddr tc) (BlockTASeg (LetTASeg (TE.encodeUtf8 k))))
          )
          (Map.toList $ blkBindings blk)

        unrefLets <- getRMUnreferredLets
        debugInstantTM "reduceBlock" (printf "unrefLets: %s" (show unrefLets))
    )
  -- Reduce all fields.
  whenBlock
    (\(_, s) -> mapM_ reduceStructField (Map.keys . stcFields $ s))
  -- Set the struct as concrete if all fields are concrete.
  whenBlock
    ( \(block, s) -> do
        -- According to the spec,
        -- A value is concrete if it is either an atom, or a struct whose field values are all concrete, recursively.
        let isStructConcrete =
              foldl
                (\acc field -> acc && isJust (rtrConcrete $ ssfValue field))
                True
                (Map.elems . stcFields $ s)
                -- dynamic fields must have concrete labels.
                && foldl
                  (\acc field -> acc && isJust (rtrConcrete $ dsfLabel field))
                  True
                  (IntMap.elems . blkDynFields $ block)
            newStruct = s{stcIsConcrete = isStructConcrete}
            newBlock = block{blkValue = BlockStruct newStruct}
        modifyTMTN (TNBlock newBlock)
    )

whenBlock :: (ReduceMonad s r m) => ((Block, Struct) -> m ()) -> m ()
whenBlock f = do
  t <- getTMTree
  case treeNode t of
    TNBlock block@(IsBlockStruct struct) -> f (block, struct)
    -- The struct might have been turned to another type due to embedding.
    _ -> return ()

validateLetName :: (ReduceMonad s r m) => T.Text -> m ()
validateLetName name =
  whenBlock
    ( \_ -> do
        tc <- getTMCursor
        -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make sure
        -- in the parent scope that there is no field with the same name.
        parResM <- searchTCIdentInPar name tc
        case parResM of
          -- If the let binding with the name is found in the scope.
          Just (_, True) -> putTMTree $ lbRedeclErr name
          -- If the field with the same name is found in the scope.
          Just (_, False) -> putTMTree $ aliasErr name
          _ -> return ()
    )

aliasErr :: T.Text -> Tree
aliasErr name = mkBottomTree $ printf "can not have both alias and field with name %s in the same scope" name

lbRedeclErr :: T.Text -> Tree
lbRedeclErr name = mkBottomTree $ printf "%s redeclared in same scope" name

reduceStructField :: (ReduceMonad s r m) => T.Text -> m ()
reduceStructField name = do
  whenBlock
    ( \(_, _) -> do
        tc <- getTMCursor
        -- Fields and let bindings are made exclusive in the same scope in the evalExpr step, so we only need to make
        -- sure in the parent scope that there is no field with the same name.
        parResM <- searchTCIdentInPar name tc

        case parResM of
          -- If the let binding with the name is found in the scope.
          Just (_, True) -> putTMTree $ aliasErr name
          _ -> return ()
    )
  whenBlock
    (\(_, _) -> inSubTM (BlockTASeg (StringTASeg (TE.encodeUtf8 name))) reduce)

{- | Handle the post process of the mutable object change in the struct.

It increases the global version. Later when we reduce the fields of the updated struct, the fields will be assigned with
the new global version. If a field "a" references another field "b" in the same struct, but the evaluation order is
["a", "b"], after reducing the "a" field, the "a"'s refVers value will still be the old version of the "b" field. Later
once the "b" is reduced, it will trigger the re-reduction of the "a" field.

The focus of the tree must be a struct.
-}
handleStructMutObjChange :: (ReduceMonad s r m) => BlockTASeg -> m [T.Text]
handleStructMutObjChange seg = do
  stc <- getTMCursor
  let focus = tcFocus stc
  case focus of
    IsBlock blk@(IsBlockStruct _struct)
      | DynFieldTASeg i _ <- seg -> debugSpanTM
          (printf "handleStructMutObjChange, seg: %s" (show seg))
          $ do
            -- void increaseRMGlobalVers
            (remAffStruct, remAffLabels) <- removeAppliedObject i blk stc
            let
              dsf = blkDynFields blk IntMap.! i
              rE = dynFieldToStatic remAffStruct dsf
              allCnstrs = IntMap.elems $ blkCnstrs blk

            debugInstantTM "handleStructMutObjChange" (printf "dsf: %s, rE: %s" (show dsf) (show rE))

            either
              ( \err -> do
                  modifyTMTN (treeNode err)
                  return []
              )
              ( \labelFieldM -> do
                  -- Constrain the dynamic field with all existing constraints.
                  (addAffFields, addAffLabels) <-
                    maybe
                      (return ([], []))
                      ( \(name, field) -> do
                          newField <- constrainFieldWithCnstrs name field allCnstrs stc
                          return
                            ( [(name, newField)]
                            , if not (null $ ssfObjects newField) then [name] else []
                            )
                      )
                      labelFieldM

                  let
                    -- TODO: dedup
                    affectedLabels = remAffLabels ++ addAffLabels
                    newBlock =
                      ( TNBlock $
                          blk
                            { blkValue = BlockStruct $ updateStructWithFields addAffFields remAffStruct
                            }
                      )
                  modifyTMTN newBlock
                  debugInstantTM
                    "handleStructMutObjChange"
                    (printf "-: %s, +: %s, all: %s" (show remAffLabels) (show addAffFields) (show affectedLabels))

                  return affectedLabels
              )
              rE
      | PatternTASeg i _ <- seg -> debugSpanTM
          (printf "handleStructMutObjChange, seg: %s" (show seg))
          $ do
            -- void increaseRMGlobalVers
            -- Constrain all fields with the new constraint if it exists.
            let cnstr = blkCnstrs blk IntMap.! i
            -- New constraint might have the following effects:
            -- A. It matches fewer fields than the previous constraint with narrower constraints.
            -- -----
            -- abcde
            --   +++
            -- In the above example, we need to do
            -- 1. Remove the constraint for a,b
            -- 2. Do nothing for c,d,e
            --
            -- B. It could also match more fields when the constraint just got reduced to a concrete pattern.

            (remAffStruct, remAffLabels) <- removeAppliedObject i blk stc
            (newStruct, addAffLabels) <- applyMoreCnstr cnstr remAffStruct stc
            let
              affectedLabels = remAffLabels ++ addAffLabels
              newBlock = TNBlock $ blk{blkValue = BlockStruct newStruct}
            modifyTMTN newBlock
            unless (null affectedLabels) $
              debugInstantTM
                "handleStructMutObjChange"
                ( printf
                    "-: %s, +: %s, new struct: %s"
                    (show remAffLabels)
                    (show addAffLabels)
                    (show $ mkStructTree newStruct)
                )

            return affectedLabels
      | EmbedTASeg i <- seg -> debugSpanTM
          (printf "handleStructMutObjChange, seg: %s" (show seg))
          $ do
            -- void increaseRMGlobalVers
            let embed = blkEmbeds blk IntMap.! i
            rmdEmbedStruct <- case embValue embed of
              IsBlock embBlock@(IsBlockStruct _) -> do
                let rmIDs = i : (IntMap.keys (blkCnstrs embBlock) ++ IntMap.keys (blkDynFields embBlock))
                (allRmStruct, _) <-
                  foldM
                    ( \(accStruct, accLabels) idx -> do
                        (s, affLabels) <- removeAppliedObject idx blk{blkValue = BlockStruct accStruct} stc
                        return (s, affLabels ++ accLabels)
                    )
                    (_struct, [])
                    rmIDs

                return allRmStruct
              -- If the embedded value is not a struct, which could be a comprehension, then we only need to remove the
              -- object.
              _ -> fst <$> removeAppliedObject i blk stc

            let newBlock = blk{blkValue = BlockStruct rmdEmbedStruct}
            modifyTMTN (TNBlock newBlock)
            debugInstantTM "handleStructMutObjChange" (printf "new struct: %s" (show newBlock))

            pconjs <- discoverPConjs
            tc <- getTMCursor
            rpconjs <- resolvePendingConjuncts pconjs tc
            mergedM <- handleResolvedPConjsForStruct rpconjs tc
            case mergedM of
              Nothing -> return []
              Just merged -> do
                handleBlockReducedRes merged
                t <- getTMTree
                return $ case t of
                  IsBlock (IsBlockStruct resStruct) -> Map.keys $ stcFields resStruct
                  _ -> []

    -- merged <- unifyNormalizedTCs [structTC] structTC
    -- utc <- handleBlockReducedRes (tcFocus structTC) (merged `setTCFocus` structTC)
    -- return
    --   ( utc
    --   , case treeNode (tcFocus utc) of
    --       -- Currently we have to re-reduce all fields because unify does not return the reduced fields.
    --       TNBlock (IsBlockStruct resStruct) -> Map.keys $ stcFields resStruct
    --       _ -> []
    --   )
    _ -> return []

getLabelFieldPairs :: Struct -> [(T.Text, Field)]
getLabelFieldPairs struct = Map.toList $ stcFields struct

{- | Convert a dynamic field to a static field.

It returns a pair which contains reduced string and the newly created/updated field.
-}
dynFieldToStatic :: Struct -> DynamicField -> Either Tree (Maybe (T.Text, Field))
dynFieldToStatic struct df
  | Just s <- rtrString label = mkField s
  | Just _ <- rtrBottom label = Left label
  -- Incomplete field label, no change is made. If the mutable was a reference with string value, then it would
  -- have been reduced to a string.
  | Nothing <- rtrNonUnion label = return Nothing
  | otherwise = Left (mkBottomTree "label can only be a string")
 where
  label = dsfLabel df
  mkField s =
    let
      unifier l r = mkMutableTree $ mkUnifyOp [l, r]
      newSF = dynToField df (lookupStructField s struct) unifier
     in
      return (Just (s, newSF))

{- | Apply pattern constraints ([pattern]: constraint) to the static field.

Returns the new field. If the field is not matched with the pattern, it returns the original field.
-}
constrainFieldWithCnstrs :: (ResolveMonad s r m) => T.Text -> Field -> [StructCnstr] -> TrCur -> m Field
constrainFieldWithCnstrs name field cnstrs tc =
  foldM
    ( \accField cnstr -> do
        (newField, _) <- bindFieldWithCnstr name accField cnstr tc
        return newField
    )
    field
    cnstrs

{- | Bind the pattern constraint ([pattern]: constraint) to the static field if the field name matches the pattern.

If the field name matches the pattern, it returns the new unify function node, which is constraint & field.
Otherwise, return the original field.

The field should not have been applied with the constraint before.

It can run in any kind of node.
-}
bindFieldWithCnstr :: (ResolveMonad s r m) => T.Text -> Field -> StructCnstr -> TrCur -> m (Field, Bool)
bindFieldWithCnstr name field cnstr tc = do
  let selPattern = scsPattern cnstr

  matched <- patMatchLabel selPattern name tc

  let
    fval = ssfValue field
    op = mkMutableTree $ mkUnifyOp [fval, scsValue cnstr]
    -- TODO: comment on why mkCnstredValTree is used.
    -- op = mkMutableTree $ mkUnifyOp [fval, mkCnstredValTree (scsValue cnstr) Nothing]
    newField =
      if matched
        then field{ssfValue = op, ssfObjects = Set.insert (scsID cnstr) (ssfObjects field)}
        else field

  return (newField, matched)

{- | Update the struct with the constrained result.

If the constrained result introduce new fields that are not in the struct, then they are ignored.
-}
updateStructWithCnstredRes ::
  -- | The constrained result is a list of tuples that contains the name of the field, the field.
  [(T.Text, Field)] ->
  Struct ->
  Struct
updateStructWithCnstredRes res struct =
  foldr
    ( \(name, newField) acc ->
        maybe
          acc
          (\_ -> updateStructField name newField acc)
          (lookupStructField name struct)
    )
    struct
    res

-- | Filter the names that are matched with the constraint's pattern.
filterMatchedNames :: (ResolveMonad s r m) => StructCnstr -> [T.Text] -> TrCur -> m [T.Text]
filterMatchedNames cnstr labels tc =
  foldM
    ( \acc name -> do
        matched <- patMatchLabel (scsPattern cnstr) name tc
        return $ if matched then name : acc else acc
    )
    []
    labels

{- | Remove the applied object from the fields.

Returns the updated struct and the list of labels whose fields are affected.

This is done by re-applying existing objects except the one that is removed because unification is a lossy operation.
-}
removeAppliedObject :: (ResolveMonad s r m) => Int -> Block -> TrCur -> m (Struct, [T.Text])
removeAppliedObject objID blk@(IsBlockStruct struct) tc = debugSpanSimpleRM "removeAppliedObject" tc $ do
  (remAffFields, removedLabels) <-
    foldM
      ( \(accUpdated, accRemoved) (name, field) -> do
          let
            newObjectIDs = Set.delete objID (ssfObjects field)
            newCnstrs = IntMap.filterWithKey (\k _ -> k `Set.member` newObjectIDs) allCnstrs
            newDyns = IntMap.filterWithKey (\k _ -> k `Set.member` newObjectIDs) allDyns
            baseRawM = ssfValue <$> Map.lookup name (blkStaticFields blk)
          debugInstantRM
            "removeAppliedObject"
            ( printf
                "field: %s, objID: %s, newObjectIDs: %s, raw: %s"
                name
                (show objID)
                (show $ Set.toList newObjectIDs)
                (show baseRawM)
            )
            tc

          case baseRawM of
            Just raw -> do
              let
                rawField = field{ssfValue = raw, ssfObjects = Set.empty}
                fieldWithDyns =
                  foldr
                    (\dyn acc -> dynToField dyn (Just acc) unifier)
                    rawField
                    (IntMap.elems newDyns)
              newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems newCnstrs) tc
              return ((name, newField) : accUpdated, accRemoved)
            -- The field is created by a dynamic field, so it does not have a base raw.
            _ ->
              if null newDyns
                -- If there are no dynamic fields left, then the field should be removed.
                then return (accUpdated, name : accRemoved)
                else do
                  let
                    dyns = IntMap.elems newDyns
                    startField = field{ssfValue = dsfValue $ head dyns}
                    fieldWithDyns =
                      foldr
                        (\dyn acc -> dynToField dyn (Just acc) unifier)
                        startField
                        (tail dyns)
                  newField <- constrainFieldWithCnstrs name fieldWithDyns (IntMap.elems newCnstrs) tc
                  return ((name, newField) : accUpdated, accRemoved)
      )
      ([], [])
      (fieldsUnifiedWithObject objID $ Map.toList $ stcFields struct)
  let res = removeStructFieldsByNames removedLabels $ updateStructWithFields remAffFields struct
  return (res, map fst remAffFields)
 where
  allCnstrs = blkCnstrs blk
  allDyns = blkDynFields blk
  unifier l r = mkMutableTree $ mkUnifyOp [l, r]

  -- Find the fields that are unified with the object
  fieldsUnifiedWithObject :: Int -> [(T.Text, Field)] -> [(T.Text, Field)]
  fieldsUnifiedWithObject j =
    foldr (\(k, field) acc -> if j `elem` ssfObjects field then (k, field) : acc else acc) []
removeAppliedObject _ _ _ = throwErrSt "removeAppliedObject: focus is not a struct"

-- | Apply the additional constraint to the fields.
applyMoreCnstr :: (ResolveMonad s r m) => StructCnstr -> Struct -> TrCur -> m (Struct, [T.Text])
applyMoreCnstr cnstr struct tc = debugSpanSimpleRM "applyMoreCnstr" tc $ do
  (addAffFields, addAffLabels) <-
    foldM
      ( \(accFields, accLabels) (name, field) -> do
          (nf, isMatched) <- bindFieldWithCnstr name field cnstr tc
          if isMatched
            then return ((name, nf) : accFields, name : accLabels)
            else return (accFields, accLabels)
      )
      ([], [])
      (getLabelFieldPairs struct)
  let newStruct = updateStructWithFields addAffFields struct
  return (newStruct, addAffLabels)

reduceDisj :: (ReduceMonad s r m) => Disj -> m ()
reduceDisj d = do
  -- We have to reduce all disjuncts because they might be generated by merging one disjunction with another value.
  mapM_
    (\(i, _) -> inSubTM (DisjRegTASeg i) reduce)
    (zip [0 ..] (dsjDisjuncts d))

  tc <- getTMCursor
  case treeNode (tcFocus tc) of
    TNDisj nd -> do
      newDisjT <- normalizeDisj nd tc
      modifyTMTN (treeNode newDisjT)
    _ -> return ()

reduceList :: (ReduceMonad s r m) => List -> m ()
reduceList l = do
  r <-
    foldM
      ( \acc (i, origElem) -> do
          r <- inSubTM (IndexTASeg i) (reduce >> getTMTree)
          case origElem of
            -- If the element is a comprehension and the result of the comprehension is a list, per the spec, we insert
            -- the elements of the list into the list at the current index.
            IsMutable (MutOp (Compreh cph))
              | cphIsListCompreh cph
              , Just rList <- rtrList r ->
                  return $ acc ++ lstSubs rList
            _ -> return $ acc ++ [r]
      )
      []
      (zip [0 ..] (lstSubs l))
  putTMTree $ mkListTree r

-- | Closes a struct when the tree has struct.
resolveCloseFunc :: (ResolveMonad s r m) => [Tree] -> TrCur -> m (Maybe Tree)
resolveCloseFunc args _
  | length args /= 1 = throwErrSt $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      let arg = head args
      return $ Just $ closeTree arg

-- | Close a struct when the tree has struct.
closeTree :: Tree -> Tree
closeTree a =
  case treeNode a of
    TNBlock b -> setTN a $ TNBlock $ modifyBlockStruct (\s -> s{stcClosed = True}) b
    TNDisj dj ->
      let
        dft = closeTree <$> dsjDefault dj
        ds = map closeTree (dsjDisjuncts dj)
       in
        setTN a $ TNDisj (dj{dsjDefault = dft, dsjDisjuncts = ds})
    -- TODO: Mutable should be closed.
    -- TNMutable _ -> throwErrSt "TODO"
    _ -> mkBottomTree $ printf "cannot use %s as struct in argument 1 to close" (show a)

{- | Discover conjuncts from a tree node that contains conjuncts as its children.

It reduces every conjunct node it finds.
-}
discoverPConjs :: (ReduceMonad s r m) => m [Maybe TrCur]
discoverPConjs = discoverPConjsOpt True

{- | Discover conjuncts from a tree node that contains conjuncts as its children without reducing them.

It should be used after reduceArgs has been called.
-}
discoverPConjsFromTC :: (ResolveMonad s r m) => TrCur -> m [Maybe TrCur]
discoverPConjsFromTC tc = do
  curCtx <- getRMContext
  (a, updated) <- runStateT (discoverPConjsOpt False) (RTCState tc curCtx)
  modify $ \s -> setContext s (rtsCtx updated)
  return a

-- | Discover conjuncts from a tree node that contains conjuncts as its children.
discoverPConjsOpt :: (ReduceMonad s r m) => Bool -> m [Maybe TrCur]
discoverPConjsOpt toReduce = debugSpanAdaptTM "discoverPConjs" adapt $ do
  conjTC <- getTMCursor
  case tcFocus conjTC of
    IsMutable (MutOp (UOp _)) -> discoverPConjsFromUnifyOp toReduce
    IsBlock _ -> discoverPConsjFromBlkConj toReduce
    _ -> do
      when toReduce reduce
      vM <- rtrNonMut <$> getTMTree
      return [maybe Nothing (Just . (`setTCFocus` conjTC)) vM]
 where
  adapt xs = toJSON (map (fmap (oneLinerStringOfCurTreeState . tcFocus)) xs)

{- | Discover pending conjuncts from a unify operation.

It recursively discovers conjuncts from the unify operation and its arguments.

It reduces any mutable argument it finds.
-}
discoverPConjsFromUnifyOp :: (ReduceMonad s r m) => Bool -> m [Maybe TrCur]
discoverPConjsFromUnifyOp toReduce = do
  tc <- getTMCursor
  case tc of
    TCFocus (IsMutable mut@(MutOp (UOp _))) -> do
      -- A conjunct can be incomplete. For example, 1 & (x + 1) resulting an atom constraint.
      foldM
        ( \acc (i, _) -> do
            subs <- inSubTM (MutArgTASeg i) (discoverPConjsOpt toReduce)
            return (acc ++ subs)
        )
        []
        (zip [0 ..] (toList $ getMutArgs mut))
    _ -> throwErrSt "discoverPConjsFromUnifyOp: not a mutable unify operation"

discoverPConsjFromBlkConj :: (ReduceMonad s r m) => Bool -> m [Maybe TrCur]
discoverPConsjFromBlkConj toReduce = do
  tc <- getTMCursor
  case tc of
    TCFocus (IsBlock blk) -> do
      -- If the struct is a sole conjunct of a unify operation, it will have its embedded values as newly discovered
      -- conjuncts. For example, x: {a: 1, b} -> x: {a: 1} & b
      -- If it is not, it can still have embedded values. For example, x: {a: 1, b} & {} -> x: {a:1} & b & {}
      -- Either way, we try to normalize the embedded values.
      embeds <-
        foldM
          ( \acc i -> do
              subs <- inSubTM (BlockTASeg (EmbedTASeg i)) (discoverPConjsOpt toReduce)
              return (acc ++ subs)
          )
          []
          (IntMap.keys $ blkEmbeds blk)

      if hasEmptyFields blk && not (null $ blkEmbeds blk)
        -- If the struct is an empty struct with only embedded values, we can just return the embedded values.
        then return embeds
        else do
          -- Since we have normalized the embedded values, we need to remove them from the struct to prevent
          -- normalizing them again, causing infinite loop.
          let pureStructTC = setTCFocusTN (TNBlock $ blk{blkEmbeds = IntMap.empty}) tc
          -- TODO: there seems no need to reduce the pure struct.
          -- reducedPureStruct <- reduce pureStructTC
          return (Just pureStructTC : embeds)
    _ -> throwErrSt "discoverPConsjFromBlkConj: not a block"

data ResolvedPConjuncts
  = -- | AtomCnstrConj is created if one of the pending conjuncts is an atom and the runtime parameter
    -- 'rpCreateCnstr' is True.
    AtomCnstrConj AtomCnstr
  | ResolvedConjuncts [TrCur]
  | IncompleteConjuncts
  deriving (Show)

{- | Resolve pending conjuncts.

The tree cursor must be the unify operation node.
-}
resolvePendingConjuncts :: (ResolveMonad s r m) => [Maybe TrCur] -> TrCur -> m ResolvedPConjuncts
resolvePendingConjuncts pconjs tc = do
  RuntimeParams{rpCreateCnstr = cc} <- asks (cfRuntimeParams . getConfig)
  let r =
        foldr
          ( \pconj acc -> case acc of
              ResolvedConjuncts xs -> case tcFocus <$> pconj of
                Nothing -> IncompleteConjuncts
                Just (IsAtom a)
                  | cc -> AtomCnstrConj (AtomCnstr a (tcFocus tc))
                Just _ -> ResolvedConjuncts (fromJust pconj : xs)
              IncompleteConjuncts -> case tcFocus <$> pconj of
                -- If we discover an atom conjunct, we can ignore the incomplete conjuncts.
                Just (IsAtom a)
                  | cc -> AtomCnstrConj (AtomCnstr a (tcFocus tc))
                _ -> IncompleteConjuncts
              _ -> acc
          )
          (ResolvedConjuncts [])
          pconjs
  debugInstantRM "resolvePendingConjuncts" (printf "resolved: %s" (show r)) tc
  return r

resolveDisjOp :: (ResolveMonad s r m) => Bool -> TrCur -> m (Maybe Tree)
resolveDisjOp asConj disjOpTC@(TCFocus (IsMutable (MutOp (DisjOp disjOp)))) =
  debugSpanMTreeRM "resolveDisjOp" disjOpTC $ do
    let terms = toList $ djoTerms disjOp
    when (length terms < 2) $
      throwErrSt $
        printf "disjunction operation requires at least 2 terms, got %d" (length terms)

    debugInstantRM "resolveDisjOp" (printf "terms: %s" (show terms)) disjOpTC
    disjuncts <- procMarkedTerms asConj terms

    debugInstantRM "resolveDisjOp" (printf "disjuncts: %s" (show disjuncts)) disjOpTC
    if null disjuncts
      -- If none of the disjuncts are ready, return Nothing.
      then return Nothing
      else do
        let d = emptyDisj{dsjDisjuncts = disjuncts}
        r <- normalizeDisj d disjOpTC
        return $ Just r
resolveDisjOp _ _ = throwErrSt "resolveDisjOp: focus is not a disjunction operation"

{- | Normalize the disjunction.

1. Flatten the disjunction.
2. Deduplicate the disjuncts.
3. Remove the bottom disjuncts.
4. If the disjunct is left with only one element, return the value.
5. If the disjunct is left with no elements, return the first bottom it found.
-}
normalizeDisj :: (ResolveMonad r s m) => Disj -> TrCur -> m Tree
normalizeDisj d tc = debugSpanTreeRM "normalizeDisj" tc $ do
  debugInstantRM "normalizeDisj" (printf "before: %s" (show $ mkDisjTree d)) tc
  flattened <- flattenDisjunction d
  debugInstantRM
    "normalizeDisj"
    (printf "flattened: %s, flattened disjuncts: %s" (show $ mkDisjTree flattened) (show $ dsjDisjuncts flattened))
    tc
  final <- delUnwantedDisjuncts flattened tc
  let
    finalDisjs = dsjDisjuncts final
   in
    return
      if
        | null finalDisjs -> head $ filter (\case IsBottom _ -> True; _ -> False) (dsjDisjuncts flattened)
        -- When there is only one disjunct and the disjunct is not default, the disjunction is converted to the disjunct.
        | length finalDisjs == 1 && null (dsjDefIndexes final) -> head finalDisjs
        | otherwise -> mkDisjTree $ buildDefVal mkDisjTree final

{- | Flatten the disjunction.

Because disjunction operation is associative, we can flatten the disjuncts. The nested disjunctions were like
parenthesized disjunctions. For example, (a | *b) | c | (d | e) = a | *b | c | d | e.

Notice before this step, there is no marked terms in the disjunction. For example, *(a | *b) has been reduced to (a |
*b).

This handles the case where a marked term is a reference. For example the f of the *f | v1 would be <f, f> if we use the
value-default pair. When the value of the f changes to a disjunction like *1 | 2, the flattened disjuncts would be 1 and
2 with the default index of di, where di is the index of the disjunct f. When the value of f changes to 1 | 2, the
flattened disjuncts would be 1 and 2 with the default indexes of di and di + 1.

It also follows the rules of disjunction operation:
D0: ⟨v1⟩ | ⟨v2⟩         => ⟨v1|v2⟩
D1: ⟨v1, d1⟩ | ⟨v2⟩     => ⟨v1|v2, d1⟩
D2: ⟨v1, d1⟩ | ⟨v2, d2⟩ => ⟨v1|v2, d1|d2⟩

TODO: more efficiency
-}
flattenDisjunction :: (ResolveMonad r s m) => Disj -> m Disj
flattenDisjunction (Disj{dsjDefIndexes = idxes, dsjDisjuncts = disjuncts}) = do
  debugInstantOpRM
    "flattenDisjunction"
    (printf "before disjuncts: %s" (show $ map treeToRepString disjuncts))
    emptyTreeAddr

  -- Use foldl because the new default indexes are based on the length of the accumulated disjuncts.
  (newIndexes, newDisjs) <- foldM flatten ([], []) (zip [0 ..] disjuncts)
  return $ emptyDisj{dsjDefIndexes = newIndexes, dsjDisjuncts = newDisjs}
 where
  origDefIdxesSet = Set.fromList idxes
  -- Suppose we are processing the ith disjunct, and we have accumulated the disjuncts xs.
  -- If the ith disjunct is not a disjunction, then we can just add it to the disjuncts. We also need to add the index
  -- to the default indexes if it belongs to the default disjunction.
  flatten (accIs, accDs) (origIdx, t) = do
    debugInstantOpRM
      "flattenDisjunction"
      (printf "each: %s" (show t))
      emptyTreeAddr
    case rtrDisj t of
      Just sub -> do
        Disj{dsjDefIndexes = subDefIndexes, dsjDisjuncts = subDisjs} <- flattenDisjunction sub
        let
          -- Add offset to the indexes of the new disjuncts. The offset is the length of the accumulated disjuncts.
          newDefIndexes =
            -- If no sub defaults found for the disjunct but the disjunct is a default disjunct, that means the
            -- disjunct has been flattened to multiple disjuncts.
            if null subDefIndexes && origIdx `Set.member` origDefIdxesSet
              then map (+ length accDs) [0 .. length subDisjs - 1]
              else map (+ length accDs) subDefIndexes
        return (accIs ++ newDefIndexes, accDs ++ subDisjs)
      _ ->
        return
          ( if origIdx `Set.member` origDefIdxesSet
              -- The index of the new disjunct is the length of the accumulated disjuncts.
              then accIs ++ [length accDs]
              else accIs
          , accDs ++ [t]
          )

{- | Remove or rewrite unwanted disjuncts.

Unwanted disjuncts include:

* duplicate default disjuncts
* duplicate disjuncts
* bottom disjuncts

TODO: consider make t an instance of Ord and use Set to remove duplicates.
-}
delUnwantedDisjuncts :: (ResolveMonad r s m) => Disj -> TrCur -> m Disj
delUnwantedDisjuncts idisj@(Disj{dsjDefIndexes = dfIdxes, dsjDisjuncts = disjuncts}) tc =
  debugSpanArgsAdaptRM
    "delUnwantedDisjuncts"
    (show $ mkDisjTree idisj)
    (const Nothing)
    (\x -> toJSON $ oneLinerStringOfCurTreeState $ mkDisjTree x)
    tc
    $ do
      (newIndexes, newDisjs) <- foldM go ([], []) (zip [0 ..] disjuncts)
      return $ emptyDisj{dsjDefIndexes = newIndexes, dsjDisjuncts = newDisjs}
 where
  defValues = map (disjuncts !!) dfIdxes
  origDefIdxesSet = Set.fromList dfIdxes

  go (accIs, accXs) (idx, v) = do
    let djTC = mkSubTC (DisjRegTASeg idx) v tc
    pconjs <- discoverPConjsFromTC djTC
    resolved <- resolvePendingConjuncts pconjs djTC
    case resolved of
      ResolvedConjuncts xs -> do
        -- Remove the conjunct if it is a reference cycle and its segment is referable.
        let ys =
              filter
                ( \x -> case tcFocus x of
                    IsRefCycle
                      | Just True <- do
                          seg <- tcFocusSeg tc
                          return $ isSegReferable seg ->
                          False
                    _ -> True
                )
                xs
        debugInstantRM
          "delUnwantedDisjuncts"
          (printf "disjunct %d: %s, resolved to: %s" idx (show v) (show ys))
          tc
        case ys of
          [] -> return (accIs, accXs)
          [y] -> return $ updateDisjuncts (accIs, accXs) (idx, tcFocus y)
          _ -> do
            yM <- unifyNormalizedTCs ys djTC
            return $
              maybe
                (updateDisjuncts (accIs, accXs) (idx, v))
                (\y -> updateDisjuncts (accIs, accXs) (idx, y))
                yM
      _ -> return $ updateDisjuncts (accIs, accXs) (idx, v)

  updateDisjuncts (accIs, accXs) (idx, x) =
    let
      notAddedDisj = not (x `elem` accXs)
      -- If the disjunct is equal to the default value. Note that it does not mean the disjunct is the original default
      -- value.
      isValEqDef = x `elem` defValues
      -- The disjunct is kept if all of the following conditions are met:
      -- 1. it is not a bottom disjunct.
      -- 2. it is not added before
      -- 3. it is not a default value OR it is one of the default disjuncts and its index is in the original default
      -- indexes.
      -- The second condition makes sure the relative order of the default disjuncts is kept.
      -- For example, *b | c | a | b | *a should be reduced to <b | c | a, 0|2>.
      keepDisjunct =
        ( case x of
            IsBottom _ -> False
            IsRefCycle -> False
            _ -> True
        )
          && notAddedDisj
          && (not isValEqDef || idx `Set.member` origDefIdxesSet)
      -- The disjunct is default if it is one of the default disjuncts and it is not seen before.
      isDefIndex = keepDisjunct && isValEqDef
     in
      -- Add the current disjunct index to the default indexes if condition is met.
      ( if isDefIndex then accIs ++ [length accXs] else accIs
      , if keepDisjunct then accXs ++ [x] else accXs
      )

{- | Construct a list of disjuncts from the disjunction terms.

Some existing rules for marked disjunctions:
M0:  ⟨v⟩    => ⟨v⟩        don't introduce defaults for unmarked term
M1: *⟨v⟩    => ⟨v, v⟩     introduce identical default for marked term
M2: *⟨v, d⟩ => ⟨v, d⟩     keep existing defaults for marked term
M3:  ⟨v, d⟩ => ⟨v⟩        strip existing defaults from unmarked term
-}
procMarkedTerms :: (ResolveMonad s r m) => Bool -> [DisjTerm] -> m [Tree]
procMarkedTerms asConj terms = do
  -- disjoin operation allows incompleteness.

  -- let concreteTerms =
  --       -- If the disjunction is a conjunct, there is no need to reduce the terms.
  --       if asConj
  --         then terms
  --         else filter (isJust . rtrNonMut . dstValue) terms

  let hasMarked = any dstMarked terms
  return $
    foldr
      ( \term accDisjuncts ->
          let val = dstValue term
           in if
                -- Apply Rule M1 and M2
                | hasMarked && dstMarked term ->
                    setTN
                      val
                      ( TNDisj $
                          maybe
                            -- Rule M1
                            (emptyDisj{dsjDefIndexes = [0], dsjDisjuncts = [val]})
                            ( \d ->
                                if null (dsjDefIndexes d)
                                  -- Rule M1
                                  then d{dsjDefIndexes = [0 .. length (dsjDisjuncts d)]}
                                  -- Rule M2
                                  else d
                            )
                            (rtrDisj val)
                      )
                      : accDisjuncts
                -- Apply Rule M0 and M3
                | hasMarked ->
                    maybe
                      val
                      (\d -> setTN val $ TNDisj $ d{dsjDefIndexes = []})
                      (rtrDisj val)
                      : accDisjuncts
                | otherwise -> val : accDisjuncts
      )
      []
      terms

reduceCompreh :: (ResolveMonad s r m) => Comprehension -> TrCur -> m (Maybe Tree)
reduceCompreh cph tc = debugSpanMTreeRM "reduceCompreh" tc $ do
  r <- comprehend 0 cph tc (IterCtx 0 Map.empty (Right []))
  case icRes r of
    Left Nothing -> return Nothing
    Left (Just t) -> return $ Just t
    Right vs ->
      if cphIsListCompreh cph
        then return $ Just $ mkListTree vs
        else return $ Just $ case vs of
          [] -> mkBlockTree emptyBlock
          [x] -> x
          _ -> mkMutableTree $ mkUnifyOp vs

data IterCtx = IterCtx
  { icCnt :: Int
  , icBindings :: Map.Map T.Text Tree
  , icRes :: Either (Maybe Tree) [Tree]
  -- ^ It contains a list of resulted structs that are generated by each iteration.
  }
  deriving (Show)

{- | Iterate through the comprehension clauses.

The iteration is done in a depth-first manner. If all clauses are processed, it creates a new struct with the
bindings and adds the struct to the result list.
-}
comprehend :: (ResolveMonad s r m) => Int -> Comprehension -> TrCur -> IterCtx -> m IterCtx
comprehend i cph tc iterCtx
  -- The leaf case where the iteration is done.
  | i == length (cphClauses cph) = debugSpanSimpleRM
      (printf "reduceIterVal iter:%s" (show $ icCnt iterCtx))
      tc
      $ do
        let s = cphBlock cph
        r <- newIterStruct (icBindings iterCtx) s
        case icRes iterCtx of
          Left _ -> throwErrSt "should not reach the leaf node"
          Right vs -> return $ iterCtx{icRes = Right (vs ++ [r]), icCnt = icCnt iterCtx + 1}
  | otherwise = reduceClause i cph tc iterCtx

reduceClause = undefined

-- -- | Reduce the ith clause of the comprehension in the depth-first manner.
-- reduceClause :: (ResolveMonad s r m) => Int -> Comprehension -> TrCur -> IterCtx -> m IterCtx
-- reduceClause i cph tc iterCtx = debugSpanTreeArgsRM
--   (printf "reduceClause ith-clause: %s, iter:%s" (show i) (show $ icCnt iterCtx))
--   (printf "iterCtx: %s" (show iterCtx))
--   ( \x -> case icRes x of
--       Left v -> v
--       Right [] -> Nothing
--       Right vs -> Just $ last vs
--   )
--   tc
--   $ case cphClauses cph `Seq.index` i of
--     ComprehClauseLet letName v ->
--       comprehend (i + 1) cph tc (iterCtx{icBindings = Map.insert letName v (icBindings iterCtx)})
--     ComprehClauseIf _ -> do
--       argTC <- newClauseTC i (icBindings iterCtx) tc
--       tM <- reduceToNonMut argTC
--       case tM of
--         Nothing -> return $ iterCtx{icRes = Left Nothing}
--         Just t ->
--           case rtrAtom t of
--             Just (Bool True) -> comprehend (i + 1) cph tc iterCtx
--             -- Do not go to next clause if the condition is false.
--             Just (Bool False) -> return iterCtx
--             _ ->
--               return $
--                 iterCtx
--                   { icRes = Left $ Just $ mkBottomTree $ printf "%s is not a boolean" (showTreeSymbol t)
--                   }
--     ComprehClauseFor k vM _ -> do
--       argTC <- newClauseTC i (icBindings iterCtx) tc
--       tM <- reduceToNonMut argTC
--       case tM of
--         Nothing -> return $ iterCtx{icRes = Left Nothing}
--         Just t ->
--           if
--             -- TODO: only iterate optional fields
--             | IsBlock (IsBlockStruct struct) <- t ->
--                 foldM
--                   ( \acc (label, field) ->
--                       comprehend
--                         (i + 1)
--                         cph
--                         tc
--                         ( acc
--                             { icBindings =
--                                 Map.union
--                                   ( Map.fromList $
--                                       maybe
--                                         [(k, ssfValue field)]
--                                         ( \v ->
--                                             [ (k, mkAtomTree (String label))
--                                             , (v, ssfValue field)
--                                             ]
--                                         )
--                                         vM
--                                   )
--                                   (icBindings acc)
--                             }
--                         )
--                   )
--                   iterCtx
--                   (Map.toList $ stcFields struct)
--             | Just (List{lstSubs = list}) <- rtrList t ->
--                 foldM
--                   ( \acc (idx, element) ->
--                       comprehend
--                         (i + 1)
--                         cph
--                         tc
--                         ( acc
--                             { icBindings =
--                                 Map.union
--                                   ( Map.fromList $
--                                       maybe
--                                         [(k, element)]
--                                         ( \v ->
--                                             [ (k, mkAtomTree (Int idx))
--                                             , (v, element)
--                                             ]
--                                         )
--                                         vM
--                                   )
--                                   (icBindings acc)
--                             }
--                         )
--                   )
--                   iterCtx
--                   (zip [0 ..] list)
--             | otherwise ->
--                 return $
--                   iterCtx
--                     { icRes = Left $ Just $ mkBottomTree $ printf "%s is not iterable" (showTreeSymbol t)
--                     }

{- | Embed a value to a new block and return a new tree cursor that points to the embedded value.

The block segment is used to identify the new block.
-}
newClauseTC :: (ResolveMonad s r m) => Int -> Map.Map T.Text Tree -> TrCur -> m TrCur
newClauseTC i bindings tc@(TCFocus (IsMutable mut@(MutOp (Compreh cph)))) = goDownTCSegMust (MutArgTASeg i) newTC
 where
  newTC = setTCFocusTN (TNMutable (setMutOp (Compreh cph{cphIterBindings = bindings}) mut)) tc
newClauseTC _ _ _ = throwErrSt "newClauseTC can only be used with a mutable comprehension"

{- | Create a new struct with the given bindings.

The generated struct will not have comoprehensions, otherwise it will be reduced again, and the bindings will be lost.
-}
newIterStruct ::
  (ResolveMonad s r m) => Map.Map T.Text Tree -> Tree -> m Tree
newIterStruct bindings t@(IsBlock blk) =
  -- The original let bindings in the struct should take the precedence over the iteration bindings.
  return $
    setTN t $
      TNBlock $
        blk{blkBindings = Map.union (blkBindings blk) (Map.map (LetBinding True) bindings)}
newIterStruct _ _ = throwErrSt "newIterStruct can only be used with a block"

resolveInterpolation :: (ResolveMonad s r m) => Interpolation -> m (Maybe Tree)
resolveInterpolation l = do
  r <-
    foldM
      ( \accRes seg -> case seg of
          IplSegExpr j -> do
            let r = itpExprs l `Seq.index` j
            if
              | Just s <- rtrString r -> return $ (`T.append` s) <$> accRes
              | Just i <- rtrInt r -> return $ (`T.append` (T.pack $ show i)) <$> accRes
              | Just b <- rtrBool r -> return $ (`T.append` (T.pack $ show b)) <$> accRes
              | Just f <- rtrFloat r -> return $ (`T.append` (T.pack $ show f)) <$> accRes
              | Just _ <- rtrStruct r ->
                  return $
                    Left $
                      mkBottomTree $
                        printf "can not use struct in interpolation: %s" (showTreeSymbol r)
              | Just _ <- rtrList r ->
                  return $
                    Left $
                      mkBottomTree $
                        printf "can not use list in interpolation: %s" (showTreeSymbol r)
              | otherwise -> return undefined
          IplSegStr s -> return $ (`T.append` s) <$> accRes
      )
      (Right T.empty)
      (itpSegs l)
  case r of
    Left err -> return $ Just err
    Right res -> return $ Just $ mkAtomTree (String res)

{- | Check the labels' permission.

The focus of the tree must be a struct.
-}
checkLabelsPerm ::
  (ResolveMonad s r m) =>
  Set.Set T.Text ->
  IntMap.IntMap StructCnstr ->
  Bool ->
  Bool ->
  Set.Set T.Text ->
  TrCur ->
  m TrCur
checkLabelsPerm baseLabels baseCnstrs isBaseClosed isEitherEmbedded labelsSet tc =
  foldM
    ( \acc opLabel ->
        case tcFocus acc of
          IsBottom _ -> return acc
          _ ->
            checkPerm baseLabels baseCnstrs isBaseClosed isEitherEmbedded opLabel acc
              >>= maybe
                (return acc)
                -- If the checkPerm returns a bottom, update the bottom to the struct.
                (\err -> return (err `setTCFocus` acc))
    )
    tc
    labelsSet

checkPerm ::
  (ResolveMonad s r m) =>
  Set.Set T.Text ->
  IntMap.IntMap StructCnstr ->
  Bool ->
  Bool ->
  T.Text ->
  TrCur ->
  m (Maybe Tree)
checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel tc =
  debugSpanMTreeArgsRM
    "checkPerm"
    ( printf
        "newLabel: %s, baseLabels: %s, baseAllCnstrs: %s, isBaseClosed: %s, isEitherEmbedded: %s"
        (show newLabel)
        (show $ Set.toList baseLabels)
        (show $ IntMap.toList baseAllCnstrs)
        (show isBaseClosed)
        (show isEitherEmbedded)
    )
    tc
    $ _checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel tc

_checkPerm ::
  (ResolveMonad s r m) =>
  Set.Set T.Text ->
  IntMap.IntMap StructCnstr ->
  Bool ->
  Bool ->
  T.Text ->
  TrCur ->
  m (Maybe Tree)
_checkPerm baseLabels baseAllCnstrs isBaseClosed isEitherEmbedded newLabel tc
  | not isBaseClosed || isEitherEmbedded = return Nothing
  | newLabel `Set.member` baseLabels = return Nothing
  | otherwise = do
      -- A "new" field is allowed if there is at least one pattern that matches the field.
      allowed <-
        foldM
          ( \acc cnstr ->
              if acc
                then return acc
                else do
                  let pat = scsPattern cnstr
                  patMatchLabel pat newLabel tc
          )
          -- By default, "new" label is not allowed.
          False
          (IntMap.elems baseAllCnstrs)

      -- A field is disallowed if no pattern exists or no pattern matches the label.
      if allowed
        then return Nothing
        else return . Just $ mkBottomTree $ printf "%s is not allowed" newLabel

{- | Returns whether the pattern matches the label.

The pattern is expected to be an Atom or a Bounds.
-}
patMatchLabel :: (ResolveMonad s r m) => Tree -> T.Text -> TrCur -> m Bool
patMatchLabel pat name tc = debugSpanSimpleRM "patMatchLabel" tc $ do
  -- Retrieve the atom or bounds from the pattern.
  let vM = listToMaybe $ catMaybes [rtrAtom pat >>= Just . mkAtomTree, rtrBounds pat >>= Just . mkBoundsTree]
  maybe (return False) match vM
 where
  match :: (ResolveMonad s r m) => Tree -> m Bool
  match v = do
    let f = mergeBinUTrees (UTree L (v `setTCFocus` tc)) (UTree R (mkAtomTree (String name) `setTCFocus` tc)) tc
    -- We should not create constraints in this context because we should not delay the evaluation of the
    -- pattern.
    r <-
      local
        ( \r ->
            let conf = Common.getConfig r
             in Common.setConfig
                  r
                  conf
                    { Common.cfRuntimeParams = (Common.cfRuntimeParams conf){Common.rpCreateCnstr = False}
                    }
        )
        f
    -- Filter the strings from the results. Non-string results are ignored meaning the fields do not match the
    -- pattern.
    case rtrAtom r of
      Just (String _) -> return True
      _ -> return False
