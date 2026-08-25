{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Instances where

import Control.DeepSeq (NFData (..))
import Data.Aeson (ToJSON (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Vector as V
import EvalAddr
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (..))
import Syntax.AST (ASTNode (..))
import Text.Printf (printf)
import Value.Comprehension
import Value.Disj
import Value.DisjoinOp
import Value.Func
import Value.Interpolation
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.Val

-----
-- Eq
-----

deriving instance Eq Comprehension
deriving instance Eq ComprehArg

deriving instance Eq Reference
deriving instance Eq ValueSelect

deriving instance Eq Interpolation

deriving instance Eq DisjoinOp
deriving instance Eq DisjTerm

deriving instance Eq Op
deriving instance Eq RegularOp
deriving instance Eq FuncCall

instance Eq Struct where
  -- Struct values are equal if they have the same set of regular field labels and the corresponding values are
  -- recursively equal. Only regular fields are considered; field order and closedness are irrelevant.
  (==) s1 s2 = stcFields s1 == stcFields s2

instance Eq Field where
  (==) f1 f2 = f1.ssfValue == f2.ssfValue && f1.ssfAttr == f2.ssfAttr

deriving instance Eq DynamicField
deriving instance Eq StructCnstr

deriving instance Eq List
deriving instance Eq Disj

deriving instance Eq ValConstraint
deriving instance Eq OpConstraint
deriving instance Eq Constraint
deriving instance Eq ConstraintsSet

instance Eq Val where
  (==) (VStruct s1) (VStruct s2) = s1 == s2
  (==) (VList ts1) (VList ts2) = ts1 == ts2
  (==) (VDisj d1) (VDisj d2) = d1 == d2
  (==) (VAtom l1) (VAtom l2) = l1 == l2
  (==) (VBounds b1) (VBounds b2) = b1 == b2
  (==) (VBottom _) (VBottom _) = True
  (==) VTop VTop = True
  (==) VUnknown VUnknown = True
  (==) _ _ = False

instance Eq VNode where
  (==) t1 t2 = value t1 == value t2

-----
-- Show
-----

deriving instance Show Comprehension
deriving instance Show ComprehArg

instance Show Reference where
  show (Reference{ident}) = "ref_" ++ show ident

instance Show ValueSelect where
  show (ValueSelect{}) = "vselect"

deriving instance Show Interpolation

deriving instance Show DisjoinOp
deriving instance Show DisjTerm

instance ShowWTIndexer DisjTerm where
  tshow term = do
    marked <- tshow (dstMarked term)
    value <- tshow (dstValue term)
    return $ T.pack $ printf "DisjTerm{marked: %s, value: %s}" marked value

deriving instance Show Op
deriving instance Show RegularOp
deriving instance Show FuncCall

instance ShowWTIndexer ResolvedIdentAddr where
  tshow (ResolvedIdentFromTop addr) = do
    t <- tshow addr
    return $ "ResolvedIdentFromTop: " <> t
  tshow (ToTargetScopeDiff diff) = do
    t <- tshow diff
    return $ "ToTargetScopeDiff: " <> t

deriving instance Show Struct
deriving instance Show Field
deriving instance Show DynamicField
deriving instance Show StructCnstr

deriving instance Show List
deriving instance Show Disj

deriving instance Show Val
deriving instance Show VNode
deriving instance Show VTermNode

deriving instance Show ValConstraint
deriving instance Show OpConstraint
deriving instance Show Constraint
deriving instance Show ConstraintsSet

instance ShowWTIndexer VNode where
  tshow = oneLinerStringOfVNode

instance ShowWTIndexer Val where
  tshow vn = oneLinerStringOfVNode (mkValVN vn)

instance ToJSON VNode where
  toJSON t = toJSON (show t)

instance ToJSON Val where
  toJSON vn = toJSON (show (mkValVN vn))

instance ToJSONWTIndexer VNode where
  ttoJSON t = do
    s <- tshow t
    return $ toJSON s

instance ToJSONWTIndexer Val where
  ttoJSON vn = do
    s <- oneLinerStringOfVNode (mkValVN vn)
    return $ toJSON s

-----
-- NFData
-----

deriving instance NFData Comprehension
deriving instance NFData ComprehArg

deriving instance NFData Reference
deriving instance NFData ValueSelect

deriving instance NFData Interpolation

deriving instance NFData DisjoinOp
deriving instance NFData DisjTerm

deriving instance NFData Op
deriving instance NFData RegularOp
deriving instance NFData FuncCall

deriving instance NFData Struct
deriving instance NFData Field
deriving instance NFData DynamicField
deriving instance NFData StructCnstr

deriving instance NFData List
deriving instance NFData Disj

deriving instance NFData Val
deriving instance NFData VNode

deriving instance NFData ValConstraint
deriving instance NFData OpConstraint
deriving instance NFData Constraint
deriving instance NFData ConstraintsSet

-----
-- VTerm
-----

mapMVectorWAddr ::
  (Monad m) => (EvalAddr -> a -> m a) -> (Int -> AddrSegment) -> EvalAddr -> V.Vector a -> m (V.Vector a)
mapMVectorWAddr f g p = V.imapM (\i !v -> f (appendSeg p (g i)) v)

mapMSeqWAddr :: (Monad m) => (EvalAddr -> a -> m a) -> (Int -> AddrSegment) -> EvalAddr -> Seq.Seq a -> m (Seq.Seq a)
mapMSeqWAddr f g p = Seq.traverseWithIndex (\i !v -> f (appendSeg p (g i)) v)

mapMIntMapWAddr ::
  (Monad m) => (EvalAddr -> a -> m a) -> (Int -> AddrSegment) -> EvalAddr -> IntMap.IntMap a -> m (IntMap.IntMap a)
mapMIntMapWAddr f g p = IntMap.traverseWithKey (\i !v -> f (appendSeg p (g i)) v)

foldrVecWAddr :: (EvalAddr -> a -> r) -> (Int -> AddrSegment) -> EvalAddr -> V.Vector a -> [r]
foldrVecWAddr f g p = V.ifoldr (\i !v acc -> f (appendSeg p (g i)) v : acc) []

foldrSeqWAddr :: (EvalAddr -> a -> r) -> (Int -> AddrSegment) -> EvalAddr -> Seq.Seq a -> [r]
foldrSeqWAddr f g p = Seq.foldrWithIndex (\i !v acc -> f (appendSeg p (g i)) v : acc) []

foldrSeqWAddrConcat :: (EvalAddr -> a -> [r]) -> (Int -> AddrSegment) -> EvalAddr -> Seq.Seq a -> [r]
foldrSeqWAddrConcat f g p = Seq.foldrWithIndex (\i !v acc -> f (appendSeg p (g i)) v ++ acc) []

foldrIntMapWAddr :: (EvalAddr -> a -> r) -> (Int -> AddrSegment) -> EvalAddr -> IntMap.IntMap a -> [r]
foldrIntMapWAddr f g p = IntMap.foldrWithKey (\i !v acc -> f (appendSeg p (g i)) v : acc) []

foldrIntMapWAddrConcat :: (EvalAddr -> a -> [r]) -> (Int -> AddrSegment) -> EvalAddr -> IntMap.IntMap a -> [r]
foldrIntMapWAddrConcat f g p = IntMap.foldrWithKey (\i !v acc -> f (appendSeg p (g i)) v ++ acc) []

adaptVTMapQOnVNode :: (EvalAddr -> VTermNode -> r) -> EvalAddr -> VNode -> r
adaptVTMapQOnVNode f p v = f p (VTVNode v)

adaptVTMapQOnVal :: (EvalAddr -> VTermNode -> r) -> EvalAddr -> Val -> r
adaptVTMapQOnVal f p vn = f p (VTVal vn)

adaptVTMapMOnVNode :: (Monad m) => (EvalAddr -> VTermNode -> m VTermNode) -> EvalAddr -> VNode -> m VNode
adaptVTMapMOnVNode f p v = do
  vt' <- f p (VTVNode v)
  return $ vtVNodeOr id v vt'

adaptVTMapMOnVal :: (Monad m) => (EvalAddr -> VTermNode -> m VTermNode) -> EvalAddr -> Val -> m Val
adaptVTMapMOnVal f p v = do
  vt' <- f p (VTVal v)
  return $ vtValOr id v vt'

adaptVTMapTOnVal :: (EvalAddr -> VTermNode -> VTermNode) -> EvalAddr -> VNode -> VNode
adaptVTMapTOnVal f p v =
  let vt' = f p (VTVNode v)
   in vtVNodeOr id v vt'

instance VTerm VTermNode where
  vtmapQ f p (VTVal vn) = vtmapQ f p vn
  vtmapQ f p (VTVNode v) = vtmapQ f p v
  vtmapQ f p (VTOp op) = vtmapQ f p op
  vtmapQ f p (VTConstraintSeq constraints) = vtmapQ f p constraints
  vtmapM f p (VTVal vn) = VTVal <$> vtmapM f p vn
  vtmapM f p (VTVNode v) = VTVNode <$> vtmapM f p v
  vtmapM f p (VTOp op) = VTOp <$> vtmapM f p op
  vtmapM f p (VTConstraintSeq constraints) = VTConstraintSeq <$> vtmapM f p constraints
  getChildVT segment (VTVal value) = getChildVT segment value
  getChildVT segment (VTVNode node) = getChildVT segment node
  getChildVT segment (VTOp op) = getChildVT segment op
  getChildVT segment (VTConstraintSeq constraints) = getChildVT segment constraints
  setChildVT segment child (VTVal value) = VTVal <$> setChildVT segment child value
  setChildVT segment child (VTVNode node) = VTVNode <$> setChildVT segment child node
  setChildVT segment child (VTOp op) = VTOp <$> setChildVT segment child op
  setChildVT segment child (VTConstraintSeq constraints) =
    VTConstraintSeq <$> setChildVT segment child constraints

instance VTerm Val where
  vtmapQ f p (VStruct s) = vtmapQ f p s
  vtmapQ f p (VList l) = vtmapQ f p l
  vtmapQ f p (VDisj d) = vtmapQ f p d
  vtmapQ _ _ _ = []
  vtmapM f p (VStruct s) = VStruct <$> vtmapM f p s
  vtmapM f p (VList l) = VList <$> vtmapM f p l
  vtmapM f p (VDisj d) = VDisj <$> vtmapM f p d
  vtmapM _ _ a = return a
  getChildVT segment (VStruct struct) = getChildVT segment struct
  getChildVT segment (VList list) = getChildVT segment list
  getChildVT segment (VDisj disj) = getChildVT segment disj
  getChildVT _ _ = Nothing
  setChildVT segment child (VStruct struct) = VStruct <$> setChildVT segment child struct
  setChildVT segment child (VList list) = VList <$> setChildVT segment child list
  setChildVT segment child (VDisj disj) = VDisj <$> setChildVT segment child disj
  setChildVT _ _ _ = Nothing

instance VTerm VNode where
  vtmapQ f p v =
    f p (VTVal $ value v) : vtmapQ f p (constraints v)
  vtmapM f p v = do
    value' <- f p (VTVal $ value v)
    constraints' <- vtmapM f p (constraints v)
    return v{value = vtValOr id (value v) value', constraints = constraints'}
  getChildVT segment node = case addrSegmentTag segment of
    ConstraintTag -> getChildVT segment node.constraints
    DynCnstrTag -> getChildVT segment node.constraints
    OpArgTag -> getSoleOpChild segment node
    ObjectTag -> getSoleOpChild segment node
    _ -> getChildVT segment node.value
  setChildVT segment child node = case addrSegmentTag segment of
    ConstraintTag -> do
      constraints' <- setChildVT segment child node.constraints
      return node{constraints = constraints'}
    DynCnstrTag -> do
      constraints' <- setChildVT segment child node.constraints
      return node{constraints = constraints'}
    OpArgTag -> setSoleOpChild segment child node
    ObjectTag -> setSoleOpChild segment child node
    _ -> do
      value' <- setChildVT segment child node.value
      return node{value = value'}

getSoleOpChild :: AddrSegment -> VNode -> Maybe VTermNode
getSoleOpChild segment node = do
  opConstraint <- soleOpConstraintVT node
  getChildVT segment opConstraint.ocOp

setSoleOpChild :: AddrSegment -> VTermNode -> VNode -> Maybe VNode
setSoleOpChild segment child node = do
  opConstraint <- soleOpConstraintVT node
  op' <- setChildVT segment child opConstraint.ocOp
  return
    node
      { constraints =
          node.constraints
            { static = Seq.singleton $ OpCnstr opConstraint{ocOp = op'}
            }
      }

soleOpConstraintVT :: VNode -> Maybe OpConstraint
soleOpConstraintVT node = case node.constraints.static of
  OpCnstr opConstraint Seq.:<| Seq.Empty -> Just opConstraint
  _ -> Nothing

instance VTerm ConstraintsSet where
  vtmapQ f p c =
    foldrSeqWAddrConcat (vtmapQ f) (termStepToAddrSegment . mkRegCnstrTermStep) p (static c)
      ++ foldrIntMapWAddrConcat (vtmapQ f) (termStepToAddrSegment . mkDynCnstrTermStep) p (dynamic c)
  vtmapM f p c = do
    static' <- mapMSeqWAddr (vtmapM f) (termStepToAddrSegment . mkRegCnstrTermStep) p (static c)
    dynamic' <- mapMIntMapWAddr (vtmapM f) (termStepToAddrSegment . mkDynCnstrTermStep) p (dynamic c)
    return c{static = static', dynamic = dynamic'}
  getChildVT segment constraints = case addrSegmentTag segment of
    ConstraintTag -> do
      (_, constraint) <- lookupSeqBySegment ConstraintTag segment constraints.static
      return $ constraintToVT constraint
    DynCnstrTag -> do
      key <- termStepIndexFor DynCnstrTag segment
      VTConstraintSeq <$> IntMap.lookup key constraints.dynamic
    _ -> Nothing
  setChildVT segment child constraints = case addrSegmentTag segment of
    ConstraintTag -> do
      (index, original) <- lookupSeqBySegment ConstraintTag segment constraints.static
      replacement <- replaceConstraintVT child original
      return constraints{static = Seq.update index replacement constraints.static}
    DynCnstrTag -> do
      key <- termStepIndexFor DynCnstrTag segment
      _ <- IntMap.lookup key constraints.dynamic
      case child of
        VTConstraintSeq replacement ->
          return constraints{dynamic = IntMap.insert key replacement constraints.dynamic}
        _ -> Nothing
    _ -> Nothing

instance VTerm Constraint where
  vtmapQ f p c = case c of
    ValCnstr vc -> [f p (VTVal vc.vcVal)]
    OpCnstr oc -> [f p (VTOp oc.ocOp)]
    StructEmbedCnstr xs -> foldrSeqWAddrConcat (vtmapQ f) (termStepToAddrSegment . mkRegCnstrTermStep) p xs
  vtmapM f p c = case c of
    ValCnstr vc -> do
      vn' <- f p (VTVal vc.vcVal)
      return $ vtValOr (\v -> ValCnstr vc{vcVal = v}) c vn'
    StructEmbedCnstr xs -> StructEmbedCnstr <$> mapMSeqWAddr (vtmapM f) (termStepToAddrSegment . mkRegCnstrTermStep) p xs
    OpCnstr oc -> do
      ovt' <- f p (VTOp oc.ocOp)
      case ovt' of
        VTOp o' -> return $ OpCnstr oc{ocOp = o'}
        VTVal v -> return $ ValCnstr $ ValConstraint{vcLoc = oc.ocLoc, vcVal = v}
        _ -> return c

instance VTerm ConstraintSeq where
  vtmapQ f = foldrSeqWAddrConcat (vtmapQ f) (termStepToAddrSegment . mkRegCnstrTermStep)
  vtmapM f = mapMSeqWAddr (vtmapM f) (termStepToAddrSegment . mkRegCnstrTermStep)
  getChildVT segment constraints = do
    (_, constraint) <- lookupSeqBySegment ConstraintTag segment constraints
    return $ constraintToVT constraint
  setChildVT segment child constraints = do
    (index, original) <- lookupSeqBySegment ConstraintTag segment constraints
    replacement <- replaceConstraintVT child original
    return $ Seq.update index replacement constraints

constraintToVT :: Constraint -> VTermNode
constraintToVT constraint = case constraint of
  ValCnstr valConstraint -> VTVal valConstraint.vcVal
  OpCnstr opConstraint -> VTOp opConstraint.ocOp
  StructEmbedCnstr constraints -> VTConstraintSeq constraints

replaceConstraintVT :: VTermNode -> Constraint -> Maybe Constraint
replaceConstraintVT replacement original = case (replacement, original) of
  (VTVal value, ValCnstr valConstraint) ->
    Just $ ValCnstr valConstraint{vcVal = value}
  (VTOp op, OpCnstr opConstraint) ->
    Just $ OpCnstr opConstraint{ocOp = op}
  (VTVal value, OpCnstr opConstraint) ->
    Just $ ValCnstr ValConstraint{vcLoc = opConstraint.ocLoc, vcVal = value}
  (VTConstraintSeq constraints, StructEmbedCnstr _) ->
    Just $ StructEmbedCnstr constraints
  _ -> Nothing

instance VTerm Struct where
  vtmapQ f p s =
    let
      fieldQs = Map.foldrWithKey (\k v acc -> vtmapQ f (nf (mkStringFeature k)) v ++ acc) [] (stcFields s)
      bindingQs = Map.foldrWithKey (\k v acc -> f (nf (mkLetFeature k)) (VTVNode v) : acc) [] (stcBindings s)
      dynFieldQs = concatMap (vtmapQ f p) (stcDynFields s)
      cnstrQs = concatMap (vtmapQ f p) (stcCnstrs s)
      embedValQs = maybe [] (\ev -> [f (appendTermStep p embedValueTermStep) (VTVal ev)]) (stcEmbedVal s)
     in
      fieldQs ++ bindingQs ++ dynFieldQs ++ cnstrQs ++ embedValQs
   where
    nf = appendFeature p
  vtmapM f p s = do
    stcBindings' <-
      Map.traverseWithKey
        ( \k !v -> do
            r <- f (nf $ mkLetFeature k) (VTVNode v)
            return $ vtVNodeOr id v r
        )
        (stcBindings s)
    stcDynFields' <- mapM (vtmapM f p) (stcDynFields s)
    stcCnstrs' <- mapM (vtmapM f p) (stcCnstrs s)
    -- Fields are of Field, not VNode so we need to use vtmapM on fields.
    stcFields' <- Map.traverseWithKey (\k !v -> vtmapM f (nf $ mkStringFeature k) v) (stcFields s)
    stcEmbedVal' <- case stcEmbedVal s of
      Nothing -> return Nothing
      Just ev ->
        Just <$> do
          r <- f (appendTermStep p embedValueTermStep) (VTVal ev)
          return $ vtValOr id ev r
    return
      s
        { stcFields = stcFields'
        , stcBindings = stcBindings'
        , stcDynFields = stcDynFields'
        , stcCnstrs = stcCnstrs'
        , stcEmbedVal = stcEmbedVal'
        }
   where
    nf = appendFeature p
  getChildVT segment struct = case addrSegmentTag segment of
    StringTag -> do
      feature <- addrSegmentToFeature segment
      field <- lookupStructField (getTextIndexFromFeature feature) struct
      return $ VTVNode field.ssfValue
    LetTag -> do
      feature <- addrSegmentToFeature segment
      VTVNode <$> lookupStructLet (getTextIndexFromFeature feature) struct
    PatternTag -> do
      step <- addrSegmentToTermStep segment
      let (identifier, _) = getPatternIndexesFromTermStep step
      constraint <- struct.stcCnstrs IntMap.!? identifier
      getChildVT segment constraint
    DynFieldTag -> do
      step <- addrSegmentToTermStep segment
      let (identifier, _) = getDynFieldIndexesFromTermStep step
      field <- struct.stcDynFields IntMap.!? identifier
      getChildVT segment field
    EmbedValueTag -> VTVal <$> struct.stcEmbedVal
    _ -> Nothing
  setChildVT segment child struct = case addrSegmentTag segment of
    StringTag -> do
      feature <- addrSegmentToFeature segment
      let key = getTextIndexFromFeature feature
      field <- lookupStructField key struct
      case child of
        VTVNode replacement ->
          return struct{stcFields = Map.insert key field{ssfValue = replacement} struct.stcFields}
        _ -> Nothing
    LetTag -> do
      feature <- addrSegmentToFeature segment
      let key = getTextIndexFromFeature feature
      _ <- lookupStructLet key struct
      case child of
        VTVNode replacement ->
          return struct{stcBindings = Map.insert key replacement struct.stcBindings}
        _ -> Nothing
    PatternTag -> do
      step <- addrSegmentToTermStep segment
      let (identifier, _) = getPatternIndexesFromTermStep step
      constraint <- struct.stcCnstrs IntMap.!? identifier
      replacement <- setChildVT segment child constraint
      return struct{stcCnstrs = IntMap.insert identifier replacement struct.stcCnstrs}
    DynFieldTag -> do
      step <- addrSegmentToTermStep segment
      let (identifier, _) = getDynFieldIndexesFromTermStep step
      field <- struct.stcDynFields IntMap.!? identifier
      replacement <- setChildVT segment child field
      return struct{stcDynFields = IntMap.insert identifier replacement struct.stcDynFields}
    EmbedValueTag -> do
      _ <- struct.stcEmbedVal
      case child of
        VTVal replacement -> return struct{stcEmbedVal = Just replacement}
        _ -> Nothing
    _ -> Nothing

instance VTerm Field where
  vtmapQ f p field = [f p (VTVNode $ ssfValue field)]
  vtmapM f p field = do
    r <- f p (VTVNode $ ssfValue field)
    return field{ssfValue = vtVNodeOr id (ssfValue field) r}

instance VTerm DynamicField where
  vtmapQ f p df =
    f (nf 0) (VTVNode $ dsfLabel df) : vtmapQ f p (dsfValue df)
   where
    nf i = appendTermStep p (mkDynFieldTermStep (dsfID df) i)
  vtmapM f p df@DynamicField{dsfLabel, dsfValue} = do
    dsfLabel' <- adaptVTMapMOnVNode f (nf 0) dsfLabel
    dsfValue' <- vtmapM f (nf 1) dsfValue
    return df{dsfLabel = dsfLabel', dsfValue = dsfValue'}
   where
    nf i = appendTermStep p (mkDynFieldTermStep (dsfID df) i)
  getChildVT segment field
    | addrSegmentTag segment == DynFieldTag = do
        step <- addrSegmentToTermStep segment
        let (identifier, selector) = getDynFieldIndexesFromTermStep step
        if identifier /= field.dsfID
          then Nothing
          else case selector of
            0 -> Just $ VTVNode field.dsfLabel
            1 -> Just $ VTConstraintSeq field.dsfValue
            _ -> Nothing
    | otherwise = Nothing
  setChildVT segment child field
    | addrSegmentTag segment == DynFieldTag = do
        step <- addrSegmentToTermStep segment
        let (identifier, selector) = getDynFieldIndexesFromTermStep step
        if identifier /= field.dsfID
          then Nothing
          else case (selector, child) of
            (0, VTVNode label) -> Just field{dsfLabel = label}
            (1, VTConstraintSeq constraints) -> Just field{dsfValue = constraints}
            _ -> Nothing
    | otherwise = Nothing

instance VTerm StructCnstr where
  vtmapQ f p cnstr =
    f (nf 0) (VTVNode $ scsPattern cnstr) : vtmapQ f p (scsValue cnstr)
   where
    nf i = appendTermStep p (mkPatternTermStep (scsID cnstr) i)
  vtmapM f p cnstr = do
    scsPattern' <- adaptVTMapMOnVNode f (nf 0) (scsPattern cnstr)
    scsValue' <- vtmapM f (nf 1) (scsValue cnstr)
    return cnstr{scsPattern = scsPattern', scsValue = scsValue'}
   where
    nf i = appendTermStep p (mkPatternTermStep (scsID cnstr) i)
  getChildVT segment constraint
    | addrSegmentTag segment == PatternTag = do
        step <- addrSegmentToTermStep segment
        let (identifier, selector) = getPatternIndexesFromTermStep step
        if identifier /= constraint.scsID
          then Nothing
          else case selector of
            0 -> Just $ VTVNode constraint.scsPattern
            1 -> Just $ VTConstraintSeq constraint.scsValue
            _ -> Nothing
    | otherwise = Nothing
  setChildVT segment child constraint
    | addrSegmentTag segment == PatternTag = do
        step <- addrSegmentToTermStep segment
        let (identifier, selector) = getPatternIndexesFromTermStep step
        if identifier /= constraint.scsID
          then Nothing
          else case (selector, child) of
            (0, VTVNode patternNode) -> Just constraint{scsPattern = patternNode}
            (1, VTConstraintSeq constraints) -> Just constraint{scsValue = constraints}
            _ -> Nothing
    | otherwise = Nothing

instance VTerm List where
  vtmapQ f p lst =
    foldrVecWAddr (adaptVTMapQOnVNode f) (termStepToAddrSegment . mkListStoreIdxTermStep) p (store lst)
      ++ foldrVecWAddr (adaptVTMapQOnVal f) (featureToAddrSegment . mkListIdxFeature) p (final lst)

  vtmapM f p lst = do
    store' <- mapMVectorWAddr (adaptVTMapMOnVNode f) (termStepToAddrSegment . mkListStoreIdxTermStep) p (store lst)
    final' <- mapMVectorWAddr (adaptVTMapMOnVal f) (featureToAddrSegment . mkListIdxFeature) p (final lst)
    return lst{store = store', final = final'}
  getChildVT segment list = case addrSegmentTag segment of
    ListStoreIdxTag -> do
      step <- addrSegmentToTermStep segment
      VTVNode <$> list.store V.!? termStepIndex step
    ListIdxTag -> do
      feature <- addrSegmentToFeature segment
      VTVal <$> list.final V.!? featureIndex feature
    _ -> Nothing
  setChildVT segment child list = case addrSegmentTag segment of
    ListStoreIdxTag -> do
      step <- addrSegmentToTermStep segment
      let index = termStepIndex step
      _ <- list.store V.!? index
      case child of
        VTVNode replacement -> return list{store = list.store V.// [(index, replacement)]}
        _ -> Nothing
    ListIdxTag -> do
      feature <- addrSegmentToFeature segment
      let index = featureIndex feature
      _ <- list.final V.!? index
      case child of
        VTVal replacement -> return list{final = list.final V.// [(index, replacement)]}
        _ -> Nothing
    _ -> Nothing

instance VTerm Disj where
  vtmapQ f p dj = foldrSeqWAddr (adaptVTMapQOnVNode f) (termStepToAddrSegment . mkDisjTermStep) p (dsjDisjuncts dj)

  vtmapM f p d = do
    dsjDisjuncts' <- mapMSeqWAddr (adaptVTMapMOnVNode f) (termStepToAddrSegment . mkDisjTermStep) p (dsjDisjuncts d)
    return d{dsjDisjuncts = dsjDisjuncts'}
  getChildVT segment disj = do
    (_, node) <- lookupSeqBySegment DisjTag segment disj.dsjDisjuncts
    return $ VTVNode node
  setChildVT segment child disj = do
    (index, _) <- lookupSeqBySegment DisjTag segment disj.dsjDisjuncts
    case child of
      VTVNode replacement ->
        return disj{dsjDisjuncts = Seq.update index replacement disj.dsjDisjuncts}
      _ -> Nothing

instance VTerm Op where
  vtmapQ f p (RegOp rop) = vtmapQ f p rop
  vtmapQ f p (Ref ref) = vtmapQ f p ref
  vtmapQ f p (VSelect idx) = vtmapQ f p idx
  vtmapQ f p (Compreh c) = vtmapQ f p c
  vtmapQ f p (DisjOp d) = vtmapQ f p d
  vtmapQ f p (Itp itp) = vtmapQ f p itp
  vtmapQ f p (FCall func) = vtmapQ f p func

  vtmapM f p (RegOp rop) = RegOp <$> vtmapM f p rop
  vtmapM f p (Ref ref) = Ref <$> vtmapM f p ref
  vtmapM f p (VSelect idx) = VSelect <$> vtmapM f p idx
  vtmapM f p (Compreh c) = Compreh <$> vtmapM f p c
  vtmapM f p (DisjOp d) = DisjOp <$> vtmapM f p d
  vtmapM f p (Itp itp) = Itp <$> vtmapM f p itp
  vtmapM f p (FCall func) = FCall <$> vtmapM f p func
  getChildVT segment (RegOp regular) = getChildVT segment regular
  getChildVT segment (Ref reference) = getChildVT segment reference
  getChildVT segment (VSelect select) = getChildVT segment select
  getChildVT segment (Compreh comprehension) = getChildVT segment comprehension
  getChildVT segment (DisjOp disjoin) = getChildVT segment disjoin
  getChildVT segment (Itp interpolation) = getChildVT segment interpolation
  getChildVT segment (FCall function) = getChildVT segment function
  setChildVT segment child (RegOp regular) = RegOp <$> setChildVT segment child regular
  setChildVT segment child (Ref reference) = Ref <$> setChildVT segment child reference
  setChildVT segment child (VSelect select) = VSelect <$> setChildVT segment child select
  setChildVT segment child (Compreh comprehension) = Compreh <$> setChildVT segment child comprehension
  setChildVT segment child (DisjOp disjoin) = DisjOp <$> setChildVT segment child disjoin
  setChildVT segment child (Itp interpolation) = Itp <$> setChildVT segment child interpolation
  setChildVT segment child (FCall function) = FCall <$> setChildVT segment child function

appendMutArgF :: EvalAddr -> Int -> EvalAddr
appendMutArgF p i = appendTermStep p (mkOpArgTermStep i)

instance VTerm RegularOp where
  vtmapQ f p rop = foldrSeqWAddr (adaptVTMapQOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p (ropArgs rop)
  vtmapM f p rop = do
    ropArgs' <- mapMSeqWAddr (adaptVTMapMOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p (ropArgs rop)
    return rop{ropArgs = ropArgs'}
  getChildVT segment regular = getVNodeSeqChild OpArgTag segment regular.ropArgs
  setChildVT segment child regular = do
    args' <- setVNodeSeqChild OpArgTag segment child regular.ropArgs
    return regular{ropArgs = args'}

instance VTerm Reference where
  vtmapQ f p ref = foldrSeqWAddr (adaptVTMapQOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p (selectors ref)
  vtmapM f p ref = do
    selectors' <- mapMSeqWAddr (adaptVTMapMOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p (selectors ref)
    return ref{selectors = selectors'}
  getChildVT segment reference = getVNodeSeqChild OpArgTag segment reference.selectors
  setChildVT segment child reference = do
    selectors' <- setVNodeSeqChild OpArgTag segment child reference.selectors
    return reference{selectors = selectors'}

instance VTerm ValueSelect where
  vtmapQ f p (ValueSelect i b xs _) =
    adaptVTMapQOnVNode f (appendTermStep p (mkObjectTermStep i)) b
      : foldrSeqWAddr (adaptVTMapQOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p xs
  vtmapM f p (ValueSelect i b xs typs) = do
    b' <- adaptVTMapMOnVNode f (appendTermStep p (mkObjectTermStep i)) b
    xs' <- mapMSeqWAddr (adaptVTMapMOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p xs
    return $ ValueSelect i b' xs' typs
  getChildVT segment select = case addrSegmentTag segment of
    ObjectTag -> do
      identifier <- termStepIndexFor ObjectTag segment
      if identifier == select.bvID
        then Just $ VTVNode select.base
        else Nothing
    OpArgTag -> getVNodeSeqChild OpArgTag segment select.iSelectors
    _ -> Nothing
  setChildVT segment child select = case addrSegmentTag segment of
    ObjectTag -> do
      identifier <- termStepIndexFor ObjectTag segment
      if identifier /= select.bvID
        then Nothing
        else case child of
          VTVNode replacement -> Just select{base = replacement}
          _ -> Nothing
    OpArgTag -> do
      selectors' <- setVNodeSeqChild OpArgTag segment child select.iSelectors
      return select{iSelectors = selectors'}
    _ -> Nothing

instance VTerm Comprehension where
  vtmapQ f p c =
    Seq.foldrWithIndex
      (\i arg acc -> adaptVTMapQOnVNode f (appendTermStep p (mkRegCnstrTermStep i)) (getValFromIterClause arg) : acc)
      []
      c.args
  vtmapM f p c = do
    args' <-
      Seq.traverseWithIndex
        ( \i arg -> do
            v' <- adaptVTMapMOnVNode f (appendTermStep p (mkRegCnstrTermStep i)) (getValFromIterClause arg)
            return $ setValInIterClause v' arg
        )
        c.args
    return c{args = args'}
  getChildVT segment comprehension = do
    (_, argument) <- lookupSeqBySegment ConstraintTag segment comprehension.args
    return $ VTVNode $ getValFromIterClause argument
  setChildVT segment child comprehension = do
    (index, argument) <- lookupSeqBySegment ConstraintTag segment comprehension.args
    case child of
      VTVNode replacement ->
        return
          comprehension
            { args = Seq.update index (setValInIterClause replacement argument) comprehension.args
            }
      _ -> Nothing

instance VTerm DisjoinOp where
  vtmapQ f p d =
    Seq.foldrWithIndex
      (\i term acc -> adaptVTMapQOnVNode f (appendMutArgF p i) (dstValue term) : acc)
      []
      (djoTerms d)
  vtmapM f p djo = do
    djoTerms' <-
      Seq.traverseWithIndex
        ( \i term -> do
            dstValue' <- adaptVTMapMOnVNode f (appendMutArgF p i) (dstValue term)
            return $ term{dstValue = dstValue'}
        )
        (djoTerms djo)
    return djo{djoTerms = djoTerms'}
  getChildVT segment disjoin = do
    (_, term) <- lookupSeqBySegment OpArgTag segment disjoin.djoTerms
    return $ VTVNode term.dstValue
  setChildVT segment child disjoin = do
    (index, term) <- lookupSeqBySegment OpArgTag segment disjoin.djoTerms
    case child of
      VTVNode replacement ->
        return disjoin{djoTerms = Seq.update index term{dstValue = replacement} disjoin.djoTerms}
      _ -> Nothing

instance VTerm Interpolation where
  vtmapQ f p itp = foldrSeqWAddr (adaptVTMapQOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p (itpExprs itp)
  vtmapM f p itp = do
    itpExprs' <- mapMSeqWAddr (adaptVTMapMOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p (itpExprs itp)
    return itp{itpExprs = itpExprs'}
  getChildVT segment interpolation = getVNodeSeqChild OpArgTag segment interpolation.itpExprs
  setChildVT segment child interpolation = do
    expressions' <- setVNodeSeqChild OpArgTag segment child interpolation.itpExprs
    return interpolation{itpExprs = expressions'}

instance VTerm FuncCall where
  vtmapQ f p func = foldrSeqWAddr (adaptVTMapQOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p (fnFrame func)
  vtmapM f p func = do
    fnFrame' <- mapMSeqWAddr (adaptVTMapMOnVNode f) (termStepToAddrSegment . mkOpArgTermStep) p (fnFrame func)
    return func{fnFrame = fnFrame'}
  getChildVT segment function = getVNodeSeqChild OpArgTag segment function.fnFrame
  setChildVT segment child function = do
    frame' <- setVNodeSeqChild OpArgTag segment child function.fnFrame
    return function{fnFrame = frame'}

getVNodeSeqChild :: SegmentTag -> AddrSegment -> Seq.Seq VNode -> Maybe VTermNode
getVNodeSeqChild expectedTag segment children = do
  (_, child) <- lookupSeqBySegment expectedTag segment children
  return $ VTVNode child

setVNodeSeqChild :: SegmentTag -> AddrSegment -> VTermNode -> Seq.Seq VNode -> Maybe (Seq.Seq VNode)
setVNodeSeqChild expectedTag segment child children = do
  (index, _) <- lookupSeqBySegment expectedTag segment children
  case child of
    VTVNode replacement -> Just $ Seq.update index replacement children
    _ -> Nothing

lookupSeqBySegment :: SegmentTag -> AddrSegment -> Seq.Seq a -> Maybe (Int, a)
lookupSeqBySegment expectedTag segment values = do
  index <- termStepIndexFor expectedTag segment
  value <- values Seq.!? index
  return (index, value)

termStepIndexFor :: SegmentTag -> AddrSegment -> Maybe Int
termStepIndexFor expectedTag segment
  | addrSegmentTag segment == expectedTag = termStepIndex <$> addrSegmentToTermStep segment
  | otherwise = Nothing

pretravsVTM :: (Monad m) => (EvalAddr -> VTermNode -> m VTermNode) -> EvalAddr -> VTermNode -> m VTermNode
pretravsVTM f p x = do
  x' <- f p x
  vtmapM (pretravsVTM f) p x'

pretravsVT :: (EvalAddr -> VTermNode -> VTermNode) -> EvalAddr -> VTermNode -> VTermNode
pretravsVT f p x = let x' = f p x in vtmapT (pretravsVT f) p x'

posttravsVT :: (EvalAddr -> VTermNode -> VTermNode) -> EvalAddr -> VTermNode -> VTermNode
posttravsVT f p x = let x' = vtmapT (posttravsVT f) p x in f p x'

pretravsVTQ :: (r -> r -> r) -> (EvalAddr -> VTermNode -> r) -> EvalAddr -> VTermNode -> r
pretravsVTQ k f p x = foldl k (f p x) (vtmapQ (pretravsVTQ k f) p x)

{- | Set the sub tree with the given segment and new tree.

The sub tree should already exist in the parent tree.
-}
setSubVN :: AddrSegment -> VNode -> VNode -> Maybe VNode
setSubVN segment replacement parent
  | addrSegmentTag segment == FileTopTag = Nothing
  | otherwise = do
      original <- getChildVT segment parent
      (replacementTerm, advanced) <- replacementVNodeTerm segment replacement original
      parent' <- setChildVT segment replacementTerm parent
      return $
        if advanced
          then parent'{version = parent.version + 1}
          else parent'

getSubVN :: AddrSegment -> VNode -> Maybe VNode
getSubVN segment parent
  | addrSegmentTag segment == FileTopTag = Just parent
  | otherwise = getChildVT segment parent >>= childTermVNode segment

childTermVNode :: AddrSegment -> VTermNode -> Maybe VNode
childTermVNode _ (VTVNode node) = Just node
childTermVNode segment (VTVal value)
  | isValueOnlySegment segment = Just $ mkValVN value
childTermVNode _ _ = Nothing

replacementVNodeTerm :: AddrSegment -> VNode -> VTermNode -> Maybe (VTermNode, Bool)
replacementVNodeTerm _ replacement (VTVNode original) =
  Just (VTVNode replacement, replacement.version > original.version)
replacementVNodeTerm segment replacement (VTVal original)
  | isValueOnlySegment segment =
      -- Value-only children do not retain a VNode version, so compare their
      -- values to decide whether the parent version must advance.
      Just (VTVal replacement.value, replacement.value /= original)
replacementVNodeTerm _ _ _ = Nothing

isValueOnlySegment :: AddrSegment -> Bool
isValueOnlySegment segment = case addrSegmentTag segment of
  EmbedValueTag -> True
  ListIdxTag -> True
  _ -> False

getSubVNByAddr :: EvalAddr -> VNode -> Maybe VNode
getSubVNByAddr addr = go (addrToList addr)
 where
  go [] v = Just v
  go (f : fs) v = do
    subV <- getSubVN f v
    go fs subV

-----
-- ASTNode
-----

instance ASTNode ValConstraint where
  getNodeLoc = vcLoc

instance ASTNode OpConstraint where
  getNodeLoc = ocLoc

instance ASTNode ConstraintSeq where
  getNodeLoc c =
    case Seq.viewl c of
      h Seq.:< _ -> getNodeLoc h
      Seq.EmptyL -> error "ConstraintSeq should have at least one constraint"

instance ASTNode Constraint where
  getNodeLoc c = case c of
    ValCnstr vc -> getNodeLoc vc
    OpCnstr oc -> getNodeLoc oc
    StructEmbedCnstr xs -> getNodeLoc xs

instance ASTNode ConstraintsSet where
  getNodeLoc c
    | not (Seq.null (static c)) = getNodeLoc c.static
    | otherwise = case IntMap.toList c.dynamic of
        (_, h) : _ -> getNodeLoc h
        [] -> error "ConstraintsSet should have at least one constraint"

instance ASTNode VNode where
  getNodeLoc vn = getNodeLoc vn.constraints
