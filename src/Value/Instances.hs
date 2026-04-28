{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Instances where

import Control.DeepSeq (NFData (..))
import Data.Aeson (ToJSON (..))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isNothing)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Vector as V
import Feature
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (..))
import Text.Printf (printf)
import Value.Comprehension
import Value.Disj
import Value.DisjoinOp
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

instance Eq Struct where
  (==) s1 s2 = stcFields s1 == stcFields s2 && stcClosed s1 == stcClosed s2 && stcIsConcrete s1 == stcIsConcrete s2

instance Eq Field where
  (==) f1 f2 = f1.ssfValue == f2.ssfValue && f1.ssfAttr == f2.ssfAttr

deriving instance Eq DynamicField
deriving instance Eq StructCnstr

deriving instance Eq List
deriving instance Eq Disj

deriving instance Eq Constraint
deriving instance Eq ConstraintsSet

instance Eq Val where
  (==) (VStruct s1) (VStruct s2) = s1 == s2
  (==) (VList ts1) (VList ts2) = ts1 == ts2
  (==) (VDisj d1) (VDisj d2) = d1 == d2
  (==) (VAtom l1) (VAtom l2) = l1 == l2
  (==) (VDisj dj1) n2@(VAtom _) =
    if isNothing (rtrDisjDefVal dj1)
      then False
      else (fromJust $ rtrDisjDefVal dj1) == n2
  (==) (VAtom a1) (VDisj dj2) = (==) (VDisj dj2) (VAtom a1)
  (==) (VBounds b1) (VBounds b2) = b1 == b2
  (==) (VBottom _) (VBottom _) = True
  (==) VTop VTop = True
  (==) VNoVal VNoVal = True
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
  show (ValueSelect _ _ _) = "vselect"

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

deriving instance Show Struct
deriving instance Show Field
deriving instance Show DynamicField
deriving instance Show StructCnstr

deriving instance Show List
deriving instance Show Disj

deriving instance Show Val
deriving instance Show VNode
deriving instance Show VTermNode
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
    s <- oneLinerStringOfVNode t
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

deriving instance NFData Struct
deriving instance NFData Field
deriving instance NFData DynamicField
deriving instance NFData StructCnstr

deriving instance NFData List
deriving instance NFData Disj

deriving instance NFData Val
deriving instance NFData VNode
deriving instance NFData Constraint
deriving instance NFData ConstraintsSet

-----
-- VTerm
-----

mapMVectorWAddr ::
  (Monad m) => (ValAddr -> a -> m a) -> (Int -> Feature) -> ValAddr -> V.Vector a -> m (V.Vector a)
mapMVectorWAddr f g p = V.imapM (\i !v -> f (appendSeg p (g i)) v)

mapMSeqWAddr :: (Monad m) => (ValAddr -> a -> m a) -> (Int -> Feature) -> ValAddr -> Seq.Seq a -> m (Seq.Seq a)
mapMSeqWAddr f g p = Seq.traverseWithIndex (\i !v -> f (appendSeg p (g i)) v)

mapMIntMapWAddr ::
  (Monad m) => (ValAddr -> a -> m a) -> (Int -> Feature) -> ValAddr -> IntMap.IntMap a -> m (IntMap.IntMap a)
mapMIntMapWAddr f g p = IntMap.traverseWithKey (\i !v -> f (appendSeg p (g i)) v)

foldrVecWAddr :: (ValAddr -> VNode -> r) -> (Int -> Feature) -> ValAddr -> V.Vector VNode -> [r]
foldrVecWAddr f g p = V.ifoldr (\i !v acc -> f (appendSeg p (g i)) v : acc) []

foldrSeqWAddr :: (ValAddr -> a -> r) -> (Int -> Feature) -> ValAddr -> Seq.Seq a -> [r]
foldrSeqWAddr f g p = Seq.foldrWithIndex (\i !v acc -> f (appendSeg p (g i)) v : acc) []

foldrSeqWAddrConcat :: (ValAddr -> a -> [r]) -> (Int -> Feature) -> ValAddr -> Seq.Seq a -> [r]
foldrSeqWAddrConcat f g p = Seq.foldrWithIndex (\i !v acc -> f (appendSeg p (g i)) v ++ acc) []

foldrIntMapWAddr :: (ValAddr -> a -> r) -> (Int -> Feature) -> ValAddr -> IntMap.IntMap a -> [r]
foldrIntMapWAddr f g p = IntMap.foldrWithKey (\i !v acc -> f (appendSeg p (g i)) v : acc) []

foldrIntMapWAddrConcat :: (ValAddr -> a -> [r]) -> (Int -> Feature) -> ValAddr -> IntMap.IntMap a -> [r]
foldrIntMapWAddrConcat f g p = IntMap.foldrWithKey (\i !v acc -> f (appendSeg p (g i)) v ++ acc) []

adaptVTMapQOnVNode :: (ValAddr -> VTermNode -> r) -> ValAddr -> VNode -> r
adaptVTMapQOnVNode f p v = f p (VTVNode v)

adaptVTMapQOnVal :: (ValAddr -> VTermNode -> r) -> ValAddr -> Val -> r
adaptVTMapQOnVal f p vn = f p (VTVal vn)

adaptVTMapMOnVNode :: (Monad m) => (ValAddr -> VTermNode -> m VTermNode) -> ValAddr -> VNode -> m VNode
adaptVTMapMOnVNode f p v = do
  vt' <- f p (VTVNode v)
  return $ vtVNodeOr id v vt'

adaptVTMapMOnVal :: (Monad m) => (ValAddr -> VTermNode -> m VTermNode) -> ValAddr -> Val -> m Val
adaptVTMapMOnVal f p v = do
  vt' <- f p (VTVal v)
  return $ vtValOr id v vt'

adaptVTMapTOnVal :: (ValAddr -> VTermNode -> VTermNode) -> ValAddr -> VNode -> VNode
adaptVTMapTOnVal f p v =
  let vt' = f p (VTVNode v)
   in vtVNodeOr id v vt'

instance VTerm VTermNode where
  vtmapQ f p (VTVal vn) = vtmapQ f p vn
  vtmapQ f p (VTVNode v) = vtmapQ f p v
  vtmapQ f p (VTOp op) = vtmapQ f p op
  vtmapM f p (VTVal vn) = VTVal <$> vtmapM f p vn
  vtmapM f p (VTVNode v) = VTVNode <$> vtmapM f p v
  vtmapM f p (VTOp op) = VTOp <$> vtmapM f p op

instance VTerm Val where
  vtmapQ f p (VStruct s) = vtmapQ f p s
  vtmapQ f p (VList l) = vtmapQ f p l
  vtmapQ f p (VDisj d) = vtmapQ f p d
  vtmapQ _ _ _ = []
  vtmapM f p (VStruct s) = VStruct <$> vtmapM f p s
  vtmapM f p (VList l) = VList <$> vtmapM f p l
  vtmapM f p (VDisj d) = VDisj <$> vtmapM f p d
  vtmapM _ _ a = return a

instance VTerm VNode where
  vtmapQ f p v =
    f p (VTVal $ value v) : vtmapQ f p (constraints v)
  vtmapM f p v = do
    value' <- f p (VTVal $ value v)
    constraints' <- vtmapM f p (constraints v)
    return v{value = vtValOr id (value v) value', constraints = constraints'}

instance VTerm ConstraintsSet where
  vtmapQ f p c =
    foldrSeqWAddrConcat (vtmapQ f) mkRegCnstrFeature p (static c)
      ++ foldrIntMapWAddrConcat (vtmapQ f) mkDynCnstrFeature p (dynamic c)
  vtmapM f p c = do
    static' <- mapMSeqWAddr (vtmapM f) mkRegCnstrFeature p (static c)
    dynamic' <- mapMIntMapWAddr (vtmapM f) mkDynCnstrFeature p (dynamic c)
    return c{static = static', dynamic = dynamic'}

instance VTerm Constraint where
  vtmapQ f p c = case c of
    ValCnstr vn -> [f p (VTVal vn)]
    StructEmbedCnstr xs -> foldrSeqWAddrConcat (vtmapQ f) mkRegCnstrFeature p xs
    OpCnstr o -> [f p (VTOp o)]
  vtmapM f p c = case c of
    ValCnstr vn -> do
      vn' <- f p (VTVal vn)
      return $ vtValOr ValCnstr c vn'
    StructEmbedCnstr xs -> StructEmbedCnstr <$> mapMSeqWAddr (vtmapM f) mkRegCnstrFeature p xs
    OpCnstr o -> do
      ovt' <- f p (VTOp o)
      case ovt' of
        VTOp o' -> return $ OpCnstr o'
        VTVal vn -> return $ ValCnstr vn
        _ -> return c

instance VTerm ConstraintSeq where
  vtmapQ f = foldrSeqWAddrConcat (vtmapQ f) mkRegCnstrFeature
  vtmapM f = mapMSeqWAddr (vtmapM f) mkRegCnstrFeature

instance VTerm Struct where
  vtmapQ f p s =
    let
      nf = appendSeg p
      fieldQs = Map.foldrWithKey (\k v acc -> vtmapQ f (nf (mkStringFeature k)) v ++ acc) [] (stcFields s)
      bindingQs = Map.foldrWithKey (\k v acc -> f (nf (mkLetFeature k)) (VTVNode v) : acc) [] (stcBindings s)
      dynFieldQs = concatMap (vtmapQ f p) (stcDynFields s)
      cnstrQs = concatMap (vtmapQ f p) (stcCnstrs s)
      embedValQs = maybe [] (\ev -> [f (nf mkEmbedValueFeature) (VTVal ev)]) (stcEmbedVal s)
     in
      fieldQs ++ bindingQs ++ dynFieldQs ++ cnstrQs ++ embedValQs
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
          r <- f (nf mkEmbedValueFeature) (VTVal ev)
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
    nf = appendSeg p

instance VTerm Field where
  vtmapQ f p field = [f p (VTVNode $ ssfValue field)]
  vtmapM f p field = do
    r <- f p (VTVNode $ ssfValue field)
    return field{ssfValue = vtVNodeOr id (ssfValue field) r}

instance VTerm DynamicField where
  vtmapQ f p df =
    f (nf 0) (VTVNode $ dsfLabel df) : vtmapQ f p (dsfValue df)
   where
    nf i = appendSeg p (mkDynFieldFeature (dsfID df) i)
  vtmapM f p df@DynamicField{dsfLabel, dsfValue} = do
    dsfLabel' <- adaptVTMapMOnVNode f (nf 0) dsfLabel
    dsfValue' <- vtmapM f (nf 1) dsfValue
    return df{dsfLabel = dsfLabel', dsfValue = dsfValue'}
   where
    nf i = appendSeg p (mkDynFieldFeature (dsfID df) i)

instance VTerm StructCnstr where
  vtmapQ f p cnstr =
    f (nf 0) (VTVNode $ scsPattern cnstr) : vtmapQ f p (scsValue cnstr)
   where
    nf i = appendSeg p (mkPatternFeature (scsID cnstr) i)
  vtmapM f p cnstr = do
    scsPattern' <- adaptVTMapMOnVNode f (nf 0) (scsPattern cnstr)
    scsValue' <- vtmapM f (nf 1) (scsValue cnstr)
    return cnstr{scsPattern = scsPattern', scsValue = scsValue'}
   where
    nf i = appendSeg p (mkPatternFeature (scsID cnstr) i)

instance VTerm List where
  vtmapQ f p lst =
    foldrVecWAddr (adaptVTMapQOnVNode f) mkListStoreIdxFeature p (store lst)
      ++ foldrVecWAddr (adaptVTMapQOnVNode f) mkListIdxFeature p (final lst)

  vtmapM f p lst = do
    store' <- mapMVectorWAddr (adaptVTMapMOnVNode f) mkListStoreIdxFeature p (store lst)
    final' <- mapMVectorWAddr (adaptVTMapMOnVNode f) mkListIdxFeature p (final lst)
    return lst{store = store', final = final'}

instance VTerm Disj where
  vtmapQ f p dj = foldrSeqWAddr (adaptVTMapQOnVNode f) mkDisjFeature p (dsjDisjuncts dj)

  vtmapM f p d = do
    dsjDisjuncts' <- mapMSeqWAddr (adaptVTMapMOnVNode f) mkDisjFeature p (dsjDisjuncts d)
    return d{dsjDisjuncts = dsjDisjuncts'}

instance VTerm Op where
  vtmapQ f p (RegOp rop) = vtmapQ f p rop
  vtmapQ f p (Ref ref) = vtmapQ f p ref
  vtmapQ f p (VSelect idx) = vtmapQ f p idx
  vtmapQ f p (Compreh c) = vtmapQ f p c
  vtmapQ f p (DisjOp d) = vtmapQ f p d
  vtmapQ f p (Itp itp) = vtmapQ f p itp

  vtmapM f p (RegOp rop) = RegOp <$> vtmapM f p rop
  vtmapM f p (Ref ref) = Ref <$> vtmapM f p ref
  vtmapM f p (VSelect idx) = VSelect <$> vtmapM f p idx
  vtmapM f p (Compreh c) = Compreh <$> vtmapM f p c
  vtmapM f p (DisjOp d) = DisjOp <$> vtmapM f p d
  vtmapM f p (Itp itp) = Itp <$> vtmapM f p itp

appendMutArgF :: ValAddr -> Int -> ValAddr
appendMutArgF p i = appendSeg p (mkOpArgFeature i)

instance VTerm RegularOp where
  vtmapQ f p rop = foldrSeqWAddr (adaptVTMapQOnVNode f) mkOpArgFeature p (ropArgs rop)
  vtmapM f p rop = do
    ropArgs' <- mapMSeqWAddr (adaptVTMapMOnVNode f) mkOpArgFeature p (ropArgs rop)
    return rop{ropArgs = ropArgs'}

instance VTerm Reference where
  vtmapQ f p ref = foldrSeqWAddr (adaptVTMapQOnVNode f) mkOpArgFeature p (selectors ref)
  vtmapM f p ref = do
    selectors' <- mapMSeqWAddr (adaptVTMapMOnVNode f) mkOpArgFeature p (selectors ref)
    return ref{selectors = selectors'}

instance VTerm ValueSelect where
  vtmapQ f p (ValueSelect i b xs) =
    adaptVTMapQOnVNode f (appendSeg p (mkObjectFeature i)) b
      : foldrSeqWAddr (adaptVTMapQOnVNode f) mkOpArgFeature p xs
  vtmapM f p (ValueSelect i b xs) = do
    b' <- adaptVTMapMOnVNode f (appendSeg p (mkObjectFeature i)) b
    xs' <- mapMSeqWAddr (adaptVTMapMOnVNode f) mkOpArgFeature p xs
    return $ ValueSelect i b' xs'

instance VTerm Comprehension where
  vtmapQ f p c =
    let p' = appendSeg p (mkObjectFeature c.cid)
     in Seq.foldrWithIndex
          (\i arg acc -> adaptVTMapQOnVNode f (appendSeg p' (mkComprehClausesFeature i)) (getValFromIterClause arg) : acc)
          []
          c.args
  vtmapM f p c = do
    let p' = appendSeg p (mkObjectFeature c.cid)
    args' <-
      Seq.traverseWithIndex
        ( \i arg -> do
            v' <- adaptVTMapMOnVNode f (appendSeg p' (mkComprehClausesFeature i)) (getValFromIterClause arg)
            return $ setValInIterClause v' arg
        )
        c.args
    return c{args = args'}

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

instance VTerm Interpolation where
  vtmapQ f p itp = foldrSeqWAddr (adaptVTMapQOnVNode f) mkOpArgFeature p (itpExprs itp)
  vtmapM f p itp = do
    itpExprs' <- mapMSeqWAddr (adaptVTMapMOnVNode f) mkOpArgFeature p (itpExprs itp)
    return itp{itpExprs = itpExprs'}

pretravsVTM :: (Monad m) => (ValAddr -> VTermNode -> m VTermNode) -> ValAddr -> VTermNode -> m VTermNode
pretravsVTM f p x = do
  x' <- f p x
  vtmapM (pretravsVTM f) p x'

pretravsVT :: (ValAddr -> VTermNode -> VTermNode) -> ValAddr -> VTermNode -> VTermNode
pretravsVT f p x = let x' = f p x in vtmapT (pretravsVT f) p x'

posttravsVT :: (ValAddr -> VTermNode -> VTermNode) -> ValAddr -> VTermNode -> VTermNode
posttravsVT f p x = let x' = vtmapT (posttravsVT f) p x in f p x'

pretravsVTQ :: (r -> r -> r) -> (ValAddr -> VTermNode -> r) -> ValAddr -> VTermNode -> r
pretravsVTQ k f p x = foldl k (f p x) (vtmapQ (pretravsVTQ k f) p x)