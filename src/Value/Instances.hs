{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Value.Instances where

import Control.DeepSeq (NFData (..))
import Data.Aeson (ToJSON (..))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isNothing)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Vector as V
import Feature
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (..))
import Text.Printf (printf)
import Value.Comprehension
import Value.Constraint
import Value.Disj
import Value.DisjoinOp
import Value.Fix
import Value.Interpolation
import Value.List
import Value.Op
import Value.Reference
import Value.Struct
import Value.UnifyOp
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

deriving instance Eq UnifyOp

deriving instance Eq SOp
deriving instance Eq Op
deriving instance Eq OpFrame
deriving instance Eq RegularOp

instance Eq Struct where
  (==) s1 s2 = stcFields s1 == stcFields s2 && stcClosed s1 == stcClosed s2 && stcIsConcrete s1 == stcIsConcrete s2

instance Eq Field where
  (==) f1 f2 = f1.ssfValue == f2.ssfValue && f1.ssfAttr == f2.ssfAttr

deriving instance Eq DynamicField
deriving instance Eq StructCnstr

deriving instance Eq List
deriving instance Eq Disj
deriving instance Eq AtomCnstr
deriving instance Eq Fix
deriving instance Eq FixConj

instance Eq ValNode where
  (==) (VNStruct s1) (VNStruct s2) = s1 == s2
  (==) (VNList ts1) (VNList ts2) = ts1 == ts2
  (==) (VNDisj d1) (VNDisj d2) = d1 == d2
  (==) (VNAtom l1) (VNAtom l2) = l1 == l2
  (==) (VNAtomCnstr c1) (VNAtomCnstr c2) = c1 == c2
  (==) (VNDisj dj1) n2@(VNAtom _) =
    if isNothing (rtrDisjDefVal dj1)
      then False
      else valNode (fromJust $ rtrDisjDefVal dj1) == n2
  (==) (VNAtom a1) (VNDisj dj2) = (==) (VNDisj dj2) (VNAtom a1)
  (==) (VNBounds b1) (VNBounds b2) = b1 == b2
  (==) (VNBottom _) (VNBottom _) = True
  (==) VNTop VNTop = True
  -- Only compare the ValNode part of Fix.
  (==) (VNFix r1) (VNFix r2) = r1.val == r2.val
  (==) VNNoVal VNNoVal = True
  (==) _ _ = False

instance Eq Val where
  (==) t1 t2 = valNode t1 == valNode t2

-----
-- Show
-----

deriving instance Show Comprehension
deriving instance Show ComprehArg

instance Show Reference where
  show (Reference{ident}) = "ref_" ++ show ident

instance Show ValueSelect where
  show (ValueSelect _ _) = "index"

deriving instance Show Interpolation

deriving instance Show DisjoinOp
deriving instance Show DisjTerm

instance ShowWTIndexer DisjTerm where
  tshow term = do
    marked <- tshow (dstMarked term)
    value <- tshow (dstValue term)
    return $ T.pack $ printf "DisjTerm{marked: %s, value: %s}" marked value
deriving instance Show UnifyOp

deriving instance Show SOp
deriving instance Show Op
deriving instance Show OpFrame
deriving instance Show RegularOp

deriving instance Show Struct
deriving instance Show Field
deriving instance Show DynamicField
deriving instance Show StructCnstr

deriving instance Show List
deriving instance Show Disj
deriving instance Show AtomCnstr
deriving instance Show Fix
deriving instance Show FixConj

instance ShowWTIndexer FixConj where
  tshow (FixSelect addr) = tshow addr
  tshow (FixCompreh t _) = tshow t

deriving instance Show ValNode
deriving instance Show Val

instance ShowWTIndexer Val where
  tshow = oneLinerStringOfVal

instance ToJSON Val where
  toJSON t = toJSON (show t)

instance ToJSONWTIndexer Val where
  ttoJSON t = do
    s <- oneLinerStringOfVal t
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

deriving instance NFData UnifyOp

deriving instance NFData SOp
deriving instance NFData Op
deriving instance NFData OpFrame
deriving instance NFData RegularOp

deriving instance NFData Struct
deriving instance NFData Field
deriving instance NFData DynamicField
deriving instance NFData StructCnstr

deriving instance NFData List
deriving instance NFData Disj
deriving instance NFData AtomCnstr
deriving instance NFData Fix
deriving instance NFData FixConj

deriving instance NFData ValNode
deriving instance NFData Val

-----
-- VTerm
-----

vtmapVectorM ::
  (Monad m) => (ValAddr -> Val -> m Val) -> (Int -> Feature) -> ValAddr -> V.Vector Val -> m (V.Vector Val)
vtmapVectorM f g p = V.imapM (\i !v -> f (appendSeg p (g i)) v)

vtmapSeqM :: (Monad m) => (ValAddr -> Val -> m Val) -> (Int -> Feature) -> ValAddr -> Seq.Seq Val -> m (Seq.Seq Val)
vtmapSeqM f g p = Seq.traverseWithIndex (\i !v -> f (appendSeg p (g i)) v)

vtmapVectorQ :: (ValAddr -> Val -> r) -> (Int -> Feature) -> ValAddr -> V.Vector Val -> [r]
vtmapVectorQ f g p = V.ifoldr (\i !v acc -> f (appendSeg p (g i)) v : acc) []

vtmapSeqQ :: (ValAddr -> Val -> r) -> (Int -> Feature) -> ValAddr -> Seq.Seq Val -> [r]
vtmapSeqQ f g p = Seq.foldrWithIndex (\i !v acc -> f (appendSeg p (g i)) v : acc) []

instance VTerm ValNode where
  vtmapQ f p (VNStruct s) = vtmapQ f p s
  vtmapQ f p (VNList l) = vtmapQ f p l
  vtmapQ f p (VNDisj d) = vtmapQ f p d
  vtmapQ _ _ _ = []
  vtmapM f p (VNStruct s) = VNStruct <$> vtmapM f p s
  vtmapM f p (VNList l) = VNList <$> vtmapM f p l
  vtmapM f p (VNDisj d) = VNDisj <$> vtmapM f p d
  vtmapM _ _ a = return a

instance VTerm Val where
  vtmapQ f p v =
    vtmapQ f p (valNode v)
      ++ maybe [] (vtmapQ f p) (op v)
  vtmapM f p v = do
    valNode' <- vtmapM f p (valNode v)
    op' <- case op v of
      Nothing -> return Nothing
      Just opVal -> Just <$> vtmapM f p opVal
    return v{valNode = valNode', op = op'}

instance VTerm Struct where
  vtmapQ f p s =
    let
      nf = appendSeg p
      fieldQs = Map.foldrWithKey (\k v acc -> vtmapQ f (nf (mkStringFeature k)) v ++ acc) [] (stcFields s)
      bindingQs = Map.foldrWithKey (\k v acc -> f (nf (mkLetFeature k)) v : acc) [] (stcBindings s)
      dynFieldQs = concatMap (vtmapQ f p) (stcDynFields s)
      cnstrQs = concatMap (vtmapQ f p) (stcCnstrs s)
      embedValQs = maybe [] (\ev -> [f (nf mkEmbedValueFeature) ev]) (stcEmbedVal s)
      staticFieldBaseQs = Map.foldrWithKey (\k v acc -> vtmapQ f (nf (mkStubFieldFeature k)) v ++ acc) [] (stcStaticFieldBases s)
     in
      fieldQs ++ bindingQs ++ dynFieldQs ++ cnstrQs ++ embedValQs ++ staticFieldBaseQs
  vtmapM f p s = do
    stcBindings' <- Map.traverseWithKey (\k !v -> f (nf $ mkLetFeature k) v) (stcBindings s)
    stcDynFields' <- mapM (vtmapM f p) (stcDynFields s)
    stcCnstrs' <- mapM (vtmapM f p) (stcCnstrs s)
    stcFields' <- Map.traverseWithKey (\k !v -> vtmapM f (nf $ mkStringFeature k) v) (stcFields s)
    stcEmbedVal' <- case stcEmbedVal s of
      Nothing -> return Nothing
      Just ev -> Just <$> f (nf mkEmbedValueFeature) ev
    stcStaticFieldBases' <- Map.traverseWithKey (\k !v -> vtmapM f (nf $ mkStubFieldFeature k) v) (stcStaticFieldBases s)
    return
      s
        { stcFields = stcFields'
        , stcBindings = stcBindings'
        , stcDynFields = stcDynFields'
        , stcCnstrs = stcCnstrs'
        , stcStaticFieldBases = stcStaticFieldBases'
        , stcEmbedVal = stcEmbedVal'
        }
   where
    nf = appendSeg p

instance VTerm Field where
  vtmapQ f p field = [f p (ssfValue field)]
  vtmapM f p field = do
    ssfValue' <- f p (ssfValue field)
    return field{ssfValue = ssfValue'}

instance VTerm DynamicField where
  vtmapQ f p df =
    [ f (nf 0) (dsfLabel df)
    , f (nf 1) (dsfValue df)
    ]
   where
    nf i = appendSeg p (mkDynFieldFeature (dsfID df) i)
  vtmapM f p df = do
    dsfLabel' <- f (nf 0) (dsfLabel df)
    dsfValue' <- f (nf 1) (dsfValue df)
    return df{dsfLabel = dsfLabel', dsfValue = dsfValue'}
   where
    nf i = appendSeg p (mkDynFieldFeature (dsfID df) i)

instance VTerm StructCnstr where
  vtmapQ f p cnstr =
    [ f (nf 0) (scsPattern cnstr)
    , f (nf 1) (scsValue cnstr)
    ]
   where
    nf i = appendSeg p (mkPatternFeature (scsID cnstr) i)
  vtmapM f p cnstr = do
    scsPattern' <- f (nf 0) (scsPattern cnstr)
    scsValue' <- f (nf 1) (scsValue cnstr)
    return cnstr{scsPattern = scsPattern', scsValue = scsValue'}
   where
    nf i = appendSeg p (mkPatternFeature (scsID cnstr) i)

instance VTerm List where
  vtmapQ f p lst =
    vtmapVectorQ f mkListStoreIdxFeature p (store lst)
      ++ vtmapVectorQ f mkListIdxFeature p (final lst)

  vtmapM f p lst = do
    store' <- vtmapVectorM f mkListStoreIdxFeature p (store lst)
    final' <- vtmapVectorM f mkListIdxFeature p (final lst)
    return lst{store = store', final = final'}

instance VTerm Disj where
  vtmapQ f p dj = vtmapSeqQ f mkDisjFeature p (dsjDisjuncts dj)

  vtmapM f p d = do
    dsjDisjuncts' <- vtmapSeqM f mkDisjFeature p (dsjDisjuncts d)
    return d{dsjDisjuncts = dsjDisjuncts'}

instance VTerm SOp where
  vtmapQ f p (SOp op _) = vtmapQ f p op
  vtmapM f p (SOp op frame) = do
    op' <- vtmapM f p op
    return $ SOp op' frame

instance VTerm Op where
  vtmapQ f p (RegOp rop) = vtmapQ f p rop
  vtmapQ f p (Ref ref) = vtmapQ f p ref
  vtmapQ f p (VSelect idx) = vtmapQ f p idx
  vtmapQ f p (Compreh c) = vtmapQ f p c
  vtmapQ f p (DisjOp d) = vtmapQ f p d
  vtmapQ f p (UOp u) = vtmapQ f p u
  vtmapQ f p (Itp itp) = vtmapQ f p itp

  vtmapM f p (RegOp rop) = RegOp <$> vtmapM f p rop
  vtmapM f p (Ref ref) = Ref <$> vtmapM f p ref
  vtmapM f p (VSelect idx) = VSelect <$> vtmapM f p idx
  vtmapM f p (Compreh c) = Compreh <$> vtmapM f p c
  vtmapM f p (DisjOp d) = DisjOp <$> vtmapM f p d
  vtmapM f p (UOp u) = UOp <$> vtmapM f p u
  vtmapM f p (Itp itp) = Itp <$> vtmapM f p itp

appendMutArgF :: ValAddr -> Int -> Bool -> ValAddr
appendMutArgF p i isUnify = appendSeg p (mkMutArgFeature i isUnify)

instance VTerm RegularOp where
  vtmapQ f p rop = vtmapSeqQ f (`mkMutArgFeature` False) p (ropArgs rop)
  vtmapM f p rop = do
    ropArgs' <- vtmapSeqM f (`mkMutArgFeature` False) p (ropArgs rop)
    return rop{ropArgs = ropArgs'}

instance VTerm Reference where
  vtmapQ f p ref = vtmapSeqQ f (`mkMutArgFeature` False) p (selectors ref)
  vtmapM f p ref = do
    selectors' <- vtmapSeqM f (`mkMutArgFeature` False) p (selectors ref)
    return ref{selectors = selectors'}

instance VTerm ValueSelect where
  vtmapQ f p (ValueSelect b xs) = f (appendSeg p valueSelectFeature) b : vtmapSeqQ f (`mkMutArgFeature` False) p xs
  vtmapM f p (ValueSelect b xs) = do
    b' <- f (appendSeg p valueSelectFeature) b
    xs' <- vtmapSeqM f (`mkMutArgFeature` False) p xs
    return $ ValueSelect b' xs'

instance VTerm Comprehension where
  vtmapQ f p c =
    Seq.foldrWithIndex
      (\i arg acc -> f (appendMutArgF p i False) (getValFromIterClause arg) : acc)
      []
      c.args
  vtmapM f p c = do
    args' <-
      Seq.traverseWithIndex
        ( \i arg -> do
            v' <- f (appendMutArgF p i False) (getValFromIterClause arg)
            return $ setValInIterClause v' arg
        )
        c.args
    return c{args = args'}

instance VTerm DisjoinOp where
  vtmapQ f p d =
    Seq.foldrWithIndex
      (\i term acc -> f (appendMutArgF p i False) (dstValue term) : acc)
      []
      (djoTerms d)
  vtmapM f p djo = do
    djoTerms' <-
      Seq.traverseWithIndex
        ( \i term -> do
            dstValue' <- f (appendMutArgF p i False) (dstValue term)
            return $ term{dstValue = dstValue'}
        )
        (djoTerms djo)
    return djo{djoTerms = djoTerms'}

instance VTerm UnifyOp where
  vtmapQ f p u = vtmapSeqQ f (`mkMutArgFeature` True) p (Value.UnifyOp.conjs u)
  vtmapM f p u = do
    conjs' <- vtmapSeqM f (`mkMutArgFeature` True) p (Value.UnifyOp.conjs u)
    return u{Value.UnifyOp.conjs = conjs'}

instance VTerm Interpolation where
  vtmapQ f p itp = vtmapSeqQ f (`mkMutArgFeature` False) p (itpExprs itp)
  vtmapM f p itp = do
    itpExprs' <- vtmapSeqM f (`mkMutArgFeature` False) p (itpExprs itp)
    return itp{itpExprs = itpExprs'}

pretravsValM :: (Monad m) => (ValAddr -> Val -> m Val) -> ValAddr -> Val -> m Val
pretravsValM f p x = do
  x' <- f p x
  vtmapM (pretravsValM f) p x'

pretravsVal :: (ValAddr -> Val -> Val) -> ValAddr -> Val -> Val
pretravsVal f p x = let x' = f p x in vtmapT (pretravsVal f) p x'

posttravsVal :: (ValAddr -> Val -> Val) -> ValAddr -> Val -> Val
posttravsVal f p x = let x' = vtmapT (posttravsVal f) p x in f p x'

pretravsValQ :: (r -> r -> r) -> (ValAddr -> Val -> r) -> ValAddr -> Val -> r
pretravsValQ k f p x = foldl k (f p x) (vtmapQ (pretravsValQ k f) p x)