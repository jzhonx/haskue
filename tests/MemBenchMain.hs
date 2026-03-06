{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}

module Main (main) where

import Control.DeepSeq (NFData (..))
import Control.Monad (forM_)
import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.RWS.Strict (runRWST)
import Cursor
import qualified Data.ByteString.Lazy as LB
import Data.Functor.Identity (Identity, runIdentity)
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Feature (ValAddr (..), appendSeg, mkListStoreIdxFeature, rootFeature, rootValAddr)
import GHC.Generics (Generic)
import Reduce.Monad (RM, emptyContext, emptyReduceConfig)
import StringIndex (TextIndex (..))
import Value
import Value.Instances (pretravsVal, pretravsValM, vtmapSeqM, vtmapVectorM)
import Weigh (Weigh, func, func', io, mainWith, wgroup)

main :: IO ()
main =
  mainWith $ do
    mapListB
    mapListIdentityB
    mapListRMB
    mapB
    imapB
    imapMB
    imapM2B
    vtmapTB
    vtmapVectorMRMB
    vtmapMRMViaListB
    vtmapMRMViaMutB
    vtmapSeqMRMB
    traverseWithKeyRMB
    pretravsValB
    pretravsValMRMB
    posttravsVCB

testV :: V.Vector Val
testV = V.generate 10000 (mkInputVal . fromIntegral)

testList :: [Val]
testList = map mkInputVal [0 .. 9999]

testSeq :: Seq.Seq Val
testSeq = Seq.fromList testList

testMap :: Map.Map Int Val
testMap = Map.fromList $ zip [0 .. 9999] testList

test100FieldsStruct :: Val
test100FieldsStruct =
  mkStructVal $
    emptyStruct
      { stcFields = Map.fromList $ map (\i -> (TextIndex i, mkdefaultField $ mkInputVal $ fromIntegral i)) [0 .. 99]
      }

testStruct :: Val
testStruct =
  mkStructVal $
    emptyStruct
      { stcFields = Map.fromList $ map (\i -> (TextIndex i, mkdefaultField test100FieldsStruct)) [0 .. 99]
      }

mkInputVal :: Integer -> Val
mkInputVal i = mkAtomVal (Int i)

mapListB :: Weigh ()
mapListB = func' "mapList" f testList
 where
  f v = map id v

mapListIdentityB :: Weigh ()
mapListIdentityB = func' "mapListIdentity" f testList
 where
  f v = runIdentity $ mapM return v

mapListRMB :: Weigh ()
mapListRMB = io "mapListRM" f testList
 where
  f :: [Val] -> IO (Either String [Val])
  f v = do
    let
      action :: RM [Val]
      action = mapM return v
    result <- runExceptT $ runRWST action emptyReduceConfig (emptyContext noopTraceSink)
    pure $ fmap (\(vals, _, _) -> vals) result

mapB :: Weigh ()
mapB = func' "V.map" f testV
 where
  f v = V.map id v

imapB :: Weigh ()
imapB = func' "V.imap" f testV
 where
  f v = V.imap (\_ !v -> v) v

imapMB :: Weigh ()
imapMB = func' "V.imapMIdentity" f testV
 where
  f v = runIdentity $ V.imapM (\_ !v -> return v) v

imapM2B :: Weigh ()
imapM2B = func' "V.imapMViaListIdentity" f testV
 where
  f v =
    let xs = V.toList v
     in V.fromList $ runIdentity $ mapM return xs

vtmapTB :: Weigh ()
vtmapTB = func' "vtmapT" f testV
 where
  f v = runIdentity $ vtmapVectorM (\_ v -> return v) mkListStoreIdxFeature rootValAddr v

vtmapVectorMRMB :: Weigh ()
vtmapVectorMRMB = io "vtmapVectorMRM" f testV
 where
  f v = do
    let action = vtmapVectorM idm mkListStoreIdxFeature rootValAddr v
    result <- runExceptT $ runRWST action emptyReduceConfig (emptyContext noopTraceSink)
    pure $ fmap (\(vals, _, _) -> vals) result

  idm :: ValAddr -> Val -> RM Val
  idm _ v = return v

vtmapMRMViaListB :: Weigh ()
vtmapMRMViaListB = io "vtmapMRMViaList" f testV
 where
  f v = do
    let
      action :: RM (V.Vector Val)
      action = do
        let xs = V.toList v
        res <- mapM return xs
        return $ V.fromList res
    result <- runExceptT $ runRWST action emptyReduceConfig (emptyContext noopTraceSink)
    pure $ fmap (\(vals, _, _) -> vals) result

  idm :: ValAddr -> Val -> RM Val
  idm _ v = return v

vtmapMRMViaMutB :: Weigh ()
vtmapMRMViaMutB = io "vtmapMRMViaMut" f testV
 where
  f v = do
    let
      action :: RM (V.Vector Val)
      action = do
        mv <- V.thaw v
        forM_ [0 .. MV.length mv - 1] $ \i -> do
          v <- MV.read mv i
          v' <- idm (appendSeg rootValAddr (mkListStoreIdxFeature i)) v
          MV.write mv i v'
        V.unsafeFreeze mv
    result <- runExceptT $ runRWST action emptyReduceConfig (emptyContext noopTraceSink)
    pure $ fmap (\(vals, _, _) -> vals) result

  idm :: ValAddr -> Val -> RM Val
  idm _ v = return v

vtmapSeqMRMB :: Weigh ()
vtmapSeqMRMB = io "vtmapSeqMRM" f testSeq
 where
  f v = do
    let action = vtmapSeqM idm mkListStoreIdxFeature rootValAddr v
    result <- runExceptT $ runRWST action emptyReduceConfig (emptyContext noopTraceSink)
    pure $ fmap (\(vals, _, _) -> vals) result

  idm :: ValAddr -> Val -> RM Val
  idm _ v = return v

traverseWithKeyRMB :: Weigh ()
traverseWithKeyRMB = io "Map.traverseWithKey" f testMap
 where
  f v = do
    let action = Map.traverseWithKey (\k !v -> idm (appendSeg rootValAddr (mkListStoreIdxFeature k)) v) v
    result <- runExceptT $ runRWST action emptyReduceConfig (emptyContext noopTraceSink)
    pure $ fmap (\(vals, _, _) -> vals) result

  idm :: ValAddr -> Val -> RM Val
  idm _ v = return v

pretravsValB :: Weigh ()
pretravsValB = io "pretravsVal" f testStruct
 where
  f v = do
    let
      action :: RM Val
      action = return $ pretravsVal idm rootValAddr v
    result <- runExceptT $ runRWST action emptyReduceConfig (emptyContext noopTraceSink)
    pure $ fmap (\(vals, _, _) -> vals) result

  idm :: ValAddr -> Val -> Val
  idm _ v = v

pretravsValMRMB :: Weigh ()
pretravsValMRMB = io "pretravsValM" f testStruct
 where
  f v = do
    let action = pretravsValM idm rootValAddr v
    result <- runExceptT $ runRWST action emptyReduceConfig (emptyContext noopTraceSink)
    pure $ fmap (\(vals, _, _) -> vals) result

  idm :: ValAddr -> Val -> RM Val
  idm _ v = return v

posttravsVCB :: Weigh ()
posttravsVCB = io "posttravsVC" f testStruct
 where
  f v = do
    let
      action :: RM Val
      action = do
        vc <- postVisitValSimple (subNodes False) return (VCur{focus = v, crumbs = [(rootFeature, mkNewVal VNTop)]})
        return $ focus vc
    result <- runExceptT $ runRWST action emptyReduceConfig (emptyContext noopTraceSink)
    pure $ fmap (\(vals, _, _) -> vals) result

  idm :: ValAddr -> Val -> RM Val
  idm _ v = return v

noopTraceSink :: LB.ByteString -> IO ()
noopTraceSink _ = pure ()
