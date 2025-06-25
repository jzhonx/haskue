{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import qualified Common
import Control.DeepSeq (NFData (..))
import Data.Foldable (toList)
import Data.List (intercalate)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import GHC.Generics (Generic)
import qualified Path
import Value.Atom

data RefArg t
  = -- | RefPath denotes a reference starting with an identifier.
    RefPath T.Text (Seq.Seq t)
  | -- | RefIndex denotes a reference starts with an in-place value. For example, ({x:1}.x).
    RefIndex (Seq.Seq t)
  deriving (Generic, NFData)

data Reference t = Reference
  { refArg :: RefArg t
  , refOrigAddrs :: Maybe Path.TreeAddr
  -- ^ refOrigAddrs indicates whether the reference is in a scope that is copied and evaluated from another
  -- expression.
  -- If it is, the address of the scope is stored here.
  -- When dereferencing the reference, the correct scope is the one stored in refOrigAddrs.
  -- The address is the abs address of the value in the subtree.
  , refVers :: Maybe Int
  -- ^ refVers records the version of the referenced value.
  , refValue :: Maybe t
  }
  deriving (Show, Generic, NFData)

instance Show (RefArg t) where
  show (RefPath s _) = "ref_v_" ++ show s
  show (RefIndex _) = "index"

instance (Eq t) => Eq (RefArg t) where
  (==) (RefPath s1 xs1) (RefPath s2 xs2) = s1 == s2 && xs1 == xs2
  (==) (RefIndex xs1) (RefIndex xs2) = xs1 == xs2
  (==) _ _ = False

instance (Eq t) => Eq (Reference t) where
  (==) r1 r2 = refArg r1 == refArg r2 && refOrigAddrs r1 == refOrigAddrs r2

showRefArg :: RefArg t -> (t -> Maybe String) -> String
showRefArg (RefPath s xs) f = intercalate "." (show s : map (\x -> maybe "_" id (f x)) (toList xs))
showRefArg (RefIndex xs) f = "index." ++ intercalate "." (map (\x -> maybe "_" id (f x)) (toList xs))

refHasRefPath :: Reference t -> Bool
refHasRefPath r = case refArg r of
  RefPath _ _ -> True
  RefIndex _ -> False

getIndexSegs :: Reference t -> Maybe (Seq.Seq t)
getIndexSegs r = case refArg r of
  RefPath _ _ -> Nothing
  RefIndex xs -> Just xs

valPathFromRefArg :: (t -> Maybe Atom) -> RefArg t -> Maybe Path.ValPath
valPathFromRefArg treeToA arg = case arg of
  RefPath var xs -> do
    sels <-
      mapM
        ( \x -> case treeToA x of
            Just (String s) -> return $ Path.StringSel (TE.encodeUtf8 s)
            Just (Int i) -> return $ Path.IntSel (fromIntegral i)
            _ -> Nothing
        )
        (toList xs)
    return $ Path.ValPath (Path.StringSel (TE.encodeUtf8 var) : sels)
  -- RefIndex does not start with a string.
  RefIndex _ -> Nothing

valPathFromRef :: (t -> Maybe Atom) -> Reference t -> Maybe Path.ValPath
valPathFromRef treeToA ref = valPathFromRefArg treeToA (refArg ref)

appendRefArg :: t -> RefArg t -> RefArg t
appendRefArg y (RefPath s xs) = RefPath s (xs Seq.|> y)
appendRefArg y (RefIndex xs) = RefIndex (xs Seq.|> y)

subRefArgs :: RefArg t -> Seq.Seq t
subRefArgs (RefPath _ xs) = xs
subRefArgs (RefIndex xs) = xs

modifySubRefArgs :: (Seq.Seq t -> Seq.Seq t) -> RefArg t -> RefArg t
modifySubRefArgs f (RefPath s xs) = RefPath s (f xs)
modifySubRefArgs f (RefIndex xs) = RefIndex (f xs)

mkIndexRef :: Seq.Seq t -> Reference t
mkIndexRef ts =
  Reference
    { refArg = RefIndex ts
    , refValue = Nothing
    , refOrigAddrs = Nothing
    , refVers = Nothing
    }

emptyIdentRef :: T.Text -> Reference t
emptyIdentRef ident =
  Reference
    { refArg = RefPath ident Seq.empty
    , refOrigAddrs = Nothing
    , refValue = Nothing
    , refVers = Nothing
    }

mkRefFromValPath :: (Common.Env r s m) => (Atom -> t) -> T.Text -> Path.ValPath -> m (Reference t)
mkRefFromValPath aToTree var (Path.ValPath xs) = do
  ys <-
    mapM
      ( \y -> case y of
          Path.StringSel s -> do
            case TE.decodeUtf8' s of
              Left err -> throwErrSt (show err)
              Right str -> return $ aToTree (String str)
          Path.IntSel i -> return $ aToTree (Int $ fromIntegral i)
      )
      xs
  return $
    Reference
      { refArg = RefPath var (Seq.fromList ys)
      , refValue = Nothing
      , refOrigAddrs = Nothing
      , refVers = Nothing
      }