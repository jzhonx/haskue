{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import qualified Common
import Data.Foldable (toList)
import Data.List (intercalate)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Exception (throwErrSt)
import GHC.Generics (Generic)
import Path
import Value.Atom
import {-# SOURCE #-} Value.Tree

data Reference = Reference
  { refArg :: RefArg
  , refOrigAddrs :: Maybe TreeAddr
  -- ^ refOrigAddrs indicates whether the reference is in a scope that is copied and evaluated from another
  -- expression.
  -- If it is, the address of the scope is stored here.
  -- When dereferencing the reference, the correct scope is the one stored in refOrigAddrs.
  -- The address is the abs address of the value in the subtree.
  , refVers :: Maybe Int
  -- ^ refVers records the version of the referenced value.
  , refValue :: Maybe Tree
  }
  deriving (Generic)

data RefArg
  = -- | RefPath denotes a reference starting with an identifier.
    RefPath T.Text (Seq.Seq Tree)
  | -- | RefIndex denotes a reference starts with an in-place value. For example, ({x:1}.x).
    RefIndex (Seq.Seq Tree)
  deriving (Generic)

showRefArg :: RefArg -> (Tree -> Maybe String) -> String
showRefArg (RefPath s xs) f = intercalate "." (show s : map (\x -> maybe "_" id (f x)) (toList xs))
showRefArg (RefIndex xs) f = "index." ++ intercalate "." (map (\x -> maybe "_" id (f x)) (toList xs))

refHasRefPath :: Reference -> Bool
refHasRefPath r = case refArg r of
  RefPath _ _ -> True
  RefIndex _ -> False

getIndexSegs :: Reference -> Maybe (Seq.Seq Tree)
getIndexSegs r = case refArg r of
  RefPath _ _ -> Nothing
  RefIndex xs -> Just xs

valPathFromRefArg :: (Tree -> Maybe Atom) -> RefArg -> Maybe ValPath
valPathFromRefArg treeToA arg = case arg of
  RefPath var xs -> do
    sels <-
      mapM
        ( \x -> case treeToA x of
            Just (String s) -> return $ StringSel (TE.encodeUtf8 s)
            Just (Int i) -> return $ IntSel (fromIntegral i)
            _ -> Nothing
        )
        (toList xs)
    return $ ValPath (StringSel (TE.encodeUtf8 var) : sels)
  -- RefIndex does not start with a string.
  RefIndex _ -> Nothing

valPathFromRef :: (Tree -> Maybe Atom) -> Reference -> Maybe ValPath
valPathFromRef treeToA ref = valPathFromRefArg treeToA (refArg ref)

appendRefArg :: Tree -> RefArg -> RefArg
appendRefArg y (RefPath s xs) = RefPath s (xs Seq.|> y)
appendRefArg y (RefIndex xs) = RefIndex (xs Seq.|> y)

subRefArgs :: RefArg -> Seq.Seq Tree
subRefArgs (RefPath _ xs) = xs
subRefArgs (RefIndex xs) = xs

modifySubRefArgs :: (Seq.Seq Tree -> Seq.Seq Tree) -> RefArg -> RefArg
modifySubRefArgs f (RefPath s xs) = RefPath s (f xs)
modifySubRefArgs f (RefIndex xs) = RefIndex (f xs)

mkIndexRef :: Seq.Seq Tree -> Reference
mkIndexRef ts =
  Reference
    { refArg = RefIndex ts
    , refValue = Nothing
    , refOrigAddrs = Nothing
    , refVers = Nothing
    }

emptyIdentRef :: T.Text -> Reference
emptyIdentRef ident =
  Reference
    { refArg = RefPath ident Seq.empty
    , refOrigAddrs = Nothing
    , refValue = Nothing
    , refVers = Nothing
    }

mkRefFromValPath :: (Common.Env r s m) => (Atom -> Tree) -> T.Text -> ValPath -> m Reference
mkRefFromValPath aToTree var (ValPath xs) = do
  ys <-
    mapM
      ( \y -> case y of
          StringSel s -> do
            case TE.decodeUtf8' s of
              Left err -> throwErrSt (show err)
              Right str -> return $ aToTree (String str)
          IntSel i -> return $ aToTree (Int $ fromIntegral i)
      )
      xs
  return $
    Reference
      { refArg = RefPath var (Seq.fromList ys)
      , refValue = Nothing
      , refOrigAddrs = Nothing
      , refVers = Nothing
      }