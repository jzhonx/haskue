{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Cursor where

import Class
import Data.ByteString.Builder (
  Builder,
  char7,
  string7,
  toLazyByteString,
 )
import qualified Data.ByteString.Lazy.Char8 as LBS
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Env
import Error
import Path
import Util

class HasCtxVal s t a | s -> a, s -> t where
  getCtxVal :: s -> CtxVal t a
  setCtxVal :: s -> CtxVal t a -> s

data CtxVal t a = CtxVal
  { cvVal :: a
  , cvCtx :: Context t
  }

instance Functor (CtxVal t) where
  fmap f c = c{cvVal = f (cvVal c)}

instance HasCtxVal (CtxVal t a) t a where
  getCtxVal = id
  setCtxVal _ x = x

instance HasTrace (CtxVal t a) where
  getTrace = ctxTrace . cvCtx
  setTrace cv tr = cv{cvCtx = (cvCtx cv){ctxTrace = tr}}

cvFromCur :: ValCursor t a -> CtxVal t a
cvFromCur cur =
  CtxVal
    { cvVal = vcFocus cur
    , cvCtx = emptyContext{ctxCrumbs = vcCrumbs cur}
    }

type CtxTree t = CtxVal t t

data Context t = Context
  { ctxCrumbs :: [TreeCrumb t]
  , ctxReduceStack :: [Path]
  , ctxNotifiers :: Map.Map Path [Path]
  , ctxTrace :: Trace
  }
  deriving (Eq, Show)

type TreeCrumb t = (Selector, t)

ctxPath :: Context t -> Path
ctxPath = pathFromCrumbs . ctxCrumbs

pathFromCrumbs :: [TreeCrumb t] -> Path
pathFromCrumbs crumbs = Path . reverse $ go crumbs []
 where
  go :: [TreeCrumb t] -> [Selector] -> [Selector]
  go [] acc = acc
  go ((n, _) : cs) acc = go cs (n : acc)

cvPath :: CtxVal t a -> Path
cvPath = ctxPath . cvCtx

getCVCursor :: CtxVal t a -> ValCursor t a
getCVCursor cv = ValCursor (cvVal cv) (ctxCrumbs . cvCtx $ cv)

emptyContext :: Context t
emptyContext =
  Context
    { ctxCrumbs = []
    , ctxReduceStack = []
    , ctxNotifiers = Map.empty
    , ctxTrace = emptyTrace
    }

{- | Add a notifier pair to the context.
The first element is the source path, which is the path that is being watched.
The second element is the dependent path, which is the path that is watching the source path.
-}
addCtxNotifier :: Context t -> (Path, Path) -> Context t
addCtxNotifier ctx (src, dep) = ctx{ctxNotifiers = Map.insert src newDepList oldMap}
 where
  oldMap = ctxNotifiers ctx
  depList = fromMaybe [] $ Map.lookup src oldMap
  newDepList = if dep `elem` depList then depList else dep : depList

type TreeCursor t = ValCursor t t

{- | TreeCursor is a pair of a value and a list of crumbs.
For example,
{
a: {
  b: {
    c: 42
  } // struct_c
} // struct_b
} // struct_a
Suppose the cursor is at the struct that contains the value 42. The cursor is
(struct_c, [("b", struct_b), ("a", struct_a)]).
-}
data ValCursor t a = ValCursor
  { vcFocus :: a
  , vcCrumbs :: [TreeCrumb t]
  }
  deriving (Eq)

instance (Show t, Show a) => Show (ValCursor t a) where
  show = showCursor

instance Functor (ValCursor t) where
  fmap f (ValCursor t cs) = ValCursor (f t) cs

tcPath :: ValCursor t a -> Path
tcPath c = pathFromCrumbs (vcCrumbs c)

parentTC :: TreeCursor t -> Maybe (TreeCursor t)
parentTC (ValCursor _ []) = Nothing
parentTC (ValCursor _ ((_, t) : cs)) = Just $ ValCursor t cs

showCursor :: (Show t, Show a) => ValCursor t a -> String
showCursor tc = LBS.unpack $ toLazyByteString $ prettyBldr tc
 where
  prettyBldr :: (Show t, Show a) => ValCursor t a -> Builder
  prettyBldr (ValCursor t cs) =
    string7 "-- ():\n"
      <> string7 (show t)
      <> char7 '\n'
      <> foldl
        ( \b (sel, n) ->
            b
              <> string7 "-- "
              <> string7 (show sel)
              <> char7 ':'
              <> char7 '\n'
              <> string7 (show n)
              <> char7 '\n'
        )
        mempty
        cs

mkSubTC :: Selector -> a -> TreeCursor t -> ValCursor t a
mkSubTC sel a tc = ValCursor a ((sel, vcFocus tc) : vcCrumbs tc)

goDownTCPath :: (TreeOp t) => Path -> TreeCursor t -> Maybe (TreeCursor t)
goDownTCPath (Path sels) = go (reverse sels)
 where
  go :: (TreeOp t) => [Selector] -> TreeCursor t -> Maybe (TreeCursor t)
  go [] cursor = Just cursor
  go (x : xs) cursor = do
    nextCur <- goDownTCSel x cursor
    go xs nextCur

{- | Go down the TreeCursor with the given selector and return the new cursor.
It handles the case when the current node is a disjunction node.
-}
goDownTCSel :: (TreeOp t) => Selector -> TreeCursor t -> Maybe (TreeCursor t)
goDownTCSel sel tc = do
  nextTree <- subTree sel (vcFocus tc)
  return $ mkSubTC sel nextTree tc

-- | propUp propagates the changes made to the focus of the block to the parent block.
propValUp :: (Env m, TreeOp t) => TreeCursor t -> m (TreeCursor t)
propValUp tc@(ValCursor _ []) = return tc
propValUp (ValCursor subT ((sel, parT) : cs)) = do
  t <- setSubTree sel subT parT
  return $ ValCursor t cs

-- | Propagate the value up until the lowest selector is matched.
propUpTCUntil :: (Env m, TreeOp t) => Selector -> TreeCursor t -> m (TreeCursor t)
propUpTCUntil _ (ValCursor _ []) = throwErrSt "already at the top"
propUpTCUntil sel tc@(ValCursor _ ((s, _) : _))
  | s == sel = return tc
  | otherwise = propValUp tc >>= propUpTCUntil sel

{- | Search the tree cursor up to the root and return the tree cursor that points to the variable.
The cursor will also be propagated to the parent block.
-}
searchTCVar :: (Env m, TreeOp t) => Selector -> TreeCursor t -> m (Maybe (TreeCursor t))
searchTCVar sel@(StructSelector ssel@(StringSelector _)) tc =
  maybe
    (goUp tc)
    (\field -> return . Just $ mkSubTC sel field tc)
    (getVarField ssel $ vcFocus tc)
 where
  goUp :: (Env m, TreeOp t) => TreeCursor t -> m (Maybe (TreeCursor t))
  goUp (ValCursor _ [(RootSelector, _)]) = return Nothing
  goUp utc = propValUp utc >>= searchTCVar sel
searchTCVar _ _ = return Nothing
