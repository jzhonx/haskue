{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Cursor where

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
import Exception (throwErrSt)
import Path (TASeg, TreeAddr (TreeAddr))
import Util (HasTrace (..), Trace, emptyTrace)

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
  , ctxObjID :: Int
  , ctxReduceStack :: [TreeAddr]
  , ctxNotifEnabled :: Bool
  , ctxNotifGraph :: Map.Map TreeAddr [TreeAddr]
  , ctxNotifQueue :: [TreeAddr]
  -- ^ The notif queue is a list of addresses that will trigger the notification.
  , ctxCnstrValidatorAddr :: Maybe TreeAddr
  , ctxTrace :: Trace
  }
  deriving (Eq, Show)

type TreeCrumb t = (TASeg, t)

ctxTreeAddr :: Context t -> TreeAddr
ctxTreeAddr = addrFromCrumbs . ctxCrumbs

addrFromCrumbs :: [TreeCrumb t] -> TreeAddr
addrFromCrumbs crumbs = TreeAddr . reverse $ go crumbs []
 where
  go :: [TreeCrumb t] -> [TASeg] -> [TASeg]
  go [] acc = acc
  go ((n, _) : cs) acc = go cs (n : acc)

cvTreeAddr :: CtxVal t a -> TreeAddr
cvTreeAddr = ctxTreeAddr . cvCtx

getCVCursor :: CtxVal t a -> ValCursor t a
getCVCursor cv = ValCursor (cvVal cv) (ctxCrumbs . cvCtx $ cv)

emptyContext :: Context t
emptyContext =
  Context
    { ctxCrumbs = []
    , ctxObjID = 0
    , ctxReduceStack = []
    , ctxNotifGraph = Map.empty
    , ctxNotifQueue = []
    , ctxNotifEnabled = True
    , ctxCnstrValidatorAddr = Nothing
    , ctxTrace = emptyTrace
    }

{- | Add a notifier pair to the context.
The first element is the source addr, which is the addr that is being watched.
The second element is the dependent addr, which is the addr that is watching the source addr.
-}
addCtxNotifier :: Context t -> (TreeAddr, TreeAddr) -> Context t
addCtxNotifier ctx (src, dep) = ctx{ctxNotifGraph = Map.insert src newDepList oldMap}
 where
  oldMap = ctxNotifGraph ctx
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

tcTreeAddr :: ValCursor t a -> TreeAddr
tcTreeAddr c = addrFromCrumbs (vcCrumbs c)

-- | Get the parent of the cursor without propagating the value up.
parentTC :: TreeCursor t -> Maybe (TreeCursor t)
parentTC (ValCursor _ []) = Nothing
parentTC (ValCursor _ ((_, t) : cs)) = Just $ ValCursor t cs

-- | Get the segment paired with the focus of the cursor.
focusTCSeg :: (Env m) => TreeCursor t -> m TASeg
focusTCSeg (ValCursor _ []) = throwErrSt "already at the top"
focusTCSeg tc = return $ fst . head $ vcCrumbs tc

isTCTop :: TreeCursor t -> Bool
isTCTop (ValCursor _ []) = True
isTCTop _ = False

showCursor :: (Show t, Show a) => ValCursor t a -> String
showCursor tc = LBS.unpack $ toLazyByteString $ prettyBldr tc
 where
  prettyBldr :: (Show t, Show a) => ValCursor t a -> Builder
  prettyBldr (ValCursor t cs) =
    string7 "-- ():\n"
      <> string7 (show t)
      <> char7 '\n'
      <> foldl
        ( \b (seg, n) ->
            b
              <> string7 "-- "
              <> string7 (show seg)
              <> char7 ':'
              <> char7 '\n'
              <> string7 (show n)
              <> char7 '\n'
        )
        mempty
        cs

showNotifiers :: Map.Map TreeAddr [TreeAddr] -> String
showNotifiers notifiers =
  let s = Map.foldrWithKey go "" notifiers
   in if null s then "[]" else "[" ++ s ++ "\n]"
 where
  go :: TreeAddr -> [TreeAddr] -> String -> String
  go src deps acc = acc ++ "\n" ++ show src ++ " -> " ++ show deps

mkSubTC :: TASeg -> a -> TreeCursor t -> ValCursor t a
mkSubTC seg a tc = ValCursor a ((seg, vcFocus tc) : vcCrumbs tc)