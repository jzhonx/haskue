{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- {-# LANGUAGE FunctionalDependencies #-}

module Cursor where

import Common
import Data.ByteString.Builder (
  Builder,
  char7,
  string7,
  toLazyByteString,
 )
import qualified Data.ByteString.Lazy.Char8 as LBS
import Exception (throwErrSt)
import Path (TASeg, TreeAddr (TreeAddr))

class HasTreeCursor s t where
  getTreeCursor :: s -> TreeCursor t
  setTreeCursor :: s -> TreeCursor t -> s

-- class HasCtxVal s t a | s -> a, s -> t where
--   getCtxVal :: s -> CtxVal t a
--   setCtxVal :: s -> CtxVal t a -> s

-- data CtxVal t a = CtxVal
--   { cvVal :: a
--   , cvCtx :: Context t
--   }

-- instance Functor (CtxVal t) where
--   fmap f c = c{cvVal = f (cvVal c)}

-- instance HasCtxVal (CtxVal t a) t a where
--   getCtxVal = id
--   setCtxVal _ x = x

-- instance HasTrace (CtxVal t a) where
--   getTrace = ctxTrace . cvCtx
--   setTrace cv tr = cv{cvCtx = (cvCtx cv){ctxTrace = tr}}

-- instance IDStore (CtxVal t a) where
--   getID cv = ctxObjID (cvCtx cv)
--   setID cv i = cv{cvCtx = (cvCtx cv){ctxObjID = i}}

-- mkCtxVal :: TreeCursor t -> Int -> Trace -> CtxVal t a
-- mkCtxVal cur objID trace =
--   CtxVal
--     { cvVal = tcFocus cur
--     , cvCtx = emptyContext{ctxCrumbs = tcCrumbs cur, ctxObjID = objID, ctxTrace = trace}
--     }

-- type CtxTree t = CtxVal t t

type TreeCrumb t = (TASeg, t)

-- ctxTreeAddr :: Context t -> TreeAddr
-- ctxTreeAddr = addrFromCrumbs . ctxCrumbs

addrFromCrumbs :: [TreeCrumb t] -> TreeAddr
addrFromCrumbs crumbs = TreeAddr . reverse $ go crumbs []
 where
  go :: [TreeCrumb t] -> [TASeg] -> [TASeg]
  go [] acc = acc
  go ((n, _) : cs) acc = go cs (n : acc)

-- cvTreeAddr :: CtxVal t a -> TreeAddr
-- cvTreeAddr = ctxTreeAddr . cvCtx

-- getCVCursor :: CtxVal t a -> TreeCursor t
-- getCVCursor cv = TreeCursor (cvVal cv) (ctxCrumbs . cvCtx $ cv)

-- emptyContext :: Context t
-- emptyContext =
--   Context
--     { ctxCrumbs = []
--     , ctxObjID = 0
--     , ctxReduceStack = []
--     , ctxRefSysGraph = Map.empty
--     , ctxRefSysQueue = []
--     , ctxRefSysEnabled = True
--     , ctxTrace = emptyTrace
--     }

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
data TreeCursor t = TreeCursor
  { tcFocus :: t
  , tcCrumbs :: [TreeCrumb t]
  }
  deriving (Eq)

instance (Show t) => Show (TreeCursor t) where
  show = showCursor

setTCFocus :: t -> TreeCursor t -> TreeCursor t
setTCFocus t (TreeCursor _ cs) = TreeCursor t cs

tcTreeAddr :: TreeCursor t -> TreeAddr
tcTreeAddr c = addrFromCrumbs (tcCrumbs c)

-- | Get the parent of the cursor without propagating the value up.
parentTC :: TreeCursor t -> Maybe (TreeCursor t)
parentTC (TreeCursor _ []) = Nothing
parentTC (TreeCursor _ ((_, t) : cs)) = Just $ TreeCursor t cs

parentTCMust :: (Env r s m) => TreeCursor t -> m (TreeCursor t)
parentTCMust tc = maybe (throwErrSt "already top") return (parentTC tc)

-- | Get the segment paired with the focus of the cursor.
focusTCSeg :: (Env r s m) => TreeCursor t -> m TASeg
focusTCSeg (TreeCursor _ []) = throwErrSt "already at the top"
focusTCSeg tc = return $ fst . head $ tcCrumbs tc

isTCTop :: TreeCursor t -> Bool
isTCTop (TreeCursor _ []) = True
isTCTop _ = False

showCursor :: (Show t) => TreeCursor t -> String
showCursor tc = LBS.unpack $ toLazyByteString $ prettyBldr tc
 where
  prettyBldr :: (Show t) => TreeCursor t -> Builder
  prettyBldr (TreeCursor t cs) =
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

mkSubTC :: TASeg -> t -> TreeCursor t -> TreeCursor t
mkSubTC seg a tc = TreeCursor a ((seg, tcFocus tc) : tcCrumbs tc)
