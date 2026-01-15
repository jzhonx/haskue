{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.TraceSpan where

import Control.Monad.Reader (asks)
import Cursor
import Data.Aeson (KeyValue (..), ToJSON, Value, toJSON)
import Data.Aeson.Types (object)
import qualified Data.Set as Set
import qualified Data.Text as T
import Env (
  Config (..),
 )
import Feature
import Reduce.Monad (
  RM,
  baseConfig,
  getTMVal,
  withAddrAndFocus,
 )
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (ttoJSON))
import Text.Printf (printf)
import Util.Trace (debugInstant, getTraceID, traceSpanExec, traceSpanStart)
import Value
import Value.Export.Debug

data RMStartTraceArgs = RMStartTraceArgs
  { cstaTraceID :: !Int
  , cstaAddr :: !T.Text
  , cstaBeforeFocus :: !Value
  , cstaCustomVal :: !Value
  }
  deriving (Eq, Show)

instance ToJSON RMStartTraceArgs where
  toJSON cta =
    object
      [ "traceid" .= show (cstaTraceID cta)
      , "addr" .= cstaAddr cta
      , "bfcs" .= cstaBeforeFocus cta
      , "ctm" .= cstaCustomVal cta
      ]

data RMEndTraceArgs = RMEndTraceArgs
  { cetaResVal :: !Value
  , cetaFocus :: !Value
  }
  deriving (Eq, Show)

instance ToJSON RMEndTraceArgs where
  toJSON cta =
    object
      [ "res" .= cetaResVal cta
      , "fcs" .= cetaFocus cta
      ]

data RMInstantTraceArgs = RMInstantTraceArgs
  { ctiTraceID :: !Int
  , ctiAddr :: !T.Text
  , ctiCustomVal :: !Value
  }
  deriving (Eq, Show)

instance ToJSON RMInstantTraceArgs where
  toJSON c =
    object
      [ "traceid" .= show (ctiTraceID c)
      , "addr" .= ctiAddr c
      , "ctm" .= ctiCustomVal c
      ]

whenTraceEnabled :: String -> RM a -> RM a -> RM a
whenTraceEnabled name f traced = do
  Config{stTraceEnable = traceEnable, stTraceFilter = tFilter} <-
    asks baseConfig
  if traceEnable && (Set.null tFilter || Set.member name tFilter)
    then traced
    else f

spanTreeMsgs :: Bool -> Bool -> Val -> RM Value
spanTreeMsgs isTreeRoot ignore t = do
  Config{stTracePrintTree = tracePrintTree} <- asks baseConfig
  if not tracePrintTree || ignore
    then return $ object []
    else do
      rep <- buildRepVal t (defaultValRepBuildOption{trboRepSubFields = isTreeRoot})
      return $ toJSON rep

traceSpanTM :: (ToJSONWTIndexer a) => String -> RM a -> RM a
traceSpanTM name = traceActionTM name (const $ return Nothing) ttoJSON

traceSpanArgsTM :: (ToJSONWTIndexer a) => String -> (() -> RM String) -> RM a -> RM a
traceSpanArgsTM name args = traceActionTM name ((Just <$>) <$> args) ttoJSON

traceSpanAdaptTM :: String -> (a -> RM Value) -> RM a -> RM a
traceSpanAdaptTM name = traceActionTM name (const $ return Nothing)

traceSpanArgsAdaptTM :: String -> (() -> RM String) -> (a -> RM Value) -> RM a -> RM a
traceSpanArgsAdaptTM name args = traceActionTM name ((Just <$>) <$> args)

traceActionTM :: String -> (() -> RM (Maybe String)) -> (a -> RM Value) -> RM a -> RM a
traceActionTM name argsM jsonfy f = withAddrAndFocus $ \addr _ ->
  traceAction name addr argsM jsonfy False f

traceSpanRMTC :: (ToJSONWTIndexer a) => String -> VCur -> RM a -> RM a
traceSpanRMTC name = traceActionRM name (const $ return Nothing) ttoJSON

traceSpanArgsRMTC :: (ToJSONWTIndexer a) => String -> (() -> RM String) -> VCur -> RM a -> RM a
traceSpanArgsRMTC name args = traceActionRM name ((Just <$>) <$> args) ttoJSON

traceSpanAdaptRM :: String -> (a -> RM Value) -> VCur -> RM a -> RM a
traceSpanAdaptRM name = traceActionRM name (const $ return Nothing)

traceSpanArgsAdaptRM :: String -> (() -> RM String) -> (a -> RM Value) -> VCur -> RM a -> RM a
traceSpanArgsAdaptRM name args = traceActionRM name ((Just <$>) <$> args)

traceActionRM :: String -> (() -> RM (Maybe String)) -> (a -> RM Value) -> VCur -> RM a -> RM a
traceActionRM name argsM resFetch vc = traceAction name (vcAddr vc) argsM resFetch True

traceAction :: String -> ValAddr -> (() -> RM (Maybe String)) -> (a -> RM Value) -> Bool -> RM a -> RM a
traceAction name addr argsMGen jsonfy ignoreFocus f = whenTraceEnabled name f do
  let isRoot = addr == rootValAddr
  bTraced <- getTMVal >>= spanTreeMsgs isRoot ignoreFocus
  addrS <- tshow addr
  trID <- getTraceID
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  let
    header = T.pack $ printf "%s, at:%s" name addrS

  argsM <- argsMGen ()
  traceSpanStart
    header
    ( toJSON $
        RMStartTraceArgs
          { cstaTraceID = trID
          , cstaAddr = addrS
          , cstaBeforeFocus = optVal extraInfo bTraced
          , cstaCustomVal = optVal extraInfo (toJSON argsM)
          }
    )

  res <- f
  resVal <- jsonfy res
  resFocus <- getTMVal >>= spanTreeMsgs isRoot ignoreFocus

  traceSpanExec
    header
    ( toJSON $
        RMEndTraceArgs
          { cetaResVal = optVal extraInfo resVal
          , cetaFocus = optVal extraInfo resFocus
          }
    )
  return res

optVal :: Bool -> Value -> Value
optVal extraInfo v = if extraInfo then v else object []

emptySpanValue :: a -> RM Value
emptySpanValue _ = return $ toJSON ()

-- === Debug instant traces ===

debugInstantRM :: String -> (() -> RM String) -> VCur -> RM ()
debugInstantRM name args vc = debugInst name args (vcAddr vc)

debugInstantOpRM :: String -> (() -> RM String) -> ValAddr -> RM ()
debugInstantOpRM = debugInst

debugInstantTM :: String -> RM T.Text -> RM ()
debugInstantTM name margs = withAddrAndFocus $ \addr _ -> debugInst name (const $ T.unpack <$> margs) addr

debugInst :: String -> (() -> RM String) -> ValAddr -> RM ()
debugInst name argsGen addr = whenTraceEnabled name (return ()) $ do
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  trID <- getTraceID
  args <- argsGen ()
  debugInstant
    (T.pack name)
    ( toJSON $
        RMInstantTraceArgs
          { ctiTraceID = trID
          , ctiAddr = addrS
          , ctiCustomVal = optVal extraInfo (toJSON args)
          }
    )