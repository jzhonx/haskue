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
traceSpanTM name = traceActionTM name Nothing ttoJSON

traceSpanArgsTM :: (ToJSONWTIndexer a) => String -> String -> RM a -> RM a
traceSpanArgsTM name args = traceActionTM name (Just args) ttoJSON

traceSpanAdaptTM :: String -> (a -> RM Value) -> RM a -> RM a
traceSpanAdaptTM name = traceActionTM name Nothing

traceSpanArgsAdaptTM :: String -> String -> (a -> RM Value) -> RM a -> RM a
traceSpanArgsAdaptTM name args = traceActionTM name (Just args)

traceActionTM :: String -> Maybe String -> (a -> RM Value) -> RM a -> RM a
traceActionTM name argsM jsonfy f = withAddrAndFocus $ \addr _ ->
  traceAction name addr argsM jsonfy False f

traceAction :: String -> ValAddr -> Maybe String -> (a -> RM Value) -> Bool -> RM a -> RM a
traceAction name addr argsM jsonfy ignoreFocus f = whenTraceEnabled name f do
  let isRoot = addr == rootValAddr
  bTraced <- getTMVal >>= spanTreeMsgs isRoot ignoreFocus
  addrS <- tshow addr
  trID <- getTraceID
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  let
    header = T.pack $ printf "%s, at:%s" name addrS

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

debugInstantTM :: String -> RM T.Text -> RM ()
debugInstantTM name margs = withAddrAndFocus $ \addr _ -> do
  args <- margs
  debugInst name (T.unpack args) addr

debugInst :: String -> String -> ValAddr -> RM ()
debugInst name args addr = whenTraceEnabled name (return ()) $ do
  addrS <- tshow addr
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  trID <- getTraceID
  debugInstant
    (T.pack name)
    ( toJSON $
        RMInstantTraceArgs
          { ctiTraceID = trID
          , ctiAddr = addrS
          , ctiCustomVal = optVal extraInfo (toJSON args)
          }
    )

traceSpanRMTC :: (ToJSONWTIndexer a) => String -> VCur -> RM a -> RM a
traceSpanRMTC name = traceActionRM name Nothing ttoJSON

traceSpanArgsRMTC :: (ToJSONWTIndexer a) => String -> String -> VCur -> RM a -> RM a
traceSpanArgsRMTC name args = traceActionRM name (Just args) ttoJSON

traceSpanAdaptRM :: String -> (a -> RM Value) -> VCur -> RM a -> RM a
traceSpanAdaptRM name = traceActionRM name Nothing

traceSpanArgsAdaptRM :: String -> String -> (a -> RM Value) -> VCur -> RM a -> RM a
traceSpanArgsAdaptRM name args = traceActionRM name (Just args)

traceActionRM :: String -> Maybe String -> (a -> RM Value) -> VCur -> RM a -> RM a
traceActionRM name argsM resFetch vc = traceAction name (vcAddr vc) argsM resFetch True

debugInstantRM :: String -> String -> VCur -> RM ()
debugInstantRM name args vc = debugInst name args (vcAddr vc)

debugInstantOpRM :: String -> String -> ValAddr -> RM ()
debugInstantOpRM = debugInst

emptySpanValue :: a -> RM Value
emptySpanValue _ = return $ toJSON ()