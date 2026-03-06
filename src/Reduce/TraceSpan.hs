{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.TraceSpan where

import Control.Monad.Reader (asks)
import Data.Aeson (KeyValue (..), ToJSON, Value, toJSON)
import Data.Aeson.Types (object)
import qualified Data.Set as Set
import qualified Data.Text as T
import Env (Config (..))
import Feature
import Reduce.Monad (
  RM,
  baseConfig,
 )
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (ttoJSON))
import Text.Printf (printf)
import Util.Trace (debugInstant, getTraceID, traceSpanExec, traceSpanStart)
import Value
import Value.Export.Debug

data RMStartTraceArgs = RMStartTraceArgs
  { cstaTraceID :: !Int
  , cstaAddr :: !T.Text
  , cstaBefore :: !Value
  , cstaCustomVal :: !Value
  }
  deriving (Eq, Show)

instance ToJSON RMStartTraceArgs where
  toJSON cta =
    object
      [ "traceid" .= show (cstaTraceID cta)
      , "addr" .= cstaAddr cta
      , "before" .= cstaBefore cta
      , "ctm" .= cstaCustomVal cta
      ]

newtype RMEndTraceArgs = RMEndTraceArgs
  { cetaResult :: Value
  }
  deriving (Eq, Show)

instance ToJSON RMEndTraceArgs where
  toJSON cta = object ["after" .= cetaResult cta]

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
  Config{stTraceEnable = traceEnable, stTraceFilter = tFilter} <- asks baseConfig
  if traceEnable && (Set.null tFilter || Set.member name tFilter)
    then traced
    else f

valDebugRepJSON :: ValAddr -> Val -> RM Value
valDebugRepJSON addr v = do
  let isRoot = addr == rootValAddr
  rep <- buildRepVal v (defaultValRepBuildOption{trboRepSubFields = isRoot})
  return $ toJSON rep

valDebugRep :: ValAddr -> Val -> RM String
valDebugRep addr v = do
  let isRoot = addr == rootValAddr
  rep <- buildRepVal v (defaultValRepBuildOption{trboRepSubFields = isRoot})
  return $ repToString 0 rep

traceSpanTM :: (ToJSONWTIndexer a) => String -> ValAddr -> RM Value -> RM a -> RM a
traceSpanTM name addr beforeM = traceAction name addr beforeM (const $ return Nothing) ttoJSON

traceSpanArgsTM :: (ToJSONWTIndexer a) => String -> ValAddr -> RM Value -> (() -> RM String) -> RM a -> RM a
traceSpanArgsTM name addr beforeM args = traceAction name addr beforeM ((Just <$>) <$> args) ttoJSON

traceSpanAdaptTM :: String -> ValAddr -> RM Value -> (a -> RM Value) -> RM a -> RM a
traceSpanAdaptTM name addr beforeM = traceAction name addr beforeM (const $ return Nothing)

traceSpanArgsAdaptTM :: String -> ValAddr -> RM Value -> (() -> RM String) -> (a -> RM Value) -> RM a -> RM a
traceSpanArgsAdaptTM name addr beforeM args = traceAction name addr beforeM ((Just <$>) <$> args)

traceSpanValTM :: String -> ValAddr -> Val -> RM Val -> RM Val
traceSpanValTM name addr v = traceAction name addr (valDebugRepJSON addr v) (const $ return Nothing) (valDebugRepJSON addr)

traceSpanValAnyTM :: (ToJSONWTIndexer a) => String -> ValAddr -> Val -> RM a -> RM a
traceSpanValAnyTM name addr v = traceAction name addr (valDebugRepJSON addr v) (const $ return Nothing) ttoJSON

traceAction :: String -> ValAddr -> RM Value -> (() -> RM (Maybe String)) -> (b -> RM Value) -> RM b -> RM b
traceAction name addr beforeM argsMGen jsonfyb f = whenTraceEnabled name f do
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  addrS <- tshow addr
  trID <- getTraceID
  let
    header = T.pack $ printf "%s, at:%s" name addrS

  cstaBefore <- optValRM extraInfo beforeM
  cstaCustomVal <- optValRM extraInfo (toJSON <$> argsMGen ())
  traceSpanStart
    header
    ( toJSON $
        RMStartTraceArgs
          { cstaTraceID = trID
          , cstaAddr = addrS
          , cstaBefore = cstaBefore
          , cstaCustomVal = cstaCustomVal
          }
    )

  res <- f
  cetaResult <- optValRM extraInfo (jsonfyb res)
  traceSpanExec header (toJSON $ RMEndTraceArgs{cetaResult = cetaResult})
  return res

optValRM :: Bool -> RM Value -> RM Value
optValRM extraInfo f = if extraInfo then f else return $ object []

emptySpanValue :: RM Value
emptySpanValue = return $ toJSON ()

-- === Debug instant traces ===

debugInstStr :: String -> ValAddr -> (() -> RM String) -> RM ()
debugInstStr name addr f =
  debugInst
    name
    addr
    ( const $ do
        s <- f ()
        return $ toJSON s
    )

debugInstText :: String -> ValAddr -> RM T.Text -> RM ()
debugInstText name addr margs =
  debugInst name addr (const $ toJSON <$> margs)

debugInstJV :: String -> ValAddr -> RM Value -> RM ()
debugInstJV name addr margs = debugInst name addr (const margs)

debugInst :: String -> ValAddr -> (() -> RM Value) -> RM ()
debugInst name addr argsGen = whenTraceEnabled name (return ()) $ do
  addrS <- tshow addr
  trID <- getTraceID
  extraInfo <- asks (stTraceExtraInfo . baseConfig)
  ctiCustomVal <- optValRM extraInfo (toJSON <$> argsGen ())
  debugInstant
    (T.pack name)
    ( toJSON $
        RMInstantTraceArgs
          { ctiTraceID = trID
          , ctiAddr = addrS
          , ctiCustomVal = ctiCustomVal
          }
    )