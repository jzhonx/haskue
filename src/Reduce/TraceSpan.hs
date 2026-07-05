{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduce.TraceSpan where

import Control.Monad (when)
import Control.Monad.Reader (asks)
import Control.Monad.State.Strict (gets, modify')
import Data.Aeson (KeyValue (..), ToJSON, Value, toJSON)
import Data.Aeson.Types (object)
import qualified Data.Map as Map
import qualified Data.Text as T
import DepGraph (GrpAddr, lookupGrpAddr)
import Feature
import Reduce.Monad (
  RM,
  TraceConfig (..),
  debugMode,
  depGraph,
  flowIDCounter,
  flowIDMap,
  traceConfig,
 )
import StringIndex (ShowWTIndexer (..), ToJSONWTIndexer (ttoJSON))
import Text.Printf (printf)
import Util.Trace (debugInstant, emitFlowEvent, getTraceID, traceSpanExec, traceSpanStart)
import Value.Export.Debug

data RMStartTraceArgs = RMStartTraceArgs
  { cstaTraceID :: Maybe Int
  , cstaAddr :: !T.Text
  , cstaBefore :: !Value
  , cstaCustomVal :: !Value
  }
  deriving (Eq, Show)

instance ToJSON RMStartTraceArgs where
  toJSON cta =
    object $
      [ "addr" .= cstaAddr cta
      , "before" .= cstaBefore cta
      , "custom" .= cstaCustomVal cta
      ]
        ++ case cstaTraceID cta of
          Just tid -> ["traceid" .= show tid]
          Nothing -> []

newtype RMEndTraceArgs = RMEndTraceArgs
  { cetaResult :: Value
  }
  deriving (Eq, Show)

instance ToJSON RMEndTraceArgs where
  toJSON cta = object ["after" .= cetaResult cta]

data RMInstantTraceArgs = RMInstantTraceArgs
  { ctiTraceID :: Maybe Int
  , ctiAddr :: !T.Text
  , ctiCustomVal :: !Value
  }
  deriving (Eq, Show)

instance ToJSON RMInstantTraceArgs where
  toJSON c =
    object $
      [ "addr" .= ctiAddr c
      , "custom" .= ctiCustomVal c
      ]
        ++ case ctiTraceID c of
          Just tid -> ["traceid" .= show tid]
          Nothing -> []

data TracePreData = TracePreData
  { tpvVal :: Value
  , tpvArgs :: Maybe String
  }

emptyTracePreData :: TracePreData
emptyTracePreData =
  TracePreData
    { tpvVal = toJSON ()
    , tpvArgs = Nothing
    }

mkTracePreDataWithOnlyVal :: Value -> TracePreData
mkTracePreDataWithOnlyVal v = TracePreData{tpvVal = v, tpvArgs = Nothing}

traceSpanNoPreRM :: (ToJSONWTIndexer a) => String -> ValAddr -> RM a -> RM a
traceSpanNoPreRM name addr = traceSpanRM name addr emptyTracePreDataRM

emptyTracePreDataRM :: RM TracePreData
emptyTracePreDataRM = return emptyTracePreData

traceSpanRM :: (ToJSONWTIndexer a) => String -> ValAddr -> RM TracePreData -> RM a -> RM a
traceSpanRM name addr preData = traceSpanWithRM name addr preData ttoJSON

traceSpanTermsRepTM ::
  (ToJSONWTIndexer a, TermsRepShow a, ToJSONWTIndexer b, TermsRepShow b) => String -> ValAddr -> a -> RM b -> RM b
traceSpanTermsRepTM name addr a =
  traceSpanWithRM
    name
    addr
    ( do
        debugMode <- asks debugMode
        if debugMode
          then do
            rep <- termsRepToJSONWithAddr addr a
            return $ mkTracePreDataWithOnlyVal rep
          else do
            v <- ttoJSON a
            return $ mkTracePreDataWithOnlyVal v
    )
    ( \b -> do
        debugMode <- asks debugMode
        if debugMode
          then termsRepToJSONWithAddr addr b
          else ttoJSON b
    )

traceSpanTermsRepAnyTM ::
  (ToJSONWTIndexer a, TermsRepShow a, ToJSONWTIndexer b) => String -> ValAddr -> a -> RM b -> RM b
traceSpanTermsRepAnyTM name addr a =
  traceSpanWithRM
    name
    addr
    ( do
        debugMode <- asks debugMode
        if debugMode
          then do
            rep <- termsRepToJSONWithAddr addr a
            return $ mkTracePreDataWithOnlyVal rep
          else do
            v <- ttoJSON a
            return $ mkTracePreDataWithOnlyVal v
    )
    ttoJSON

traceSpanWithRM :: String -> ValAddr -> RM TracePreData -> (b -> RM Value) -> RM b -> RM b
traceSpanWithRM name addr preDataM jsonfyb f = whenTraceEnabled name addr f do
  debugMode <- asks debugMode
  addrS <- tshow addr
  trID <- getTraceID
  let header = T.pack $ printf "%s, at:%s" name addrS

  cstaBefore <- optValRM (tpvVal <$> preDataM)
  cstaCustomVal <- optValRM (toJSON . tpvArgs <$> preDataM)
  traceSpanStart
    header
    ( toJSON $
        RMStartTraceArgs
          { cstaTraceID = if debugMode then Just trID else Nothing
          , cstaAddr = addrS
          , cstaBefore = cstaBefore
          , cstaCustomVal = cstaCustomVal
          }
    )

  res <- f
  cetaResult <- optValRM (jsonfyb res)
  traceSpanExec header (toJSON $ RMEndTraceArgs{cetaResult = cetaResult})
  return res

whenTraceEnabled :: String -> ValAddr -> RM a -> RM a -> RM a
whenTraceEnabled name _addr f traced = do
  TraceConfig{stTraceEnable = traceEnable} <- asks traceConfig
  debugMode <- asks debugMode
  -- If debugMode is not enabled, we only trace the "reduce" and "recalc" functions.
  if traceEnable && (debugMode || name == "reduce" || name == "recalc")
    then traced
    else f

optValRM :: RM Value -> RM Value
optValRM f = do
  disableShowVal <- asks (stTraceDisableShowValue . traceConfig)
  if not disableShowVal then f else return $ object []

markFlowEventStart :: ValAddr -> Int -> RM ()
markFlowEventStart addr vers = case addrIsVertex addr of
  Just vAddr -> do
    flowIDMap <- gets flowIDMap
    flowIDCounter <- gets flowIDCounter
    let newFlowID = flowIDCounter + 1
    ng <- gets depGraph
    let
      r = lookupGrpAddr vAddr ng
    case r of
      Just grpAddr -> do
        modify' $ \ctx -> ctx{flowIDMap = Map.insert (grpAddr, vers) newFlowID flowIDMap, flowIDCounter = newFlowID}

        whenTraceEnabled "reduce" addr (return ()) $ emitFlowEvent "s" (T.pack $ printf "0x%x" newFlowID)
      Nothing -> return ()
  Nothing -> return ()

markFlowEventEnd :: GrpAddr -> Int -> RM ()
markFlowEventEnd addr vers = do
  flowIDMap <- gets flowIDMap
  case Map.lookup (addr, vers) flowIDMap of
    Just flowID ->
      whenTraceEnabled
        "reduce"
        fileTopValAddr
        (return ())
        $ emitFlowEvent "f" (T.pack $ printf "0x%x" flowID)
    Nothing -> return ()

-- === Debug instant traces ===

debugInstStr :: String -> ValAddr -> RM String -> RM ()
debugInstStr name addr f = debugInst name addr (toJSON <$> f)

debugInst :: String -> ValAddr -> RM Value -> RM ()
debugInst name addr argsGen = do
  debugMode <- asks debugMode
  when debugMode $
    whenTraceEnabled name addr (return ()) $ do
      addrS <- tshow addr
      trID <- getTraceID
      ctiCustomVal <- optValRM (toJSON <$> argsGen)
      debugInstant
        (T.pack name)
        ( toJSON $
            RMInstantTraceArgs
              { ctiTraceID = if debugMode then Just trID else Nothing
              , ctiAddr = addrS
              , ctiCustomVal = ctiCustomVal
              }
        )