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
import DepGraph (DepGroupDesc, addrIsVertex, lookupDepGroup)
import EvalAddr
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

traceSpanNoPreRM :: (ToJSONWTIndexer a) => String -> EvalAddr -> RM a -> RM a
traceSpanNoPreRM name addr = traceSpanRM name addr emptyTracePreDataRM

emptyTracePreDataRM :: RM TracePreData
emptyTracePreDataRM = return emptyTracePreData

traceSpanRM :: (ToJSONWTIndexer a) => String -> EvalAddr -> RM TracePreData -> RM a -> RM a
traceSpanRM name addr preData = traceSpanWithRM name addr preData ttoJSON

traceSpanTermTreeTM ::
  (ToJSONWTIndexer a, ToTermTree a, ToJSONWTIndexer b, ToTermTree b) => String -> EvalAddr -> a -> RM b -> RM b
traceSpanTermTreeTM name addr a =
  traceSpanWithRM
    name
    addr
    ( do
        debugMode <- asks debugMode
        if debugMode
          then do
            treeJSON <- toTermTreeJSONForAddr addr a
            return $ mkTracePreDataWithOnlyVal treeJSON
          else do
            v <- ttoJSON a
            return $ mkTracePreDataWithOnlyVal v
    )
    ( \b -> do
        debugMode <- asks debugMode
        if debugMode
          then toTermTreeJSONForAddr addr b
          else ttoJSON b
    )

traceSpanTermTreeAnyTM ::
  (ToJSONWTIndexer a, ToTermTree a, ToJSONWTIndexer b) => String -> EvalAddr -> a -> RM b -> RM b
traceSpanTermTreeAnyTM name addr a =
  traceSpanWithRM
    name
    addr
    ( do
        debugMode <- asks debugMode
        if debugMode
          then do
            treeJSON <- toTermTreeJSONForAddr addr a
            return $ mkTracePreDataWithOnlyVal treeJSON
          else do
            v <- ttoJSON a
            return $ mkTracePreDataWithOnlyVal v
    )
    ttoJSON

traceSpanWithRM :: String -> EvalAddr -> RM TracePreData -> (b -> RM Value) -> RM b -> RM b
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

{- | Run the traced action only when tracing is enabled for the named operation;
otherwise run the fallback action. Keep trace-only work inside the @traced@
action so it is not performed when tracing is disabled.
-}
whenTraceEnabled :: String -> EvalAddr -> RM a -> RM a -> RM a
whenTraceEnabled name _addr f traced = do
  TraceConfig{stTraceEnable = traceEnable} <- asks traceConfig
  debugMode <- asks debugMode
  -- If debugMode is not enabled, we only trace the "reduce" and "recalc" functions.
  if traceEnable && (debugMode || name == "reduce" || name == "recalc")
    then traced
    else f

{- | Generate a value only when trace value rendering is enabled. The supplied
action may be expensive and is deliberately not run when values are hidden.
-}
optValRM :: RM Value -> RM Value
optValRM f = do
  disableShowVal <- asks (stTraceDisableShowValue . traceConfig)
  if not disableShowVal then f else return $ object []

markFlowEventStart :: EvalAddr -> Int -> RM ()
markFlowEventStart addr vers = case addrIsVertex addr of
  Just vAddr -> do
    flowIDMap <- gets flowIDMap
    flowIDCounter <- gets flowIDCounter
    let newFlowID = flowIDCounter + 1
    ng <- gets depGraph
    let
      r = lookupDepGroup vAddr ng
    case r of
      Just group -> do
        modify' $ \ctx -> ctx{flowIDMap = Map.insert (group, vers) newFlowID flowIDMap, flowIDCounter = newFlowID}

        whenTraceEnabled "reduce" addr (return ()) $ emitFlowEvent "s" (T.pack $ printf "0x%x" newFlowID)
      Nothing -> return ()
  Nothing -> return ()

markFlowEventEnd :: DepGroupDesc -> Int -> RM ()
markFlowEventEnd group vers = do
  flowIDMap <- gets flowIDMap
  case Map.lookup (group, vers) flowIDMap of
    Just flowID ->
      whenTraceEnabled
        "reduce"
        fileTopEvalAddr
        (return ())
        $ emitFlowEvent "f" (T.pack $ printf "0x%x" flowID)
    Nothing -> return ()

-- === Debug instant traces ===

{- | Emit a string-valued debug instant.

The @RM String@ argument is deliberately a message-generating action. It is
run only when the debug instant is enabled (and trace values are not hidden).
Callers should therefore pass message generation directly to this function,
instead of binding the generated 'String' before calling it. For example:

@
debugInstStr "descend" startAddr $
  debugDescend startAddr matchedAddr start selectors unmatchedSels
@
-}
debugInstStr :: String -> EvalAddr -> RM String -> RM ()
debugInstStr name addr f = debugInst name addr (toJSON <$> f)

{- | Emit a value-producing debug instant. As with 'debugInstStr', @argsGen@ is
conditional: it is run only in debug mode when tracing is enabled for @name@
and trace values are not hidden. Keep any debug-only payload construction in
this action so normal evaluation does not pay its cost or observe its effects.
-}
debugInst :: String -> EvalAddr -> RM Value -> RM ()
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
