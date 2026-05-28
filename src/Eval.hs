{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Eval (
  Config (..),
  evalStr,
  evalFile,
  emptyConfig,
  strToCUEVal,
)
where

import Control.Monad (void, when)
import Control.Monad.Except (ExceptT, liftEither, mapExceptT, runExcept)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.RWS.Strict (runRWST)
import Control.Monad.Reader (MonadReader (..))
import Data.Aeson (Value)
import Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.ByteString as B
import Data.ByteString.Builder (
  Builder,
  byteString,
  lazyByteString,
  string7,
 )
import qualified Data.ByteString.Lazy as LB
import Data.List.Split (splitOn)
import qualified Data.Set as Set
import qualified Data.Yaml as Yaml
import Env (stMaxTreeDepth, stTraceEnable, stTraceExtraInfo, stTraceFilter)
import qualified Env
import Feature (fileTopValAddr)
import Reduce (finalize, reduce)
import Reduce.Core (storeBuiltinsAndPackages)
import Reduce.Monad
import Reduce.Recalc (recalc)
import Reduce.Store (fetchValMust)
import Semant.Semant (TM, TransErr (..), TransState (..), mkTransState, transExprToVal, transSourceFile)
import StringIndex (TextIndexer, emptyTextIndexer)
import Syntax.AST
import Syntax.Parser (parseExpr, parseSourceFile)
import Syntax.Scanner (scanTokens, scanTokensFromFile)
import System.IO (Handle, hPutStr, stderr, stdout)
import Text.Printf (printf)
import Value
import Value.Export.Debug (vnToFullStringTermsRep)
import Value.Export.JSON (buildJSON)

data Config = Config
  { outputFormat :: String
  , ecDebugMode :: Bool
  , ecTraceExec :: Bool
  , ecTraceExtraInfo :: Bool
  , ecTraceFilter :: String
  , ecTraceHandle :: Handle
  , ecMaxTreeDepth :: Int
  , ecFilePath :: String
  }

emptyConfig :: Config
emptyConfig =
  Config
    { outputFormat = ""
    , ecDebugMode = False
    , ecTraceExec = False
    , ecTraceExtraInfo = False
    , ecTraceFilter = ""
    , ecTraceHandle = stdout
    , ecMaxTreeDepth = 0
    , ecFilePath = ""
    }

evalStr :: B.ByteString -> Config -> ExceptT String IO Builder
evalStr eStr conf
  | conf.outputFormat == "json" = do
      r <- evalStrToJSON eStr conf
      case r of
        Left err -> return $ string7 err
        Right val -> do
          let bs = encodePretty val
          return $ lazyByteString bs
  | conf.outputFormat == "yaml" = do
      r <- evalStrToJSON eStr conf
      case r of
        Left err -> return $ string7 err
        Right val -> do
          let bs = Yaml.encode val
          return $ byteString bs
  | otherwise = do
      r <- evalStrToAST eStr conf
      case r of
        Left err -> return $ string7 err
        -- For the declaration result, we don't want to print the curly braces.
        Right (Unary (Primary (PrimExprOperand (OpLiteral (LitStruct (StructLit _ decls _)))))) ->
          return (declsToBuilder decls)
        Right e -> return $ exprToBuilder False e

evalStrToAST :: B.ByteString -> Config -> ExceptT String IO (Either String Expression)
evalStrToAST s conf = do
  (t, cs) <- evalStrToVal s conf
  case value t of
    -- print the error message to the console.
    VBottom (Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ ->
      let e = runExcept $ buildExpr t cs
       in case e of
            Left err -> return $ Left err
            Right (expr, _) -> return $ Right expr

evalStrToJSON :: B.ByteString -> Config -> ExceptT String IO (Either String Value)
evalStrToJSON s conf = do
  (t, cs) <- evalStrToVal s conf
  case value t of
    -- print the error message to the console.
    VBottom (Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ ->
      let e = runExcept $ buildJSON t cs
       in case e of
            Left err -> return $ Left err
            Right (expr, _) -> return $ Right expr

strToCUEVal :: B.ByteString -> Config -> ExceptT String IO (VNode, TextIndexer)
strToCUEVal s conf = do
  tokens <-
    liftEither
      ( case scanTokens s of
          Left errTk -> Left (show errTk)
          Right ts -> Right ts
      )
  -- -- Print the tokens for debugging.
  -- do
  --   let tokenReps = map show tokens
  --   liftIO $ hPutStr stderr $ "Tokens: " ++ show tokenReps ++ "\n"
  e <- liftEither $ parseExpr tokens
  evalVal (transExprToVal e fileTopValAddr) conf

evalStrToVal :: B.ByteString -> Config -> ExceptT String IO (VNode, TextIndexer)
evalStrToVal s conf = do
  tokens <-
    liftEither
      ( case scanTokensFromFile (ecFilePath conf) s of
          Left errTk -> Left (show errTk)
          Right ts -> Right ts
      )
  -- do
  --   let tokenReps = map show tokens
  --   liftIO $ hPutStr stderr $ "Tokens: " ++ show tokenReps ++ "\n"
  e <- liftEither (parseSourceFile tokens)
  evalFile e conf

evalFile :: SourceFile -> Config -> ExceptT String IO (VNode, TextIndexer)
evalFile sf conf = evalVal (transSourceFile sf fileTopValAddr) conf

evalVal :: TM VNode -> Config -> ExceptT String IO (VNode, TextIndexer)
evalVal f conf = do
  let
    initTransState = mkTransState emptyTextIndexer
    transRes = runRWST f () initTransState
  (raw, tIndexer, isValid) <-
    mapExceptT
      ( \m -> do
          r <- m
          case r of
            Left (SemantErr msg) -> return $ Right (mkBottomVN msg, emptyTextIndexer, False)
            Left (FatalErr msg) -> return $ Left msg
            Right (val, s, _) -> return $ Right (val, s.tIndexer, True)
      )
      transRes
  if isValid
    then evalValInner conf tIndexer raw
    else return (raw, tIndexer)

evalValInner :: Config -> TextIndexer -> VNode -> ExceptT String IO (VNode, TextIndexer)
evalValInner conf textIndexer raw = do
  let config =
        Env.Config
          { stTraceEnable = ecTraceExec conf
          , stTraceExtraInfo = ecTraceExtraInfo conf
          , stTraceFilter =
              let s = ecTraceFilter conf
               in if null s then Set.empty else Set.fromList $ splitOn "," s
          , stMaxTreeDepth = ecMaxTreeDepth conf
          }

  (reducedRoot, finalized, _) <-
    runRWST
      ( do
          when (ecDebugMode conf) $ do
            rawRep <- vnToFullStringTermsRep raw
            liftIO $ hPutStr stderr $ "Translated result: " ++ rawRep ++ "\n"

          storeBuiltinsAndPackages

          topVal <-
            local
              (mapParams (\p -> p{createCnstr = True}))
              ( do
                  void $ reduce fileTopValAddr raw
                  recalc
                  fetchValMust "eval" fileTopValAddr
              )
          reducedTopVal <- local (mapParams (\p -> p{createCnstr = False})) (finalize fileTopValAddr topVal)

          when (ecDebugMode conf) $ do
            rep <- vnToFullStringTermsRep reducedTopVal
            liftIO $
              hPutStr stderr $
                "Final eval result: " ++ rep ++ "\n"

          return reducedTopVal
      )
      (ReduceConfig{baseConfig = config, params = (emptyReduceParams{createCnstr = True})})
      (emptyContext (LB.hPut conf.ecTraceHandle))
        { Reduce.Monad.tIndexer = textIndexer
        }

  return
    ( reducedRoot
    , finalized.tIndexer
    )
