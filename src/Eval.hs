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

import Control.Monad (when)
import Control.Monad.Except (ExceptT, liftEither, mapExceptT, runExcept)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.RWS.Strict (MonadState (get), runRWST)
import Control.Monad.Reader (MonadReader (..))
import Cursor
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
import Env (stMaxTreeDepth, stTraceEnable, stTraceExtraInfo, stTraceFilter, stTracePrintTree)
import qualified Env
import Feature (rootFeature)
import Reduce (finalize, reduce)
import Reduce.Monad
import Semant.Resolver (ResolveState (..), initResolveState, resolve)
import Semant.Semant (TM, TransState (..), emptyTransState, transExpr, transSourceFile)
import StringIndex (TextIndexer, emptyTextIndexer)
import Syntax.AST
import Syntax.Parser (parseExpr, parseSourceFile)
import Syntax.Scanner (scanTokens, scanTokensFromFile)
import System.IO (Handle, hPutStr, stderr, stdout)
import Text.Printf (printf)
import Value
import Value.Export.Debug (treeToFullRepString)
import Value.Export.JSON (buildJSON)

data Config = Config
  { outputFormat :: String
  , ecDebugMode :: Bool
  , ecTraceExec :: Bool
  , ecTracePrintTree :: Bool
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
    , ecTracePrintTree = False
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
  case valNode t of
    -- print the error message to the console.
    VNBottom (Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ ->
      let e = runExcept $ buildExpr t cs
       in case e of
            Left err -> return $ Left err
            Right (expr, _) -> return $ Right expr

evalStrToJSON :: B.ByteString -> Config -> ExceptT String IO (Either String Value)
evalStrToJSON s conf = do
  (t, cs) <- evalStrToVal s conf
  case valNode t of
    -- print the error message to the console.
    VNBottom (Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ ->
      let e = runExcept $ buildJSON t cs
       in case e of
            Left err -> return $ Left err
            Right (expr, _) -> return $ Right expr

strToCUEVal :: B.ByteString -> Config -> ExceptT String IO (Val, TextIndexer)
strToCUEVal s conf = do
  tokens <-
    liftEither
      ( case scanTokens s of
          Left errTk -> Left (show errTk)
          Right ts -> Right ts
      )
  e <- liftEither $ do
    parseExpr tokens
  mapErrToString $ evalVal (transExpr e) conf

evalStrToVal :: B.ByteString -> Config -> ExceptT String IO (Val, TextIndexer)
evalStrToVal s conf = do
  tokens <-
    liftEither
      ( case scanTokensFromFile (ecFilePath conf) s of
          Left errTk -> Left (show errTk)
          Right ts -> Right ts
      )
  liftEither (parseSourceFile tokens) >>= flip evalFile conf

mapErrToString :: ExceptT Error IO a -> ExceptT String IO a
mapErrToString =
  mapExceptT
    ( \x -> do
        e <- x
        return $ case e of
          Left err -> Left $ show err
          Right v -> Right v
    )

mapStringToErr :: (Monad m) => ExceptT String m a -> ExceptT Error m a
mapStringToErr =
  mapExceptT
    ( \x -> do
        e <- x
        return $ case e of
          Left err -> Left $ FatalErr err
          Right v -> Right v
    )

evalFile :: SourceFile -> Config -> ExceptT String IO (Val, TextIndexer)
evalFile sf conf = mapErrToString $ evalVal (transSourceFile sf) conf

evalVal :: TM Val -> Config -> ExceptT Error IO (Val, TextIndexer)
evalVal f conf =
  do
    (raw, transState, _) <- mapStringToErr (runRWST f () (emptyTransState emptyTextIndexer))
    (rootVC, resolverState, _) <-
      mapStringToErr (runRWST (resolve (VCur raw [(rootFeature, mkNewVal VNTop)])) () (initResolveState transState.tIndexer))

    let config =
          Env.Config
            { stTraceEnable = ecTraceExec conf
            , stTracePrintTree = ecTracePrintTree conf
            , stTraceExtraInfo = ecTraceExtraInfo conf
            , stTraceFilter =
                let s = ecTraceFilter conf
                 in if null s then Set.empty else Set.fromList $ splitOn "," s
            , stMaxTreeDepth = ecMaxTreeDepth conf
            }
    (_, finalized, _) <-
      runRWST
        ( do
            when (ecDebugMode conf) $ do
              rawRep <- treeToFullRepString raw
              liftIO $ hPutStr stderr $ "Parsed result: " ++ rawRep ++ "\n"
              resolvedRep <- treeToFullRepString rootVC.focus
              liftIO $ hPutStr stderr $ "Resolved result: " ++ resolvedRep ++ "\n"

            putTMCursor rootVC
            local (mapParams (\p -> p{createCnstr = True})) reduce
            local (mapParams (\p -> p{createCnstr = False})) finalize

            finalized <- get
            let finalTC = finalized.rtsTC
            when (ecDebugMode conf) $ do
              rep <- treeToFullRepString (focus finalTC)
              liftIO $
                hPutStr stderr $
                  "Final eval result: " ++ rep ++ "\n"
        )
        (ReduceConfig config (emptyReduceParams{createCnstr = True}))
        ( RTCState
            (VCur (mkNewVal VNTop) [])
            (emptyContext (LB.hPut conf.ecTraceHandle)){Reduce.Monad.tIndexer = resolverState.tIndexer}
        )

    return
      ( finalized.rtsTC.focus
      , finalized.rtsCtx.tIndexer
      )