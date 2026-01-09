{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Eval (
  EvalConfig (..),
  runIO,
  runTreeIO,
  evalFile,
  emptyEvalConfig,
  strToCUEVal,
)
where

import AST
import Control.Monad (when)
import Control.Monad.Except (ExceptT, liftEither, mapExceptT, runExcept)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.RWS.Strict (MonadState (get), RWST, runRWST)
import Control.Monad.Reader (MonadReader (..))
import Cursor
import Data.Aeson (Value, encode)
import qualified Data.ByteString as B
import Data.ByteString.Builder (
  Builder,
  lazyByteString,
  string7,
 )
import Data.List.Split (splitOn)
import qualified Data.Set as Set
import Env (
  Config (..),
 )
import EvalExpr (evalExpr, evalSourceFile)
import Feature (rootFeature)
import Parser (parseExpr, parseSourceFile)
import Reduce (postValidation, reduce)
import Reduce.RMonad
import StringIndex (TextIndexer)
import System.IO (hPutStr, stderr)
import Text.Printf (printf)
import Value
import Value.Export.Debug (treeToFullRepString)
import Value.Export.JSON (buildJSON)

data EvalConfig = EvalConfig
  { outputFormat :: String
  , ecDebugMode :: Bool
  , ecTraceExec :: Bool
  , ecTracePrintTree :: Bool
  , ecTraceExtraInfo :: Bool
  , ecTraceFilter :: String
  , ecShowMutArgs :: Bool
  , ecMaxTreeDepth :: Int
  , ecFilePath :: String
  }

emptyEvalConfig :: EvalConfig
emptyEvalConfig =
  EvalConfig
    { outputFormat = ""
    , ecDebugMode = False
    , ecTraceExec = False
    , ecTracePrintTree = False
    , ecTraceExtraInfo = False
    , ecTraceFilter = ""
    , ecShowMutArgs = False
    , ecMaxTreeDepth = 0
    , ecFilePath = ""
    }

runIO :: B.ByteString -> EvalConfig -> ExceptT String IO Builder
runIO eStr conf
  | conf.outputFormat == "json" = do
      r <- evalStrToJSON eStr conf
      case r of
        Left err -> return $ string7 err
        Right val -> do
          let bs = encode val
          return $ lazyByteString bs
  | otherwise = do
      r <- evalStrToAST eStr conf
      case r of
        Left err -> return $ string7 err
        -- For the declaration result, we don't want to print the curly braces.
        Right
          ( anVal ->
              AST.ExprUnaryExpr
                ( anVal ->
                    AST.UnaryExprPrimaryExpr
                      ( anVal ->
                          AST.PrimExprOperand
                            ( anVal ->
                                AST.OpLiteral
                                  ( anVal ->
                                      AST.LitStructLit
                                        (anVal -> AST.StructLit decls)
                                    )
                              )
                        )
                  )
            ) ->
            return (declsToBuilder decls)
        Right e -> return $ exprToBuilder False e

runTreeIO :: B.ByteString -> ExceptT String IO Val
runTreeIO s = fst <$> evalStrToVal s emptyEvalConfig

evalStrToAST :: B.ByteString -> EvalConfig -> ExceptT String IO (Either String AST.Expression)
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

evalStrToJSON :: B.ByteString -> EvalConfig -> ExceptT String IO (Either String Value)
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

strToCUEVal :: B.ByteString -> EvalConfig -> ExceptT String IO (Val, TextIndexer)
strToCUEVal s conf = do
  e <- liftEither $ parseExpr s
  mapErrToString $ evalVal (evalExpr e) conf

evalStrToVal :: B.ByteString -> EvalConfig -> ExceptT String IO (Val, TextIndexer)
evalStrToVal s conf = liftEither (parseSourceFile (ecFilePath conf) s) >>= flip evalFile conf

mapErrToString :: ExceptT Error IO a -> ExceptT String IO a
mapErrToString =
  mapExceptT
    ( \x -> do
        e <- x
        return $ case e of
          Left err -> Left $ show err
          Right v -> Right v
    )

evalFile :: SourceFile -> EvalConfig -> ExceptT String IO (Val, TextIndexer)
evalFile sf conf = mapErrToString $ evalVal (evalSourceFile sf) conf

evalVal ::
  RWST ReduceConfig () RTCState (ExceptT Error IO) Val ->
  EvalConfig ->
  ExceptT Error IO (Val, TextIndexer)
evalVal f conf =
  do
    let config =
          Config
            { stTraceEnable = ecTraceExec conf
            , stTracePrintTree = ecTracePrintTree conf
            , stTraceExtraInfo = ecTraceExtraInfo conf
            , stTraceFilter =
                let s = ecTraceFilter conf
                 in if null s then Set.empty else Set.fromList $ splitOn "," s
            , stShowMutArgs = ecShowMutArgs conf
            , stMaxTreeDepth = ecMaxTreeDepth conf
            }
    (_, finalized, _) <-
      runRWST
        ( do
            root <- f
            when (ecDebugMode conf) $ do
              rep <- treeToFullRepString root
              liftIO $
                hPutStr stderr $
                  "Initial eval result: " ++ rep ++ "\n"
            let
              rootVC = VCur root [(rootFeature, mkNewVal VNTop)]
            putTMCursor rootVC
            local (mapParams (\p -> p{createCnstr = True})) reduce
            local (mapParams (\p -> p{createCnstr = False})) postValidation

            finalized <- get
            let finalTC = finalized.rtsTC
            when (ecDebugMode conf) $ do
              rep <- treeToFullRepString (focus finalTC)
              liftIO $
                hPutStr stderr $
                  "Final eval result: " ++ rep ++ "\n"
        )
        (ReduceConfig config (emptyReduceParams{createCnstr = True}))
        (RTCState (VCur (mkNewVal VNTop) []) emptyContext)

    return
      ( finalized.rtsTC.focus
      , finalized.rtsCtx.tIndexer
      )