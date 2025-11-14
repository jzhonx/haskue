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
import Control.Monad.Except (ExceptT, liftEither, mapExceptT)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.RWS.Strict (RWST, runRWST)
import Control.Monad.Reader (MonadReader (..), ReaderT (runReaderT))
import Control.Monad.State.Strict (evalStateT)
import Cursor
import Data.ByteString.Builder (
  Builder,
  string7,
 )
import Data.List.Split (splitOn)
import qualified Data.Set as Set
import Env (
  CommonState (..),
  Config (..),
  eesObjID,
  eesTrace,
  emptyConfig,
 )
import EvalExpr (evalExpr, evalSourceFile)
import Exception (throwErrSt)
import Feature (rootFeature)
import Parser (parseExpr, parseSourceFile)
import Reduce (postValidation, reduce)
import Reduce.RMonad
import System.IO (hPutStr, stderr)
import Text.Printf (printf)
import Value
import Value.Util.TreeRep (treeToFullRepString)

data EvalConfig = EvalConfig
  { ecDebugMode :: Bool
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
    { ecDebugMode = False
    , ecTraceExec = False
    , ecTracePrintTree = False
    , ecTraceExtraInfo = False
    , ecTraceFilter = ""
    , ecShowMutArgs = False
    , ecMaxTreeDepth = 0
    , ecFilePath = ""
    }

runIO :: String -> EvalConfig -> ExceptT String IO Builder
runIO eStr conf = do
  r <- runStr eStr conf
  case r of
    Left err -> return $ string7 err
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
    _ -> throwErrSt "Expected a struct literal"

runTreeIO :: String -> ExceptT String IO Tree
runTreeIO s = fst <$> runTreeStr s emptyEvalConfig

runStr :: String -> EvalConfig -> ExceptT String IO (Either String AST.Expression)
runStr s conf = do
  (t, cs) <- runTreeStr s conf
  case treeNode t of
    -- print the error message to the console.
    TNBottom (Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ -> Right <$> evalStateT (runReaderT (buildASTExpr t) emptyConfig) cs

strToCUEVal :: String -> EvalConfig -> ExceptT String IO (Tree, CommonState)
strToCUEVal s conf = do
  e <- liftEither $ parseExpr s
  mapErrToString $ evalToTree (evalExpr e) conf

runTreeStr :: String -> EvalConfig -> ExceptT String IO (Tree, CommonState)
runTreeStr s conf = liftEither (parseSourceFile (ecFilePath conf) s) >>= flip evalFile conf

mapErrToString :: ExceptT Error IO a -> ExceptT String IO a
mapErrToString =
  mapExceptT
    ( \x -> do
        e <- x
        return $ case e of
          Left err -> Left $ show err
          Right v -> Right v
    )

evalFile :: SourceFile -> EvalConfig -> ExceptT String IO (Tree, CommonState)
evalFile sf conf = mapErrToString $ evalToTree (evalSourceFile sf) conf

evalToTree ::
  RWST ReduceConfig () RTCState (ExceptT Error IO) Tree ->
  EvalConfig ->
  ExceptT Error IO (Tree, CommonState)
evalToTree f conf =
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
            when (ecDebugMode conf) $
              liftIO $
                hPutStr stderr $
                  "Initial eval result: " ++ treeToFullRepString root ++ "\n"
            let
              rootTC = TrCur root [(rootFeature, mkNewTree TNTop)]
            putTMCursor rootTC
            local (mapParams (\p -> p{createCnstr = True})) reduce
            local (mapParams (\p -> p{createCnstr = False})) postValidation
        )
        (ReduceConfig config (emptyReduceParams{createCnstr = True}))
        (RTCState (TrCur (mkNewTree TNTop) []) emptyContext)

    let finalTC = finalized.rtsTC
    when (ecDebugMode conf) $
      liftIO $
        hPutStr stderr $
          "Final eval result: " ++ treeToFullRepString (tcFocus finalTC) ++ "\n"
    return
      ( tcFocus finalTC
      , CommonState
          { eesObjID = finalized.rtsCtx.ctxObjID
          , eesTrace = finalized.rtsCtx.ctxTrace
          , tIndexer = finalized.rtsCtx.tIndexer
          }
      )