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
import Common (
  CommonState,
  Config (..),
  eesObjID,
  eesTrace,
  emptyCommonState,
  emptyConfig,
 )
import Control.Monad (when)
import Control.Monad.Except (MonadError, modifyError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (StateT, evalStateT, execStateT, runStateT)
import Cursor
import Data.ByteString.Builder (
  Builder,
  string7,
 )
import Data.List.Split (splitOn)
import qualified Data.Set as Set
import EvalExpr (evalExpr, evalSourceFile)
import Exception (throwErrSt)
import Parser (parseExpr, parseSourceFile)
import Path (TASeg (RootTASeg))
import Reduce (postValidation, reduce)
import Reduce.RMonad
import System.IO (hPutStr, stderr)
import Text.Printf (printf)
import Util (emptyTrace)
import Value
import Value.Util.TreeRep (treeToFullRepString)

data EvalConfig = EvalConfig
  { ecDebugLogging :: Bool
  , ecTraceExec :: Bool
  , ecTracePrintTree :: Bool
  , ecTraceFilter :: String
  , ecShowMutArgs :: Bool
  , ecMaxTreeDepth :: Int
  , ecFilePath :: String
  }

emptyEvalConfig :: EvalConfig
emptyEvalConfig =
  EvalConfig
    { ecDebugLogging = False
    , ecTraceExec = False
    , ecTracePrintTree = False
    , ecTraceFilter = ""
    , ecShowMutArgs = False
    , ecMaxTreeDepth = 0
    , ecFilePath = ""
    }

runIO :: (MonadIO m, MonadError String m) => String -> EvalConfig -> m Builder
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

runTreeIO :: (MonadIO m, MonadError String m) => String -> m Tree
runTreeIO s = runTreeStr s emptyEvalConfig

runStr :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m (Either String AST.Expression)
runStr s conf = do
  t <- runTreeStr s conf
  case treeNode t of
    -- print the error message to the console.
    TNBottom (Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ -> Right <$> evalStateT (runReaderT (buildASTExpr t) emptyConfig) emptyTrace

strToCUEVal :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m Tree
strToCUEVal s conf = do
  e <- parseExpr s
  evalToTree (evalExpr e) conf

runTreeStr :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m Tree
runTreeStr s conf = parseSourceFile (ecFilePath conf) s >>= flip evalFile conf

evalFile :: (MonadError String m, MonadIO m) => SourceFile -> EvalConfig -> m Tree
evalFile sf = evalToTree (evalSourceFile sf)

evalToTree ::
  (MonadError String m, MonadIO m) => StateT CommonState (ReaderT ReduceConfig m) Tree -> EvalConfig -> m Tree
evalToTree f conf = do
  let config =
        Config
          { stDebugLogging = ecDebugLogging conf
          , stTraceExec = ecTraceExec conf
          , stTracePrintTree = ecTracePrintTree conf
          , stTraceFilter =
              let s = ecTraceFilter conf
               in if null s then Set.empty else Set.fromList $ splitOn "," s
          , stShowMutArgs = ecShowMutArgs conf
          , stMaxTreeDepth = ecMaxTreeDepth conf
          }

  reduced <-
    runReaderT
      ( do
          (root, eeState) <- runStateT f emptyCommonState
          when (ecDebugLogging conf) $
            liftIO $
              hPutStr stderr $
                "Initial eval result: " ++ treeToFullRepString root ++ "\n"
          let
            rootTC = TrCur root [(RootTASeg, mkNewTree TNTop)]
            cv = mkRTState rootTC (eesObjID eeState) (eesTrace eeState)
          execStateT (modifyError show reduce) cv
      )
      (ReduceConfig config (emptyReduceParams{createCnstr = True}))

  finalized <-
    runReaderT
      (execStateT (modifyError show postValidation) reduced)
      (ReduceConfig config emptyReduceParams)

  let finalTC = getTreeCursor finalized
  when (ecDebugLogging conf) $
    liftIO $
      hPutStr stderr $
        "Final eval result: " ++ treeToFullRepString (tcFocus finalTC) ++ "\n"
  return $ tcFocus finalTC
