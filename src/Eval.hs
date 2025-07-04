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
  emptyRunner,
  Runner (..),
)
where

import AST
import qualified Common
import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (MonadIO)
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
import qualified Reduce
import Reduce.PostReduce (postValidation)
import Reduce.RMonad
import Text.Printf (printf)
import Util (emptyTrace)
import Value

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

-- | Runner holds the configuration and functions for evaluation.
data Runner = Runner
  { rcConfig :: Common.Config
  }

instance Show Runner where
  show r = printf "{rcConfig = %s}" (show $ rcConfig r)

emptyRunner :: Runner
emptyRunner =
  Runner
    { rcConfig = Common.emptyConfig
    }

updateConfig :: Runner -> Common.Config -> Runner
updateConfig r c = r{rcConfig = c}

instance Common.HasConfig Runner where
  getConfig = rcConfig
  setConfig r c = r{rcConfig = c}

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
        return (declsBld 0 decls)
    _ -> throwErrSt "Expected a struct literal"

runTreeIO :: (MonadIO m, MonadError String m) => String -> m Tree
runTreeIO s = runTreeStr s emptyEvalConfig

runStr :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m (Either String AST.Expression)
runStr s conf = do
  t <- runTreeStr s conf
  case treeNode t of
    -- print the error message to the console.
    TNBottom (Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ -> Right <$> evalStateT (runReaderT (buildASTExpr t) emptyRunner) emptyTrace

strToCUEVal :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m Tree
strToCUEVal s conf = do
  e <- parseExpr s
  evalToTree (evalExpr e) conf

runTreeStr :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m Tree
runTreeStr s conf = parseSourceFile (ecFilePath conf) s >>= flip evalFile conf

evalFile :: (MonadError String m, MonadIO m) => SourceFile -> EvalConfig -> m Tree
evalFile sf = evalToTree (evalSourceFile sf)

evalToTree ::
  (MonadError String m, MonadIO m) => StateT Common.EEState (ReaderT Runner m) Tree -> EvalConfig -> m Tree
evalToTree f conf = do
  let runner =
        updateConfig
          emptyRunner
          ( Common.Config
              { Common.cfSettings =
                  (Common.cfSettings . rcConfig $ emptyRunner)
                    { Common.stDebugLogging = ecDebugLogging conf
                    , Common.stTraceExec = ecTraceExec conf
                    , Common.stTracePrintTree = ecTracePrintTree conf
                    , Common.stTraceFilter =
                        let s = ecTraceFilter conf
                         in if null s then Set.empty else Set.fromList $ splitOn "," s
                    , Common.stShowMutArgs = ecShowMutArgs conf
                    , Common.stMaxTreeDepth = ecMaxTreeDepth conf
                    }
              , Common.cfRuntimeParams =
                  (Common.cfRuntimeParams . rcConfig $ emptyRunner)
                    { Common.rpCreateCnstr = True
                    }
              }
          )
  reduced <-
    runReaderT
      ( do
          (root, eeState) <- runStateT f Common.emptyEEState

          let
            rootTC = TrCur root [(RootTASeg, mkNewTree TNTop)]
            cv = mkRTState rootTC (Common.eesObjID eeState) (Common.eesTrace eeState)
          execStateT Reduce.fullReduce cv
      )
      runner

  finalized <-
    runReaderT
      (execStateT postValidation reduced)
      ( updateConfig
          runner
          ( let c = rcConfig runner
             in c{Common.cfRuntimeParams = (Common.cfRuntimeParams c){Common.rpCreateCnstr = False}}
          )
      )
  let finalTC = getTreeCursor finalized
  return $ tcFocus finalTC
