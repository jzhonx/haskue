{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Eval (
  EvalConfig (..),
  runIO,
  runTreeIO,
  eval,
)
where

import AST
import Class
import Config
import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (MonadLogger, runNoLoggingT, runStderrLoggingT)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (evalStateT, execStateT)
import EvalExpr
import Parser (parseCUE)
import Path
import Reduction
import Text.Printf (printf)
import Util
import Value.Tree

data EvalConfig = EvalConfig
  { ecDebugLogging :: Bool
  , ecMermaidGraph :: Bool
  , ecFilePath :: String
  }

runIO :: (MonadIO m, MonadError String m) => String -> EvalConfig -> m AST.Expression
runIO s conf =
  if ecDebugLogging conf
    then runStderrLoggingT res
    else runNoLoggingT res
 where
  res :: (MonadError String m, MonadLogger m) => m AST.Expression
  res = runStr s (ecMermaidGraph conf)

runTreeIO :: (MonadIO m, MonadError String m) => String -> m Tree
runTreeIO s = runNoLoggingT $ runTreeStr s False

runStr :: (MonadError String m, MonadLogger m) => String -> Bool -> m AST.Expression
runStr s mermaid = do
  t <- runTreeStr s mermaid
  runReaderT (buildASTExpr False t) emptyConfig

runTreeStr :: (MonadError String m, MonadLogger m) => String -> Bool -> m Tree
runTreeStr s conf = parseCUE s >>= flip eval conf

eval :: (MonadError String m, MonadLogger m) => Expression -> Bool -> m Tree
eval expr mermaid = do
  rootTC <-
    runReaderT
      ( do
          root <- evalStateT (evalExpr expr) emptyContext
          logDebugStr $ printf "---- string evaluated to tree: ----\n%s" (show root)
          let
            rootTC = ValCursor root [(RootSelector, mkNewTree TNTop)]
            cv = cvFromCur rootTC
          logDebugStr $ printf "---- start reduce tree ----"
          res <- execStateT reduce cv
          logDebugStr $ printf "---- reduced: ----\n%s" (show . getCVCursor $ res)
          return res
      )
      Config{cfCreateCnstr = True, cfMermaid = mermaid, cfEvalExpr = evalExpr}

  finalized <-
    runReaderT
      (execStateT validateCnstrs rootTC)
      Config{cfCreateCnstr = False, cfMermaid = mermaid, cfEvalExpr = evalExpr}
  logDebugStr $ printf "---- constraints evaluated: ----\n%s" (show . getCVCursor $ finalized)
  return $ cvVal finalized
