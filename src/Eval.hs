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
import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (MonadLogger, runNoLoggingT, runStderrLoggingT)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (evalStateT, execStateT)
import EvalExpr
import EvalVal
import Parser (parseCUE)
import Path
import Text.Printf (printf)
import Value.Tree
import Util

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
  runReaderT (buildASTExpr False t) Config{}

runTreeStr :: (MonadError String m, MonadLogger m) => String -> Bool -> m Tree
runTreeStr s conf = parseCUE s >>= flip eval conf

eval :: (MonadError String m, MonadLogger m) => Expression -> Bool -> m Tree
eval expr mermaid = do
  rootTC <-
    runReaderT
      ( do
          root <- evalStateT (evalExpr expr) emptyContext
          logDebugStr $ printf "---- evaluated to rootTC: ----\n%s" (show root)
          let
            rootTC = ValCursor root [(RootSelector, mkNewTree TNTop)]
            cv = cvFromCur rootTC
          r2 <- execStateT setOrigNodes cv
          logDebugStr $ printf "---- start resolving links ----"
          res <- execStateT evalTM r2
          logDebugStr $ printf "---- resolved: ----\n%s" (show . getCVCursor $ res)
          return res
      )
      Config{cfCreateCnstr = True, cfMermaid = mermaid}

  finalized <-
    runReaderT
      (execStateT validateCnstrs rootTC)
      Config{cfCreateCnstr = False, cfMermaid = mermaid}
  logDebugStr $ printf "---- constraints evaluated: ----\n%s" (show . getCVCursor $ finalized)
  return $ cvVal finalized
