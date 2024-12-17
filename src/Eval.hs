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
  evalFile,
)
where

import AST
import Class
import Config
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (MonadLogger, runNoLoggingT, runStderrLoggingT)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (evalStateT, execStateT)
import Cursor
import Error
import EvalExpr
import Parser (parseSourceFile)
import Path
import PostReduce
import Reduction
import Ref
import Text.Printf (printf)
import Util
import Value.Tree

data EvalConfig = EvalConfig
  { ecDebugLogging :: Bool
  , ecMermaidGraph :: Bool
  , ecFileTreeAddr :: String
  }

runIO :: (MonadIO m, MonadError String m) => String -> EvalConfig -> m [AST.Declaration]
runIO s conf =
  if ecDebugLogging conf
    then runStderrLoggingT res
    else runNoLoggingT res
 where
  res :: (MonadError String m, MonadLogger m) => m [AST.Declaration]
  res = do
    ast <- runStr s (ecMermaidGraph conf)
    case ast of
      AST.ExprUnaryExpr
        (AST.UnaryExprPrimaryExpr (AST.PrimExprOperand (AST.OpLiteral (AST.StructLit decls)))) -> return decls
      _ -> throwErrSt "Expected a struct literal"

runTreeIO :: (MonadIO m, MonadError String m) => String -> m Tree
runTreeIO s = runNoLoggingT $ runTreeStr s False

runStr :: (MonadError String m, MonadLogger m) => String -> Bool -> m AST.Expression
runStr s mermaid = do
  t <- runTreeStr s mermaid
  case treeNode t of
    -- print the error message to the console.
    TNBottom (Bottom msg) -> throwError $ printf "error: %s" msg
    _ -> runReaderT (buildASTExpr False t) emptyConfig

runTreeStr :: (MonadError String m, MonadLogger m) => String -> Bool -> m Tree
runTreeStr s conf = parseSourceFile s >>= flip evalFile conf

evalConfig :: Config Tree
evalConfig =
  Config
    { cfCreateCnstr = False
    , cfMermaid = False
    , cfEvalExpr = evalExpr
    , cfClose = close
    , cfReduce = reduce
    , cfDeref = deref
    , cfIndex = index
    }

evalFile :: (MonadError String m, MonadLogger m) => SourceFile -> Bool -> m Tree
evalFile sf mermaid = do
  rootTC <-
    runReaderT
      ( do
          root <- evalStateT (evalSourceFile sf) 0
          logDebugStr $ printf "---- file evaluated to tree: ----\n%s" (show root)
          let
            rootTC = ValCursor root [(RootTASeg, mkNewTree TNTop)]
            cv = cvFromCur rootTC
          logDebugStr $ printf "---- start reduce tree ----"
          res <- execStateT fullReduce cv
          logDebugStr $ printf "---- reduced: ----\n%s" (show . getCVCursor $ res)
          return res
      )
      evalConfig
        { cfCreateCnstr = True
        , cfMermaid = mermaid
        }

  finalized <-
    runReaderT
      (execStateT postValidation rootTC)
      evalConfig
        { cfCreateCnstr = False
        , cfMermaid = mermaid
        }
  logDebugStr $ printf "---- constraints evaluated: ----\n%s" (show . getCVCursor $ finalized)
  return $ cvVal finalized
