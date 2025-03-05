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
  emptyEvalConfig,
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
import Data.ByteString.Builder (
  Builder,
  string7,
 )
import EvalExpr
import Exception
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
  , ecShowMutArgs :: Bool
  , ecFileTreeAddr :: String
  }

emptyEvalConfig :: EvalConfig
emptyEvalConfig =
  EvalConfig
    { ecDebugLogging = False
    , ecMermaidGraph = False
    , ecShowMutArgs = False
    , ecFileTreeAddr = ""
    }

runIO :: (MonadIO m, MonadError String m) => String -> EvalConfig -> m Builder
runIO s conf =
  if ecDebugLogging conf
    then runStderrLoggingT res
    else runNoLoggingT res
 where
  res :: (MonadError String m, MonadLogger m) => m Builder
  res = do
    r <- runStr s conf
    case r of
      Left err -> return $ string7 err
      Right
        ( AST.ExprUnaryExpr
            (AST.UnaryExprPrimaryExpr (AST.PrimExprOperand (AST.OpLiteral (AST.StructLit decls))))
          ) ->
          return (declsBld 0 decls)
      _ -> throwErrSt "Expected a struct literal"

runTreeIO :: (MonadIO m, MonadError String m) => String -> m Tree
runTreeIO s = runNoLoggingT $ runTreeStr s emptyEvalConfig

runStr :: (MonadError String m, MonadLogger m) => String -> EvalConfig -> m (Either String AST.Expression)
runStr s conf = do
  t <- runTreeStr s conf
  case treeNode t of
    -- print the error message to the console.
    TNBottom (Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ -> Right <$> runReaderT (buildASTExpr False t) emptyConfig

runTreeStr :: (MonadError String m, MonadLogger m) => String -> EvalConfig -> m Tree
runTreeStr s conf = parseSourceFile s >>= flip evalFile conf

defaultConfig :: Config Tree
defaultConfig =
  Config
    { cfSettings =
        Settings
          { stMermaid = False
          , stShowMutArgs = False
          }
    , cfRuntimeParams = RuntimeParams{rpCreateCnstr = False}
    , cfFunctions =
        Functions
          { fnEvalExpr = evalExpr
          , fnClose = close
          , fnReduce = reduce
          , fnDeref = deref
          , fnIndex = index
          , fnPropUpStructPost = propUpStructPost
          }
    }

evalFile :: (MonadError String m, MonadLogger m) => SourceFile -> EvalConfig -> m Tree
evalFile sf conf = do
  let evalConf =
        defaultConfig
          { cfSettings =
              (cfSettings defaultConfig)
                { stMermaid = ecMermaidGraph conf
                , stShowMutArgs = ecShowMutArgs conf
                }
          , cfRuntimeParams =
              (cfRuntimeParams defaultConfig)
                { rpCreateCnstr = True
                }
          }
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
      evalConf

  finalized <-
    runReaderT
      (execStateT postValidation rootTC)
      evalConf{cfRuntimeParams = (cfRuntimeParams evalConf){rpCreateCnstr = False}}
  logDebugStr $ printf "---- constraints evaluated: ----\n%s" (show . getCVCursor $ finalized)
  return $ cvVal finalized
