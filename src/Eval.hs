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

import AST (
  Expression (ExprUnaryExpr),
  Literal (LitStructLit),
  Operand (OpLiteral),
  PrimaryExpr (PrimExprOperand),
  SourceFile,
  StructLit (StructLit),
  UnaryExpr (UnaryExprPrimaryExpr),
  declsBld,
 )
import qualified Common
import Control.Monad.Except (MonadError)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Logger (MonadLogger, runNoLoggingT, runStderrLoggingT)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (evalStateT, execStateT)
import Cursor (
  CtxVal (cvVal),
  ValCursor (ValCursor),
  cvFromCur,
  getCVCursor,
 )
import Data.ByteString.Builder (
  Builder,
  string7,
 )
import EvalExpr (evalExpr, evalSourceFile)
import Exception (throwErrSt)
import qualified MutEnv
import Parser (parseSourceFile)
import Path (TASeg (RootTASeg))
import Reduce (
  close,
  comprehend,
  fullReduce,
  index,
  propUpStructPost,
  reduce,
 )
import Reduce.PostReduce (postValidation)
import Reduce.UnifyOp (unifyEmbeds)
import Text.Printf (printf)
import Util (logDebugStr)
import Value.Tree (
  Bottom (Bottom),
  Tree (treeNode),
  TreeNode (TNBottom, TNTop),
  mkNewTree,
 )

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

data Runner = Runner
  { rcConfig :: Common.Config
  , rcFuncs :: MutEnv.Functions Tree
  }

instance Show Runner where
  show r = printf "{rcConfig = %s}" (show $ rcConfig r)

emptyRunner :: Runner
emptyRunner =
  Runner
    { rcConfig = Common.emptyConfig
    , rcFuncs =
        MutEnv.Functions
          { MutEnv.fnEvalExpr = evalExpr
          , MutEnv.fnClose = close
          , MutEnv.fnReduce = reduce
          , MutEnv.fnIndex = index
          , MutEnv.fnPropUpStructPost = propUpStructPost
          , MutEnv.fnComprehend = comprehend
          , MutEnv.fnUnifyEmbeds = unifyEmbeds
          }
    }

updateConfig :: Runner -> Common.Config -> Runner
updateConfig r c = r{rcConfig = c}

instance MutEnv.HasFuncs Runner Tree where
  getFuncs = rcFuncs
  setFuncs r f = r{rcFuncs = f}

instance Common.HasConfig Runner where
  getConfig = rcConfig
  setConfig r c = r{rcConfig = c}

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
            (AST.UnaryExprPrimaryExpr (AST.PrimExprOperand (AST.OpLiteral (AST.LitStructLit (AST.StructLit decls)))))
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
    _ -> Right <$> runReaderT (Common.buildASTExpr False t) emptyRunner

runTreeStr :: (MonadError String m, MonadLogger m) => String -> EvalConfig -> m Tree
runTreeStr s conf = parseSourceFile s >>= flip evalFile conf

evalFile :: (MonadError String m, MonadLogger m) => SourceFile -> EvalConfig -> m Tree
evalFile sf conf = do
  let runner =
        updateConfig
          emptyRunner
          ( Common.Config
              { Common.cfSettings =
                  (Common.cfSettings . rcConfig $ emptyRunner)
                    { Common.stMermaid = ecMermaidGraph conf
                    , Common.stShowMutArgs = ecShowMutArgs conf
                    }
              , Common.cfRuntimeParams =
                  (Common.cfRuntimeParams . rcConfig $ emptyRunner)
                    { Common.rpCreateCnstr = True
                    }
              }
          )
  logDebugStr $ printf "runner: %s" (show runner)
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
      runner

  finalized <-
    runReaderT
      (execStateT postValidation rootTC)
      ( updateConfig
          runner
          ( let c = rcConfig runner
             in c{Common.cfRuntimeParams = (Common.cfRuntimeParams c){Common.rpCreateCnstr = False}}
          )
      )
  logDebugStr $ printf "---- constraints evaluated: ----\n%s" (show . getCVCursor $ finalized)
  return $ cvVal finalized
