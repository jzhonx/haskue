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
import qualified Cursor
import Data.ByteString.Builder (
  Builder,
  string7,
 )
import Data.List.Split (splitOn)
import qualified Data.Set as Set
import EvalExpr (evalExpr, evalSourceFile)
import Exception (throwErrSt)
import qualified MutEnv
import Parser (parseExpr, parseSourceFile)
import Path (TASeg (RootTASeg))
import qualified Reduce
import Reduce.PostReduce (postValidation)
import qualified Reduce.RMonad as RM
import Text.Printf (printf)
import Util (emptyTrace)
import qualified Value.Tree as VT

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
  , rcFuncs :: MutEnv.Functions
  }

instance Show Runner where
  show r = printf "{rcConfig = %s}" (show $ rcConfig r)

emptyRunner :: Runner
emptyRunner =
  Runner
    { rcConfig = Common.emptyConfig
    , rcFuncs =
        MutEnv.emptyFunctions
          { MutEnv.fnEvalExpr = evalExpr
          , MutEnv.fnReduce = Reduce.reduce
          , MutEnv.reduceUnifyConj = Reduce.reduceUnifyConj
          }
    }

updateConfig :: Runner -> Common.Config -> Runner
updateConfig r c = r{rcConfig = c}

instance MutEnv.HasFuncs Runner where
  getFuncs = rcFuncs
  setFuncs r f = r{rcFuncs = f}

instance Common.HasConfig Runner where
  getConfig = rcConfig
  setConfig r c = r{rcConfig = c}

runIO :: (MonadIO m, MonadError String m) => String -> EvalConfig -> m Builder
runIO eStr conf = do
  r <- runStr eStr conf
  case r of
    Left err -> return $ string7 err
    Right
      ( wpVal ->
          AST.ExprUnaryExpr
            ( wpVal ->
                AST.UnaryExprPrimaryExpr
                  ( wpVal ->
                      AST.PrimExprOperand
                        ( wpVal ->
                            AST.OpLiteral
                              ( wpVal ->
                                  AST.LitStructLit
                                    (wpVal -> AST.StructLit decls)
                                )
                          )
                    )
              )
        ) ->
        return (declsBld 0 decls)
    _ -> throwErrSt "Expected a struct literal"

runTreeIO :: (MonadIO m, MonadError String m) => String -> m VT.Tree
runTreeIO s = runTreeStr s emptyEvalConfig

runStr :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m (Either String AST.Expression)
runStr s conf = do
  t <- runTreeStr s conf
  case VT.treeNode t of
    -- print the error message to the console.
    VT.TNBottom (VT.Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ -> Right <$> evalStateT (runReaderT (Common.buildASTExpr False t) emptyRunner) emptyTrace

strToCUEVal :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m VT.Tree
strToCUEVal s conf = do
  e <- parseExpr s
  evalToTree (evalExpr e) conf

runTreeStr :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m VT.Tree
runTreeStr s conf = parseSourceFile (ecFilePath conf) s >>= flip evalFile conf

evalFile :: (MonadError String m, MonadIO m) => SourceFile -> EvalConfig -> m VT.Tree
evalFile sf = evalToTree (evalSourceFile sf)

evalToTree ::
  (MonadError String m, MonadIO m) => StateT Common.EEState (ReaderT Runner m) VT.Tree -> EvalConfig -> m VT.Tree
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
            rootTC = Cursor.TreeCursor root [(RootTASeg, VT.mkNewTree VT.TNTop)]
            cv = RM.mkRTState rootTC (Common.eesObjID eeState) (Common.eesTrace eeState)
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
  let finalTC = Cursor.getTreeCursor finalized
  return $ Cursor.tcFocus finalTC
