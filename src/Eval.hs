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
  CommonState (..),
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
runTreeIO s = fst <$> runTreeStr s emptyEvalConfig

runStr :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m (Either String AST.Expression)
runStr s conf = do
  (t, cs) <- runTreeStr s conf
  case treeNode t of
    -- print the error message to the console.
    TNBottom (Bottom msg) -> return $ Left $ printf "error: %s" msg
    _ -> Right <$> evalStateT (runReaderT (buildASTExpr t) emptyConfig) cs

strToCUEVal :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m (Tree, CommonState)
strToCUEVal s conf = do
  e <- parseExpr s
  evalToTree (evalExpr e) conf

runTreeStr :: (MonadError String m, MonadIO m) => String -> EvalConfig -> m (Tree, CommonState)
runTreeStr s conf = parseSourceFile (ecFilePath conf) s >>= flip evalFile conf

evalFile :: (MonadError String m, MonadIO m) => SourceFile -> EvalConfig -> m (Tree, CommonState)
evalFile sf = evalToTree (evalSourceFile sf)

evalToTree ::
  (MonadError String m, MonadIO m) =>
  StateT CommonState (ReaderT ReduceConfig m) Tree ->
  EvalConfig ->
  m (Tree, CommonState)
evalToTree f conf = do
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

  reduced <-
    runReaderT
      ( do
          (root, eeState) <- runStateT f emptyCommonState
          when (ecDebugMode conf) $
            liftIO $
              hPutStr stderr $
                "Initial eval result: " ++ treeToFullRepString root ++ "\n"
          let
            rootTC = TrCur root [(rootFeature, mkNewTree TNTop)]
            cv = mkRTState rootTC eeState
          execStateT (modifyError show reduce) cv
      )
      (ReduceConfig config (emptyReduceParams{createCnstr = True}))

  finalized <-
    runReaderT
      (execStateT (modifyError show postValidation) reduced)
      (ReduceConfig config emptyReduceParams)

  let finalTC = getTreeCursor finalized
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
