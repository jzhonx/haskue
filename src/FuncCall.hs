{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FuncCall where

import Class
import Control.Monad.Except (throwError)
import Data.Maybe (fromJust)
import Path
import Text.Printf (printf)
import Util
import Value.Tree

{- | Check whether the function is reducible.
The first argument is the function node, and the second argument is the result of the function.
-}
isFuncTreeReducible :: Tree -> Tree -> Bool
isFuncTreeReducible fnt res =
  treeHasAtom res
    || isTreeBottom res
    || isTreeRefCycleTail res
    -- If the function tree does not have any references, then we can safely replace the function with the result.
    || not (treeHasRef fnt)

{- | Call the function. It returns the result of the function.
 - This must not modify the tree, i.e. the function is not reduced or no reduce is called.
 - No global states should be changed too.
 -
 - TODO: consider whether putting back the fn accidentally left the unwanted changes in Monad.
-}
callFunc :: (TreeMonad s m) => m (Maybe Tree)
callFunc = withTree $ \t -> case getFuncFromTree t of
  Just fn -> do
    let name = fncName fn
    dumpEntireTree ("callFunc " ++ name ++ " start")
    withDebugInfo $ \path _ ->
      logDebugStr $ printf "callFunc: path: %s, function %s, tip:\n%s" (show path) (show name) (show t)

    -- modified is not equivalent to reducible. For example, if the unification generates a new struct, it is not
    -- enough to replace the function with the new struct.
    modified <- invokeFunc fn

    res <- getTMTree
    withDebugInfo $ \path _ ->
      logDebugStr $
        printf
          "callFunc: path: %s, function %s, modified: %s, result:\n%s"
          (show path)
          (show name)
          (show modified)
          (show res)

    r <-
      if modified
        then case getFuncFromTree res of
          Just _ -> do
            -- recursively call the function until the result is not a function.
            -- the tip is already the res.
            callFunc
          Nothing -> do
            -- we need to restore the original tree with the new function result.
            putTMTree (mkFuncTree $ setFuncTempRes fn res)
            return (Just res)
        else return Nothing
    dumpEntireTree ("callFunc " ++ name ++ " done")
    return r
  Nothing -> throwError "callFunc: function not found"

{- | Try to reduce the function by using the function result to replace the function node.
This should be called after the function is evaluated.
-}
handleFuncCall :: (TreeMonad s m) => Maybe Tree -> m Bool
handleFuncCall valM = do
  reduced <-
    maybe
      (return False)
      ( \val -> withTree $ \t -> case getFuncFromTree t of
          Just fn ->
            if isTreeFunc val
              -- If the function returns another function, then the function is not reducible.
              then putTMTree val >> return False
              else do
                let
                  reducible = isFuncTreeReducible t val
                withDebugInfo $ \path _ ->
                  logDebugStr $
                    printf
                      "handleFuncCall: func %s, path: %s, is reducible: %s, args: %s"
                      (show $ fncName fn)
                      (show path)
                      (show reducible)
                      (show $ fncArgs fn)
                if reducible
                  then do
                    handleReduceRes val
                    path <- getTMAbsPath
                    -- we need to delete receiver starting with the path, not only is the path. For example, if the function is
                    -- index and the first argument is a reference, then the first argument dependency should also be deleted.
                    delNotifRecvs path
                  else do
                    -- restore the original function
                    putTMTree . mkFuncTree $ fn
                return reducible
          Nothing -> throwError "handleFuncCall: tree focus is not a function"
      )
      valM

  withTree $ \t -> case getFuncFromTree t of
    -- The result is still reduced to a reference, whether has been reduced to ref or was always ref.
    Just fn | isFuncRef fn -> do
      -- add notifier. If the referenced value changes, then the reference should be updated.
      -- duplicate cases are handled by the addCtxNotifier.
      withCtxTree $ \ct -> do
        tarPath <- getRefTarAbsPath fn
        logDebugStr $ printf "handleFuncCall: add notifier: (%s, %s)" (show tarPath) (show $ cvPath ct)
        putTMContext $ addCtxNotifier (cvCtx ct) (tarPath, cvPath ct)
    _ -> return ()

  return reduced

{- | Convert the RefCycleTail to RefCycle if the path is the same as the cycle start path.
RefCycleTail is like Bottom.
-}
handleReduceRes :: (TreeMonad s m) => Tree -> m ()
handleReduceRes val = case treeNode val of
  TNRefCycle (RefCycleTail (cycleStartPath, _)) -> do
    path <- getTMAbsPath
    if cycleStartPath == path
      then do
        logDebugStr $ printf "handleRefCycle: path: %s, cycle head found" (show path)
        -- The ref cycle tree must record the original tree.
        withTree $ \t -> putTMTree $ convRefCycleTree t False
      else putTMTree val
  _ -> putTMTree val

{- | Get the reference target absolute path. The target might not exist at the time, but the path should be valid as the
first selector is a locatable var.
-}
getRefTarAbsPath :: (TreeMonad s m) => Func Tree -> m Path
getRefTarAbsPath fn =
  if isFuncRef fn
    then do
      case treesToPath (fncArgs fn) of
        Just ref -> do
          let fstSel = fromJust $ headSel ref
          tc <- getTMCursor
          varTC <-
            maybeM
              (throwError $ printf "reference %s is not found" (show fstSel))
              return
              (searchTCVar fstSel tc)
          let fstSelAbsPath = tcPath varTC
          return $ maybe fstSelAbsPath (`appendPath` fstSelAbsPath) (tailPath ref)
        Nothing -> throwError "getTarAbsPath: can not generate path from the arguments"
    else throwError "getTarAbsPath: the function is not a reference"
