{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduction where

import qualified AST
import Class
import Config
import Control.Monad (foldM, forM, void, when)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (ask)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust)
import qualified Data.Set as Set
import FuncCall
import Path
import Ref
import Text.Printf (printf)
import Util
import Value.Tree

-- | Reduce the tree to the lowest form.
reduce :: (TreeMonad s m) => m ()
reduce = do
  path <- getTMAbsPath
  logDebugStr $ printf "reduce: path: %s, start" (show path)
  dumpEntireTree "reduce start"

  origT <- getTMTree
  withTree $ \t -> case treeNode t of
    TNFunc fn -> reduceFunc fn
    TNStruct _ -> reduceStruct
    TNList _ -> traverseSub reduce
    TNDisj _ -> traverseSub reduce
    _ -> return ()

  withTree $ \t -> do
    let nt = setOrig t (treeOrig origT)
    putTMTree nt

  withTree $ \t -> startReduceRef t reduceFunc

  logDebugStr $ printf "reduce: path: %s, done" (show path)
  dumpEntireTree "reduce done"

-- Reduce tree nodes

{- | Reduce the function.
- If the result can be used to replace the function itself, then the function is replaced by the result.
- Otherwise, the function is kept.
-}
reduceFunc :: (TreeMonad s m) => Func Tree -> m ()
reduceFunc fn = do
  void $ callFunc >>= handleFuncCall

  withDebugInfo $ \path t ->
    logDebugStr $
      printf
        "reduceFunc: path: %s, function %s reduced to:\n%s"
        (show path)
        (show $ fncName fn)
        (show t)

reduceAtomOpArg :: (TreeMonad s m) => Selector -> Tree -> m (Maybe Tree)
reduceAtomOpArg sel sub = do
  ret <-
    reduceFuncArgMaybe
      sel
      sub
      ( \rM -> case rM of
          Nothing -> Nothing
          Just r ->
            if isFuncTreeReducible sub r
              then rM
              else Nothing
      )
  logDebugStr $ printf "reduceAtomOpArg: %s is evaluated to %s" (show sub) (show ret)
  return ret

reduceFuncArg :: (TreeMonad s m) => Selector -> Tree -> m Tree
reduceFuncArg sel sub = withTree $ \t -> do
  ret <- reduceFuncArgMaybe sel sub (Just . fromMaybe t)
  logDebugStr $ printf "reduceFuncArg: %s is evaluated to %s" (show sub) (show ret)
  return $ fromJust ret

-- Evaluate the argument of the function.
-- This does not reduce the argument whose type is function.
-- Notice that if the argument is a function and the result of the function, such as struct or disjunction, is not
-- reducible, the result is still returned because the parent function needs the concrete value.
reduceFuncArgMaybe :: (TreeMonad s m) => Selector -> Tree -> (Maybe Tree -> Maybe Tree) -> m (Maybe Tree)
reduceFuncArgMaybe sel sub csHandler = withTree $ \t -> do
  withDebugInfo $ \path _ ->
    logDebugStr $ printf "reduceFuncArgMaybe: path: %s, start evaluation %s" (show path) (show sub)
  if isTreeFunc t
    then do
      res <-
        inSubTM
          sel
          sub
          ( withTree $ \x -> case treeNode x of
              -- reduce should not be directly called here because if the function is reduced to a ref, the ref itself
              -- will be returned instead of the desired value of the ref points to, due to that getting the value from
              -- the ref is not allowed. We need to apply the csHandler to the result of calling the function.
              TNFunc _ -> do
                r <- callFunc
                _ <- handleFuncCall r
                return $ csHandler r
              _ -> reduce >> Just <$> getTMTree
          )
      withDebugInfo $ \path _ ->
        logDebugStr $ printf "reduceFuncArgMaybe: path: %s, %s is evaluated to:\n%s" (show path) (show sub) (show res)
      return res
    else throwError "reduceFuncArgMaybe: node is not a function"

reduceStruct :: forall s m. (TreeMonad s m) => m ()
reduceStruct = do
  whenStruct () $ \s -> mapM_ (reduceStaticSF . fst) (Map.toList . stcSubs $ s)
  -- reduce the pendings.
  delIdxes <- whenStruct [] $ \s ->
    foldM
      (\acc (i, pend) -> reducePendSE (PendingSelector i, pend) >>= \r -> return $ if r then i : acc else acc)
      []
      (zip [0 ..] (stcPendSubs s))
  whenStruct () $ \s -> do
    putTMTree . mkStructTree $
      s
        { stcPendSubs = [pse | (i, pse) <- zip [0 ..] (stcPendSubs s), i `notElem` delIdxes]
        }

  -- reduce the patterns.
  whenStruct () $ \s ->
    mapM_ reducePattern (zip (map PatternSelector [0 ..]) (stcPatterns s))

  withDebugInfo $ \path t ->
    logDebugStr $ printf "reduceStruct: path: %s, new struct: %s" (show path) (show t)

whenStruct :: (TreeMonad s m) => a -> (Struct Tree -> m a) -> m a
whenStruct a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    TNStruct struct -> f struct
    _ -> do
      putTMTree . mkBottomTree $ printf "%s is not a struct" (show t)
      return a

mustStruct :: (TreeMonad s m) => (Struct Tree -> m a) -> m a
mustStruct f = withTree $ \t -> case treeNode t of
  TNStruct struct -> f struct
  _ -> throwError $ printf "%s is not a struct" (show t)

reduceStaticSF :: (TreeMonad s m) => StructSelector -> m ()
reduceStaticSF sel = whenStruct () $ \struct ->
  inSubTM (StructSelector sel) (ssfField (stcSubs struct Map.! sel)) reduce

reducePattern :: (TreeMonad s m) => (StructSelector, PatternStructField Tree) -> m ()
reducePattern (sel, psf) = whenStruct () $ \_ -> do
  inSubTM (StructSelector sel) (psfValue psf) reduce
  checkOrExtendStaticFields sel psf

reducePendSE :: (TreeMonad s m) => (StructSelector, PendingStructElem Tree) -> m Bool
reducePendSE (sel@(PendingSelector _), pse) = case pse of
  DynamicField dsf -> do
    -- evaluate the dynamic label.
    label <- inSubTM (StructSelector sel) (dsfLabel dsf) $ reduce >> getTMTree
    withDebugInfo $ \path _ ->
      logDebugStr $
        printf
          "reducePendSE: path: %s, dynamic label is evaluated to %s"
          (show path)
          (show label)
    case treeNode label of
      TNAtom (AtomV (String s)) -> do
        newSF <- mustStruct $ \struct -> return $ dynToStaticField dsf (stcSubs struct Map.!? StringSelector s)

        let sSel = StructSelector $ StringSelector s
        mergedT <- inDiscardSubTM sSel (ssfField newSF) (reduce >> getTMTree)
        -- TODO: use whenStruct because mergedT could be a bottom.
        mustStruct $ \struct ->
          putTMTree $ mkStructTree $ addStatic struct s (newSF{ssfField = mergedT})
        return True

      -- TODO: pending label
      _ -> putTMTree (mkBottomTree "selector can only be a string") >> return False
  PatternField pattern val -> do
    -- evaluate the pattern.
    pat <- inDiscardSubTM (StructSelector sel) pattern (reduce >> getTMTree)
    withDebugInfo $ \path _ ->
      logDebugStr $
        printf
          "reducePendSE: path: %s, pattern is evaluated to %s"
          (show path)
          (show pat)
    case treeNode pat of
      TNBounds bds ->
        if null (bdsList bds)
          then putTMTree (mkBottomTree "patterns must be non-empty") >> return False
          else do
            fieldCnstr <- inDiscardSubTM (StructSelector sel) val (reduce >> getTMTree)
            withDebugInfo $ \path _ ->
              logDebugStr $
                printf
                  "reducePendSE: path: %s, constraint is evaluated to %s"
                  (show path)
                  (show fieldCnstr)

            let psf = PatternStructField bds fieldCnstr
            checkOrExtendStaticFields sel psf
            whenNotBottom False $ do
              newStruct <- mustStruct $ \struct -> return $ mkNewTree . TNStruct $ addPattern psf struct
              putTMTree newStruct
              withDebugInfo $ \path _ ->
                logDebugStr $ printf "reducePendSE: path: %s, newStruct %s" (show path) (show newStruct)
              return True
      -- The label expression does not evaluate to a bounds.
      TNFunc _ -> return False
      _ ->
        putTMTree (mkBottomTree (printf "pattern should be bounds, but is %s" (show pat)))
          >> return False
 where
  dynToStaticField ::
    DynamicStructField Tree ->
    Maybe (StaticStructField Tree) ->
    StaticStructField Tree
  dynToStaticField dsf sfM = case sfM of
    Just sf ->
      StaticStructField
        { ssfField = mkFuncTree $ mkBinaryOp AST.Unify unify (ssfField sf) (dsfValue dsf)
        , ssfAttr = mergeAttrs (ssfAttr sf) (dsfAttr dsf)
        }
    Nothing ->
      StaticStructField
        { ssfField = dsfValue dsf
        , ssfAttr = dsfAttr dsf
        }

  -- Add the pattern to the struct. Return the new struct and the index of the pattern.
  addPattern :: PatternStructField Tree -> Struct Tree -> Struct Tree
  addPattern psf x = let patterns = stcPatterns x ++ [psf] in x{stcPatterns = patterns}
reducePendSE _ = throwError "evalStructField: invalid selector field combination"

-- Validate the existing statis fields of the struct.
checkOrExtendStaticFields ::
  (TreeMonad s m) =>
  StructSelector ->
  PatternStructField Tree ->
  m ()
checkOrExtendStaticFields sel psf = mustStruct $ \struct -> do
  let
    selPattern = psfPattern psf
    toValSels =
      [ mkFuncTree $ mkBinaryOp AST.Unify unify (mkAtomTree $ String s) (mkNewTree $ TNBounds selPattern)
      | (StringSelector s) <- stcOrdLabels struct
      ]
  cnstrSels <-
    mapM (\x -> inDiscardSubTM (StructSelector sel) x (reduce >> getTMTree)) toValSels
      >>= return
        . map
          ( \x -> case treeNode x of
              TNAtom (AtomV (String s)) -> s
              _ -> ""
          )
      >>= return . filter (/= "")

  logDebugStr $ printf "checkOrExtendStaticFields: start, cnstrSels: %s" (show cnstrSels)

  results <-
    mapM
      ( \s -> do
          let
            fieldCnstr = psfValue psf
            sf = stcSubs struct Map.! StringSelector s
            f = mkFuncTree $ mkBinaryOp AST.Unify unify (ssfField sf) fieldCnstr
          nf <- inDiscardSubTM (StructSelector sel) f (reduce >> getTMTree)
          return (s, nf)
      )
      cnstrSels

  let bottoms = filter (isTreeBottom . snd) results
  if not $ null bottoms
    then putTMTree (snd . head $ bottoms)
    else do
      newStruct <-
        foldM
          (\acc (s, nf) -> updateStatic acc s nf)
          struct
          results
      putTMTree $ mkStructTree newStruct
      withDebugInfo $ \path r ->
        logDebugStr $ printf "checkOrExtendStaticFields: path: %s, newStruct %s" (show path) (show r)

-- | Create a new identifier reference.
mkVarLinkTree :: (MonadError String m) => String -> AST.UnaryExpr -> m Tree
mkVarLinkTree var ue = do
  fn <- mkRefFunc (Path [StructSelector $ StringSelector var]) ue
  return $ mkFuncTree fn

-- | Create an index function node.
mkIndexFuncTree :: Tree -> Tree -> AST.UnaryExpr -> Tree
mkIndexFuncTree treeArg selArg ue = mkFuncTree $ case treeNode treeArg of
  TNFunc g
    | isFuncIndex g ->
        g
          { fncArgs = fncArgs g ++ [selArg]
          , fncExpr = return $ AST.ExprUnaryExpr ue
          }
  _ ->
    (mkStubFunc (index ue))
      { fncName = "index"
      , fncType = IndexFunc
      , fncArgs = [treeArg, selArg]
      , fncExpr = return $ AST.ExprUnaryExpr ue
      }

{- | Index the tree with the selectors. The index should have a list of arguments where the first argument is the tree
to be indexed, and the rest of the arguments are the selectors.
-}
index :: (TreeMonad s m) => AST.UnaryExpr -> [Tree] -> m Bool
index ue ts@(t : _)
  | length ts > 1 = do
      idxPathM <- treesToPath <$> mapM evalIndexArg [1 .. length ts - 1]
      whenJustE idxPathM $ \idxPath -> case treeNode t of
        TNFunc fn
          -- If the function is a ref, then we should append the path to the ref. For example, if the ref is a.b, and
          -- the path is c, then the new ref should be a.b.c.
          | isFuncRef fn -> do
              refFunc <- appendRefFuncPath fn idxPath ue
              putTMTree (mkFuncTree refFunc)
        -- in-place expression, like ({}).a, or regular functions.
        _ -> do
          res <- reduceFuncArg (FuncSelector $ FuncArgSelector 0) t
          putTMTree res
          logDebugStr $ printf "index: tree is reduced to %s, idxPath: %s" (show res) (show idxPath)

          -- descendTM can not be used here because it would change the tree cursor.
          tc <- getTMCursor
          maybe
            (throwError $ printf "index: %s is not found" (show idxPath))
            (putTMTree . vcFocus)
            (goDownTCPath idxPath tc)
          withDebugInfo $ \_ r ->
            logDebugStr $ printf "index: the indexed is %s" (show r)
      -- The tree has been modified.
      return True
 where
  evalIndexArg :: (TreeMonad s m) => Int -> m Tree
  evalIndexArg i = inSubTM (FuncSelector $ FuncArgSelector i) (ts !! i) (reduce >> getTMTree)

  whenJustE :: (Monad m) => Maybe a -> (a -> m ()) -> m ()
  whenJustE m f = maybe (return ()) f m
index _ _ = throwError "index: invalid arguments"

appendRefFuncPath :: (TreeMonad s m) => Func Tree -> Path -> AST.UnaryExpr -> m (Func Tree)
appendRefFuncPath fn p ue
  | isFuncRef fn = do
      origTP <-
        maybe
          (throwError "appendRefFuncPath: can not generate path from the arguments")
          return
          (treesToPath (fncArgs fn))
      let tp = appendPath p origTP
      -- Reference the target node when the target node is not an atom or a cycle head.
      mkRefFunc tp ue
appendRefFuncPath _ _ _ = throwError "appendRefFuncPath: invalid function type"

mkRefFunc :: (MonadError String m) => Path -> AST.UnaryExpr -> m (Func Tree)
mkRefFunc tp ue = do
  args <-
    maybe
      (throwError "mkRefFunc: can not generate path from the arguments")
      return
      (pathToTrees tp)
  let f =
        mkStubFunc
          ( \_ -> do
              ok <- deref tp
              when ok $ withTree $ \t -> putTMTree t
              return ok
          )
  return
    f
      { fncName = printf "&%s" (show tp)
      , fncType = RefFunc
      , fncArgs = args
      , fncExpr = return $ AST.ExprUnaryExpr ue
      }

validateCnstrs :: (TreeMonad s m) => m ()
validateCnstrs = do
  logDebugStr "validateCnstrs: start"

  ctx <- getTMContext
  -- remove all notifiers.
  putTMContext $ ctx{ctxNotifiers = Map.empty}
  -- first rewrite all functions to their results if the results exist.
  snapshotTM

  -- then validate all constraints.
  traverseTM $ withTN $ \case
    TNConstraint c -> validateCnstr c
    _ -> return ()

-- Validate the constraint. It creates a validate function, and then evaluates the function. Notice that the validator
-- will be assigned to the constraint in the propValUp.
validateCnstr :: (TreeMonad s m) => Constraint Tree -> m ()
validateCnstr c = withTree $ \_ -> do
  withDebugInfo $ \path _ -> do
    tc <- getTMCursor
    Config{cfCreateCnstr = cc} <- ask
    logDebugStr $
      printf
        "validateCnstr: path: %s, validator: %s, cc: %s constraint unify tc:\n%s"
        (show path)
        (show (cnsValidator c))
        (show cc)
        (show tc)

  -- make sure return the latest atom
  let atomT = mkAtomVTree $ cnsAtom c
  -- run the validator in a sub context.
  pushTMSub unaryOpSelector (cnsValidator c)
  res <- reduce >> getTMTree
  discardTMAndPop

  putTMTree $
    if
      | isTreeAtom res -> atomT
      -- incomplete case
      | isTreeFunc res -> res
      | otherwise -> mkBottomTree $ printf "constraint not satisfied, %s" (show res)

dispUnaryFunc :: (TreeMonad s m) => AST.UnaryOp -> Tree -> m Bool
dispUnaryFunc op _t = do
  tM <- reduceAtomOpArg unaryOpSelector _t
  case tM of
    Just t -> case treeNode t of
      TNAtom ta -> case (op, amvAtom ta) of
        (AST.Plus, Int i) -> ia i id
        (AST.Plus, Float i) -> fa i id
        (AST.Minus, Int i) -> ia i negate
        (AST.Minus, Float i) -> fa i negate
        (AST.Not, Bool b) -> putTMTree (mkAtomTree (Bool (not b))) >> return True
        (AST.UnaRelOp uop, _) -> case (uop, amvAtom ta) of
          (AST.NE, a) -> mkb (BdNE a)
          (AST.LT, Int i) -> mkib BdLT i
          (AST.LT, Float f) -> mkfb BdLT f
          (AST.LE, Int i) -> mkib BdLE i
          (AST.LE, Float f) -> mkfb BdLE f
          (AST.GT, Int i) -> mkib BdGT i
          (AST.GT, Float f) -> mkfb BdGT f
          (AST.GE, Int i) -> mkib BdGE i
          (AST.GE, Float f) -> mkfb BdGE f
          (AST.ReMatch, String p) -> putTMTree (mkBoundsTree [BdStrMatch $ BdReMatch p]) >> return True
          (AST.ReNotMatch, String p) -> putTMTree (mkBoundsTree [BdStrMatch $ BdReNotMatch p]) >> return True
          _ -> putConflict
        _ -> putConflict
      TNRefCycle (RefCycleTail _) -> putTMTree t >> return True
      _ -> putConflict
    Nothing -> return False
 where
  conflict :: Tree
  conflict = mkBottomTree $ printf "%s cannot be used for %s" (show _t) (show op)

  putConflict :: (TreeMonad s m) => m Bool
  putConflict = putTMTree conflict >> return True

  ia :: (TreeMonad s m) => Integer -> (Integer -> Integer) -> m Bool
  ia a f = putTMTree (mkAtomTree (Int $ f a)) >> return True

  fa :: (TreeMonad s m) => Double -> (Double -> Double) -> m Bool
  fa a f = putTMTree (mkAtomTree (Float $ f a)) >> return True

  mkb :: (TreeMonad s m) => Bound -> m Bool
  mkb b = putTMTree (mkBoundsTree [b]) >> return True

  mkib :: (TreeMonad s m) => BdNumCmpOp -> Integer -> m Bool
  mkib uop i = putTMTree (mkBoundsTree [BdNumCmp $ BdNumCmpCons uop (NumInt i)]) >> return True

  mkfb :: (TreeMonad s m) => BdNumCmpOp -> Double -> m Bool
  mkfb uop f = putTMTree (mkBoundsTree [BdNumCmp $ BdNumCmpCons uop (NumFloat f)]) >> return True

dispBinFunc :: (TreeMonad s m) => AST.BinaryOp -> Tree -> Tree -> m Bool
dispBinFunc op = case op of
  AST.Unify -> unify
  _ -> regBin op

regBin :: (TreeMonad s m) => AST.BinaryOp -> Tree -> Tree -> m Bool
regBin op t1 t2 = regBinDir op (L, t1) (R, t2)

regBinDir :: (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> m Bool
regBinDir op (d1, _t1) (d2, _t2) = do
  withDebugInfo $ \path _ ->
    logDebugStr $
      printf "regBinDir: path: %s, %s: %s with %s: %s" (show path) (show d1) (show _t1) (show d2) (show _t2)

  t1M <- reduceAtomOpArg (toBinOpSelector d1) _t1
  t2M <- reduceAtomOpArg (toBinOpSelector d2) _t2

  withDebugInfo $ \path _ ->
    logDebugStr $
      printf "regBinDir: path: %s, reduced args, %s: %s with %s: %s" (show path) (show d1) (show t1M) (show d2) (show t2M)

  case (t1M, t2M) of
    (Just t1, Just t2) -> case (treeNode t1, treeNode t2) of
      (TNBottom _, _) -> putTMTree t1 >> return True
      (_, TNBottom _) -> putTMTree t2 >> return True
      (TNRefCycle (RefCycleTail _), _) -> putTMTree t1 >> return True
      (_, TNRefCycle (RefCycleTail _)) -> putTMTree t2 >> return True
      (TNAtom l1, _) -> regBinLeftAtom op (d1, l1, t1) (d2, t2)
      (_, TNAtom l2) -> regBinLeftAtom op (d2, l2, t2) (d1, t1)
      (TNStruct s1, _) -> regBinLeftStruct op (d1, s1, t1) (d2, t2)
      (_, TNStruct s2) -> regBinLeftStruct op (d2, s2, t2) (d1, t1)
      (TNDisj dj1, _) -> regBinLeftDisj op (d1, dj1, t1) (d2, t2)
      (_, TNDisj dj2) -> regBinLeftDisj op (d2, dj2, t2) (d1, t1)
      _ -> regBinLeftOther op (d1, t1) (d2, t2)
    _ -> return False

regBinLeftAtom :: (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, AtomV, Tree) -> (BinOpDirect, Tree) -> m Bool
regBinLeftAtom op (d1, ta1, t1) (d2, t2) = do
  logDebugStr $ printf "regBinLeftAtom: %s (%s: %s) (%s: %s)" (show op) (show d1) (show ta1) (show d2) (show t2)
  if
    -- comparison operators
    | isJust (lookup op cmpOps) -> case treeNode t2 of
        TNAtom ta2 ->
          let
            a2 = amvAtom ta2
            f :: (Atom -> Atom -> Bool)
            f = fromJust (lookup op cmpOps)
            r = case (a1, a2) of
              (String _, String _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Int _, Int _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Int _, Float _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Float _, Int _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Float _, Float _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Bool _, Bool _) -> Right . Bool $ dirApply f (d1, a1) a2
              (Null, _) -> Right . Bool $ dirApply f (d1, a1) a2
              (_, Null) -> Right . Bool $ dirApply f (d2, a2) a1
              _ -> Left $ uncmpAtoms a1 a2
           in
            case r of
              Right b -> putTree $ mkAtomTree b
              Left err -> putTree err
        TNDisj dj2 -> regBinLeftDisj op (d2, dj2, t2) (d1, t1)
        TNStruct _ -> putTree $ cmpNull a1 t2
        TNList _ -> putTree $ cmpNull a1 t2
        _ -> regBinLeftOther op (d2, t2) (d1, t1)
    -- arithmetic operators
    | op `elem` arithOps -> case treeNode t2 of
        TNAtom ta2 ->
          let
            r = case op of
              AST.Add -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (+) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (+) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (+) (d1, i1) (fromIntegral i2)
                (String s1, String s2) -> Right . String $ dirApply (++) (d1, s1) s2
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              AST.Sub -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (-) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (-) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (-) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              AST.Mul -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Int $ dirApply (*) (d1, i1) i2
                (Int i1, Float i2) -> Right . Float $ dirApply (*) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (*) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              AST.Div -> case (a1, amvAtom ta2) of
                (Int i1, Int i2) -> Right . Float $ dirApply (/) (d1, fromIntegral i1) (fromIntegral i2)
                (Int i1, Float i2) -> Right . Float $ dirApply (/) (d1, fromIntegral i1) i2
                (Float i1, Int i2) -> Right . Float $ dirApply (/) (d1, i1) (fromIntegral i2)
                _ -> Left $ mismatch op a1 (amvAtom ta2)
              _ -> Left $ mismatch op a1 (amvAtom ta2)
           in
            case r of
              Right b -> putTree $ mkAtomTree b
              Left err -> putTree err
        TNDisj dj2 -> regBinLeftDisj op (d2, dj2, t2) (d1, t1)
        TNStruct _ -> putTree $ mismatchArith a1 t2
        TNList _ -> putTree $ mismatchArith a1 t2
        _ -> regBinLeftOther op (d2, t2) (d1, t1)
    | otherwise -> putTree (mkBottomTree $ printf "operator %s is not supported" (show op))
 where
  a1 = amvAtom ta1
  cmpOps = [(AST.Equ, (==)), (AST.BinRelOp AST.NE, (/=))]
  arithOps = [AST.Add, AST.Sub, AST.Mul, AST.Div]

  putTree :: (TreeMonad s m) => Tree -> m Bool
  putTree x = putTMTree x >> return True

  uncmpAtoms :: Atom -> Atom -> Tree
  uncmpAtoms x y = mkBottomTree $ printf "%s and %s are not comparable" (show x) (show y)

  cmpNull :: Atom -> Tree -> Tree
  cmpNull a t =
    if
      -- There is no way for a non-atom to be compared with a non-null atom.
      | a /= Null -> mismatch op a t
      | op == AST.Equ -> mkAtomTree (Bool False)
      | op == AST.BinRelOp AST.NE -> mkAtomTree (Bool True)
      | otherwise -> mkBottomTree $ printf "operator %s is not supported" (show op)

  mismatchArith :: (Show a, Show b) => a -> b -> Tree
  mismatchArith = mismatch op

dirApply :: (a -> a -> b) -> (BinOpDirect, a) -> a -> b
dirApply f (di1, i1) i2 = if di1 == L then f i1 i2 else f i2 i1

mismatch :: (Show a, Show b) => AST.BinaryOp -> a -> b -> Tree
mismatch op x y = mkBottomTree $ printf "%s can not be used for %s and %s" (show op) (show x) (show y)

regBinLeftStruct ::
  (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, Struct Tree, Tree) -> (BinOpDirect, Tree) -> m Bool
regBinLeftStruct op (d1, _, t1) (d2, t2) = case treeNode t2 of
  TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1)
  _ -> putTMTree (mismatch op t1 t2) >> return True

regBinLeftDisj ::
  (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, Disj Tree, Tree) -> (BinOpDirect, Tree) -> m Bool
regBinLeftDisj op (d1, dj1, t1) (d2, t2) = case dj1 of
  Disj{dsjDefault = Just d} -> regBinDir op (d1, d) (d2, t2)
  _ -> case treeNode t2 of
    TNAtom a2 -> regBinLeftAtom op (d2, a2, t2) (d1, t1)
    _ -> putTMTree (mismatch op t1 t2) >> return True

regBinLeftOther :: (TreeMonad s m) => AST.BinaryOp -> (BinOpDirect, Tree) -> (BinOpDirect, Tree) -> m Bool
regBinLeftOther op (d1, t1) (d2, t2) = do
  withDebugInfo $ \path _ ->
    logDebugStr $ printf "regBinLeftOther: path: %s, %s: %s, %s: %s" (show path) (show d1) (show t1) (show d2) (show t2)
  case (treeNode t1, t2) of
    (TNRefCycle _, _) -> return False
    (TNConstraint c, _) -> do
      na <- regBinDir op (d1, mkNewTree (TNAtom $ cnsAtom c)) (d2, t2) >> getTMTree
      case treeNode na of
        TNAtom atom -> putTMTree (mkNewTree (TNConstraint $ updateCnstrAtom atom c)) >> return True
        _ -> undefined
    _ -> putTMTree (mkBottomTree mismatchErr) >> return True
 where
  mismatchErr :: String
  mismatchErr = printf "values %s and %s cannot be used for %s" (show t1) (show t2) (show op)

data DisjItem = DisjDefault Tree | DisjRegular Tree

instance Show DisjItem where
  show (DisjDefault t) = show t
  show (DisjRegular t) = show t

-- reduceDisjPair is used to evaluate a disjunction whose both sides are evaluated.
reduceDisjPair :: (TreeMonad s m) => DisjItem -> DisjItem -> m Tree
reduceDisjPair i1 i2 = case (i1, i2) of
  (DisjDefault v1, _) -> do
    logDebugStr $ printf "reduceDisjPair: *: %s, r: %s" (show v1) (show i2)
    t <- reduceLeftDefault (\(df1, ds1, df2, ds2) -> newDisj df1 ds1 df2 ds2) v1 i2
    logDebugStr $ printf "reduceDisjPair: *: %s, r: %s, resulting to:\n%s" (show v1) (show i2) (show t)
    return t
  -- reverse v2 r1 and also the order to the disjCons.
  (DisjRegular _, DisjDefault v2) -> do
    reduceLeftDefault (\(df2, ds2, df1, ds1) -> newDisj df1 ds1 df2 ds2) v2 i1
  (DisjRegular v1, DisjRegular v2) -> do
    logDebugStr $ printf "reduceDisjPair: both regulars v1: %s, v2: %s" (show v1) (show v2)
    r <- reduceRegularDisj v1 v2
    logDebugStr $ printf "reduceDisjPair: both regulars results: %s" (show r)
    return r

-- reduceLeftDefault is used to evaluate a disjunction whose left side is a default.
-- the first argument is a function that takes the four lists of values and returns a disjunction.
reduceLeftDefault ::
  (MonadError String m) => ((Maybe Tree, [Tree], Maybe Tree, [Tree]) -> m Tree) -> Tree -> DisjItem -> m Tree
-- Below is rule M2 and M3. We eliminate the defaults from the right side.
reduceLeftDefault disjCons (Tree{treeNode = TNDisj dj1}) (DisjRegular (Tree{treeNode = TNDisj dj2})) =
  disjCons (dsjDefault dj1, dsjDisjuncts dj1, Nothing, dsjDisjuncts dj2)
-- Below is rule M1.
reduceLeftDefault disjCons v1 (DisjRegular (Tree{treeNode = TNDisj dj2})) =
  disjCons (Just v1, [v1], dsjDefault dj2, dsjDisjuncts dj2)
reduceLeftDefault disjCons v1 (DisjRegular v2) =
  disjCons (Just v1, [v1], Nothing, [v2])
reduceLeftDefault disjCons v1 (DisjDefault v2) =
  disjCons (Nothing, [v1], Nothing, [v2])

-- evalFullDisj is used to evaluate a disjunction whose both sides are regular.
-- Rule: D1, D2
reduceRegularDisj :: (TreeMonad s m) => Tree -> Tree -> m Tree
reduceRegularDisj (Tree{treeNode = TNDisj dj1}) (Tree{treeNode = TNDisj dj2}) =
  newDisj (dsjDefault dj1) (dsjDisjuncts dj1) (dsjDefault dj2) (dsjDisjuncts dj2)
reduceRegularDisj (Tree{treeNode = TNDisj dj}) y = newDisj (dsjDefault dj) (dsjDisjuncts dj) Nothing [y]
reduceRegularDisj x (Tree{treeNode = TNDisj dj}) = newDisj Nothing [x] (dsjDefault dj) (dsjDisjuncts dj)
-- Rule D0
reduceRegularDisj x y = newDisj Nothing [x] Nothing [y]

-- dedupAppend appends unique elements in ys to the xs list, but only if they are not already in xs.
-- xs and ys are guaranteed to be unique.
dedupAppend :: [Tree] -> [Tree] -> [Tree]
dedupAppend xs ys = xs ++ foldr (\y acc -> if y `elem` xs then acc else y : acc) [] ys

newDisj :: (TreeMonad s m) => Maybe Tree -> [Tree] -> Maybe Tree -> [Tree] -> m Tree
newDisj df1 ds1 df2 ds2 =
  let
    st :: Maybe Tree
    st = case map fromJust (filter isJust [df1, df2]) of
      [x] -> Just x
      [x, y] -> Just $ mkDisjTree Nothing [x, y]
      _ -> Nothing
   in
    return $ mkDisjTree st (dedupAppend ds1 ds2)

data UTree = UTree
  { utVal :: Tree
  , utDir :: Path.BinOpDirect
  , utEmbedded :: Bool
  -- ^ Whether the tree is embedded in a struct.
  }

instance Show UTree where
  show (UTree t d e) = printf "(%s,e:%s,\n%s)" (show d) (show e) (show t)

unify :: (TreeMonad s m) => Tree -> Tree -> m Bool
unify t1 t2 = unifyUTrees (UTree t1 Path.L False) (UTree t2 Path.R False)

-- | Unify the right embedded tree with the left tree.
unifyREmbedded :: (TreeMonad s m) => Tree -> Tree -> m Bool
unifyREmbedded t1 t2 = unifyUTrees (UTree t1 Path.L False) (UTree t2 Path.R True)

-- If there exists a struct beneath the current node, we need to be careful about the references in the struct. We
-- should not further reduce the values of the references.
-- For example, {a: b + 100, b: a - 100} & {b: 50}. The "b" in the first struct will have to see the atom 50.
unifyUTrees :: (TreeMonad s m) => UTree -> UTree -> m Bool
unifyUTrees ut1@(UTree{utVal = t1}) ut2@(UTree{utVal = t2}) = do
  withDebugInfo $ \path _ ->
    logDebugStr $
      printf ("unifying start, path: %s:, %s" ++ "\n" ++ "with %s") (show path) (show ut1) (show ut2)

  -- Each case should handle embedded case when the left value is embedded.
  r <- case (treeNode t1, treeNode t2) of
    (TNBottom _, _) -> putTree t1
    (_, TNBottom _) -> putTree t2
    (TNTop, _) -> unifyLeftTop ut1 ut2
    (_, TNTop) -> unifyLeftTop ut2 ut1
    (TNAtom a1, _) -> unifyLeftAtom (a1, ut1) ut2
    -- Below is the earliest time to create a constraint
    (_, TNAtom a2) -> unifyLeftAtom (a2, ut2) ut1
    (TNDisj dj1, _) -> unifyLeftDisj (dj1, ut1) ut2
    (TNStruct s1, _) -> unifyLeftStruct (s1, ut1) ut2
    (TNBounds b1, _) -> unifyLeftBound (b1, ut1) ut2
    _ -> unifyLeftOther ut1 ut2

  withDebugInfo $ \path res ->
    logDebugStr $
      printf "unifying done, path: %s, %s with %s, res: %s" (show path) (show ut1) (show ut2) (show res)
  return r
 where
  putTree :: (TreeMonad s m) => Tree -> m Bool
  putTree x = putTMTree x >> return True

unifyLeftTop :: (TreeMonad s m) => UTree -> UTree -> m Bool
unifyLeftTop ut1 ut2 = do
  case treeNode . utVal $ ut2 of
    -- If the left top is embedded in the right struct, we can immediately put the top into the tree without worrying
    -- any future existing/new fields. Because for example {_, a: 1} is equivalent to _ & {a: 1}. This follows the
    -- behavior of the spec:
    -- The result of { A } is A for any A (including definitions).
    -- Notice that this is different from the behavior of the latest CUE. The latest CUE would do the following:
    -- {_, _h: int} & {_h: "hidden"} -> _|_.
    TNStruct _ | utEmbedded ut1 -> putTMTree (utVal ut1)
    _ -> putTMTree (utVal ut2)
  return True

unifyLeftAtom :: (TreeMonad s m) => (AtomV, UTree) -> UTree -> m Bool
unifyLeftAtom (v1, ut1@(UTree{utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = do
  case (amvAtom v1, treeNode t2) of
    (String x, TNAtom s)
      | String y <- amvAtom s -> putTree $ if x == y then TNAtom v1 else amismatch x y
    (Int x, TNAtom s)
      | Int y <- amvAtom s -> putTree $ if x == y then TNAtom v1 else amismatch x y
    (Float x, TNAtom s)
      | Float y <- amvAtom s -> putTree $ if x == y then TNAtom v1 else amismatch x y
    (Bool x, TNAtom s)
      | Bool y <- amvAtom s -> putTree $ if x == y then TNAtom v1 else amismatch x y
    (Null, TNAtom s) | Null <- amvAtom s -> putTree $ TNAtom v1
    (_, TNBounds b) -> do
      logDebugStr $ printf "unifyLeftAtom, %s with Bounds: %s" (show v1) (show t2)
      putTMTree $ unifyAtomBounds (d1, amvAtom v1) (d2, bdsList b)
      return True
    (_, TNConstraint c) ->
      if v1 == cnsAtom c
        then putCnstr (cnsAtom c) >> return True
        else do
          putTMTree . mkBottomTree $
            printf "values mismatch: %s != %s" (show v1) (show $ cnsAtom c)
          return True
    (_, TNDisj dj2) -> do
      logDebugStr $ printf "unifyLeftAtom: TNDisj %s, %s" (show t2) (show v1)
      unifyLeftDisj (dj2, ut2) ut1
    (_, TNFunc fn2) -> case fncType fn2 of
      -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
      -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
      -- marked disjunction.
      DisjFunc -> unifyLeftOther ut2 ut1
      _ -> procOther
    (_, TNRefCycle _) -> procOther
    -- If the left atom is embedded in the right struct and there is no fields and no pending dynamic fields, we can
    -- immediately put the atom into the tree without worrying any future new fields. This is what CUE currently
    -- does.
    (_, TNStruct s2) | utEmbedded ut1 && hasEmptyFields s2 -> putTree (TNAtom v1)
    _ -> unifyLeftOther ut1 ut2
 where
  putTree :: (TreeMonad s m) => TreeNode Tree -> m Bool
  putTree n = do
    withTree $ \t -> putTMTree $ setTN t n
    return True

  amismatch :: (Show a) => a -> a -> TreeNode Tree
  amismatch x y = TNBottom . Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

  procOther :: (TreeMonad s m) => m Bool
  procOther = do
    Config{cfCreateCnstr = cc} <- ask
    logDebugStr $ printf "unifyLeftAtom: cc: %s, procOther: %s, %s" (show cc) (show ut1) (show ut2)
    if cc
      then putCnstr v1 >> return True
      else unifyLeftOther ut2 ut1

  putCnstr :: (TreeMonad s m) => AtomV -> m ()
  putCnstr a1 = withTree $ \t -> putTMTree $ mkCnstrTree a1 t

unifyLeftBound :: (TreeMonad s m) => (Bounds, UTree) -> UTree -> m Bool
unifyLeftBound (b1, ut1@(UTree{utVal = t1, utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = case treeNode t2 of
  TNAtom ta2 -> do
    logDebugStr $ printf "unifyAtomBounds: %s, %s" (show t1) (show t2)
    putTMTree $ unifyAtomBounds (d2, amvAtom ta2) (d1, bdsList b1)
    return True
  TNBounds b2 -> do
    logDebugStr $ printf "unifyBoundList: %s, %s" (show t1) (show t2)
    let res = unifyBoundList (d1, bdsList b1) (d2, bdsList b2)
    case res of
      Left err -> putTMTree (mkBottomTree err) >> return True
      Right bs ->
        let
          r =
            foldl
              ( \acc x -> case x of
                  BdIsAtom a -> (fst acc, Just a)
                  _ -> (x : fst acc, snd acc)
              )
              ([], Nothing)
              bs
         in
          case snd r of
            Just a -> putTMTree (mkAtomTree a) >> return True
            Nothing -> putTMTree (mkBoundsTree (fst r)) >> return True
  -- If the left bounds are embedded in the right struct and there is no fields and no pending dynamic fields, we can
  -- immediately put the bounds into the tree without worrying any future new fields. This is what CUE currently
  -- does.
  TNStruct s2 | utEmbedded ut1 && hasEmptyFields s2 -> putTMTree t1 >> return True
  _ -> unifyLeftOther ut2 ut1

unifyAtomBounds :: (Path.BinOpDirect, Atom) -> (Path.BinOpDirect, [Bound]) -> Tree
unifyAtomBounds (d1, a1) (d2, bs) =
  -- try to find the atom in the bounds list.
  foldl1 findAtom (map withBound bs)
 where
  ta1 = mkAtomTree a1

  findAtom acc x = if acc == ta1 || x == ta1 then acc else x

  withBound :: Bound -> Tree
  withBound b =
    let
      r = unifyBounds (d1, BdIsAtom a1) (d2, b)
     in
      case r of
        Left s -> mkBottomTree s
        Right v -> case v of
          [x] -> case x of
            BdIsAtom a -> mkAtomTree a
            _ -> mkBottomTree $ printf "unexpected bounds unification result: %s" (show x)
          _ -> mkBottomTree $ printf "unexpected bounds unification result: %s" (show v)

-- TODO: regex implementation
-- Second argument is the pattern.
reMatch :: String -> String -> Bool
reMatch = (==)

-- TODO: regex implementation
-- Second argument is the pattern.
reNotMatch :: String -> String -> Bool
reNotMatch = (/=)

unifyBoundList :: (Path.BinOpDirect, [Bound]) -> (Path.BinOpDirect, [Bound]) -> Either String [Bound]
unifyBoundList (d1, bs1) (d2, bs2) = case (bs1, bs2) of
  ([], _) -> return bs2
  (_, []) -> return bs1
  _ -> do
    bss <- manyToMany (d1, bs1) (d2, bs2)
    let bsMap = Map.fromListWith (++) (map (\b -> (bdRep b, [b])) (concat bss))
    norm <- forM bsMap narrowBounds
    let m = Map.toList norm
    return $ concat $ map snd m
 where
  oneToMany :: (Path.BinOpDirect, Bound) -> (Path.BinOpDirect, [Bound]) -> Either String [Bound]
  oneToMany (ld1, b) (ld2, ts) =
    let f x y = unifyBounds (ld1, x) (ld2, y)
     in do
          r <- mapM (`f` b) ts
          return $ concat r

  manyToMany :: (Path.BinOpDirect, [Bound]) -> (Path.BinOpDirect, [Bound]) -> Either String [[Bound]]
  manyToMany (ld1, ts1) (ld2, ts2) =
    if ld1 == Path.R
      then mapM (\y -> oneToMany (ld2, y) (ld1, ts1)) ts2
      else mapM (\x -> oneToMany (ld1, x) (ld2, ts2)) ts1

-- | Narrow the bounds to the smallest set of bounds for the same bound type.
narrowBounds :: [Bound] -> Either String [Bound]
narrowBounds xs = case xs of
  [] -> return []
  (BdNE _) : _ -> return xs
  x : rs ->
    let
      f acc y =
        if length acc == 1
          then unifyBounds (Path.L, acc !! 0) (Path.R, y)
          else Left "bounds mismatch"
     in
      foldM f [x] rs

unifyBounds :: (Path.BinOpDirect, Bound) -> (Path.BinOpDirect, Bound) -> Either String [Bound]
unifyBounds db1@(d1, b1) db2@(_, b2) = case b1 of
  BdNE a1 -> case b2 of
    BdNE a2 -> return $ if a1 == a2 then [b1] else newOrdBounds
    BdNumCmp c2 -> uNENumCmp a1 c2
    BdStrMatch m2 -> uNEStrMatch a1 m2
    BdType t2 -> uNEType a1 t2
    BdIsAtom a2 -> if a1 == a2 then Left conflict else return [b2]
  BdNumCmp c1 -> case b2 of
    BdNumCmp c2 -> uNumCmpNumCmp c1 c2
    BdStrMatch _ -> Left conflict
    BdType t2 ->
      if t2 `elem` [BdInt, BdFloat, BdNumber]
        then return [b1]
        else Left conflict
    BdIsAtom a2 -> uNumCmpAtom c1 a2
    _ -> unifyBounds db2 db1
  BdStrMatch m1 -> case b2 of
    BdStrMatch m2 -> case (m1, m2) of
      (BdReMatch _, BdReMatch _) -> return $ if m1 == m2 then [b1] else newOrdBounds
      (BdReNotMatch _, BdReNotMatch _) -> return $ if m1 == m2 then [b1] else newOrdBounds
      _ -> return [b1, b2]
    BdType t2 ->
      if t2 `elem` [BdString]
        then return [b1]
        else Left conflict
    BdIsAtom a2 -> uStrMatchAtom m1 a2
    _ -> unifyBounds db2 db1
  BdType t1 -> case b2 of
    BdType t2 -> if t1 == t2 then return [b1] else Left conflict
    BdIsAtom a2 -> uTypeAtom t1 a2
    _ -> unifyBounds db2 db1
  BdIsAtom a1 -> case b2 of
    BdIsAtom a2 -> if a1 == a2 then return [b1] else Left conflict
    _ -> unifyBounds db2 db1
 where
  uNENumCmp :: Atom -> BdNumCmp -> Either String [Bound]
  uNENumCmp a1 (BdNumCmpCons o2 y) = do
    x <- case a1 of
      Int x -> return $ NumInt x
      Float x -> return $ NumFloat x
      _ -> Left conflict
    case o2 of
      BdLT -> if x < y then Left conflict else return newOrdBounds
      BdLE -> if x <= y then Left conflict else return newOrdBounds
      BdGT -> if x > y then Left conflict else return newOrdBounds
      BdGE -> if x >= y then Left conflict else return newOrdBounds

  uNEStrMatch :: Atom -> BdStrMatch -> Either String [Bound]
  uNEStrMatch a1 m2 = do
    _ <- case a1 of
      String x -> return x
      _ -> Left conflict
    case m2 of
      -- delay verification
      BdReMatch _ -> return [b1, b2]
      BdReNotMatch _ -> return [b1, b2]

  uNEType :: Atom -> BdType -> Either String [Bound]
  uNEType a1 t2 = case a1 of
    Bool _ -> if BdBool == t2 then Left conflict else return newOrdBounds
    Int _ -> if BdInt == t2 then Left conflict else return newOrdBounds
    Float _ -> if BdFloat == t2 then Left conflict else return newOrdBounds
    String _ -> if BdString == t2 then Left conflict else return newOrdBounds
    -- TODO: null?
    _ -> Left conflict

  ncncGroup :: [([BdNumCmpOp], [(Number -> Number -> Bool)])]
  ncncGroup =
    [ ([BdLT, BdLE], [(<=), (>)])
    , ([BdGT, BdGE], [(>=), (<)])
    ]

  uNumCmpNumCmp :: BdNumCmp -> BdNumCmp -> Either String [Bound]
  uNumCmpNumCmp (BdNumCmpCons o1 n1) (BdNumCmpCons o2 n2) =
    let
      c1g = if o1 `elem` fst (ncncGroup !! 0) then ncncGroup !! 0 else ncncGroup !! 1
      c1SameGCmp = snd c1g !! 0
      c1OppGCmp = snd c1g !! 1
      isSameGroup = o2 `elem` (fst c1g)
      oppClosedEnds = sort [o1, o2] == [BdLE, BdGE]
     in
      if isSameGroup
        then return $ if c1SameGCmp n1 n2 then [b1] else [b2]
        else
          if
            | oppClosedEnds && n1 == n2 -> case n1 of
                NumInt i -> return [BdIsAtom $ Int i]
                NumFloat f -> return [BdIsAtom $ Float f]
            | c1OppGCmp n1 n2 -> return newOrdBounds
            | otherwise -> Left conflict

  uNumCmpAtom :: BdNumCmp -> Atom -> Either String [Bound]
  uNumCmpAtom (BdNumCmpCons o1 n1) a2 = do
    x <- case a2 of
      Int x -> return $ NumInt x
      Float x -> return $ NumFloat x
      _ -> Left conflict
    let r = case o1 of
          BdLT -> x < n1
          BdLE -> x <= n1
          BdGT -> x > n1
          BdGE -> x >= n1
    if r then return [b2] else Left conflict

  uStrMatchAtom :: BdStrMatch -> Atom -> Either String [Bound]
  uStrMatchAtom m1 a2 = case a2 of
    String s2 ->
      let r = case m1 of
            BdReMatch p1 -> reMatch s2 p1
            BdReNotMatch p1 -> reNotMatch s2 p1
       in if r then return [b2] else Left conflict
    _ -> Left conflict

  uTypeAtom :: BdType -> Atom -> Either String [Bound]
  uTypeAtom t1 a2 =
    let r = case a2 of
          Bool _ -> t1 == BdBool
          Int _ -> t1 `elem` [BdInt, BdNumber]
          Float _ -> t1 `elem` [BdFloat, BdNumber]
          String _ -> t1 == BdString
          _ -> False
     in if r then return [b2] else Left conflict

  conflict :: String
  conflict = printf "bounds %s and %s conflict" (show b1) (show b2)

  newOrdBounds :: [Bound]
  newOrdBounds = if d1 == Path.L then [b1, b2] else [b2, b1]

-- | unifyLeftOther is the sink of the unification process.
unifyLeftOther :: (TreeMonad s m) => UTree -> UTree -> m Bool
unifyLeftOther ut1@(UTree{utVal = t1, utDir = d1}) ut2@(UTree{utVal = t2}) =
  case (treeNode t1, treeNode t2) of
    (TNFunc _, _) -> do
      withDebugInfo $ \path _ ->
        logDebugStr $
          printf "unifyLeftOther starts, path: %s, %s, %s" (show path) (show ut1) (show ut2)
      r1 <- reduceFuncArg (Path.toBinOpSelector d1) t1
      withDebugInfo $ \path _ ->
        logDebugStr $ printf "unifyLeftOther, path: %s, %s is reduced to %s" (show path) (show t1) (show r1)

      case treeNode r1 of
        TNFunc _ -> return False
        _ -> unifyUTrees (ut1{utVal = r1}) ut2

    -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
    -- containing an atom or a bottom.
    (TNConstraint c1, _) -> do
      r <- unifyUTrees (ut1{utVal = mkNewTree (TNAtom $ cnsAtom c1)}) ut2
      na <- getTMTree
      putTMTree $ case treeNode na of
        TNBottom _ -> na
        _ -> t1
      return r
    -- According to the spec,
    -- A field value of the form r & v, where r evaluates to a reference cycle and v is a concrete value, evaluates to v.
    -- Unification is idempotent and unifying a value with itself ad infinitum, which is what the cycle represents,
    -- results in this value. Implementations should detect cycles of this kind, ignore r, and take v as the result of
    -- unification.
    -- We can just return the second value.
    (TNRefCycle _, _) -> do
      putTMTree t2
      return True
    _ -> putNotUnifiable
 where
  putNotUnifiable :: (TreeMonad s m) => m Bool
  putNotUnifiable = mkNodeWithDir ut1 ut2 f >> return False
   where
    f :: (TreeMonad s m) => Tree -> Tree -> m ()
    f x y = putTMTree $ mkBottomTree $ printf "values not unifiable: L:\n%s, R:\n%s" (show x) (show y)

unifyLeftStruct :: (TreeMonad s m) => (Struct Tree, UTree) -> UTree -> m Bool
unifyLeftStruct (s1, ut1@(UTree{utDir = d1})) ut2@(UTree{utVal = t2, utDir = d2}) = case treeNode t2 of
  -- If either of the structs is embedded, closed struct restrictions are ignored.
  TNStruct s2 -> unifyStructs (utEmbedded ut1 || utEmbedded ut2) (d1, s1) (d2, s2)
  _ -> unifyLeftOther ut2 ut1

unifyStructs ::
  (TreeMonad s m) => Bool -> (Path.BinOpDirect, Struct Tree) -> (Path.BinOpDirect, Struct Tree) -> m Bool
unifyStructs isEitherEmbeded (Path.L, s1) (_, s2) = do
  lE1 <- checkPermittedLabels s1 isEitherEmbeded s2
  lE2 <- checkPermittedLabels s2 isEitherEmbeded s1
  case (lE1, lE2) of
    (Just b1, _) -> putTMTree b1
    (_, Just b2) -> putTMTree b2
    _ -> do
      let merged = nodesToStruct allStatics combinedPatterns combinedPendSubs
      withDebugInfo $ \path _ ->
        logDebugStr $ printf "unifyStructs: %s gets updated to tree:\n%s" (show path) (show merged)
      putTMTree merged
      -- in reduce, the new combined fields will be checked by the combined patterns.
      reduce
  return True
 where
  fields1 = stcSubs s1
  fields2 = stcSubs s2
  l1Set = Map.keysSet fields1
  l2Set = Map.keysSet fields2
  interKeysSet = Set.intersection l1Set l2Set
  disjKeysSet1 = Set.difference l1Set interKeysSet
  disjKeysSet2 = Set.difference l2Set interKeysSet
  combinedPendSubs = stcPendSubs s1 ++ stcPendSubs s2
  combinedPatterns = stcPatterns s1 ++ stcPatterns s2

  -- Returns the intersection fields of the two structs. The relative order of the fields is preserved.
  inter :: [(Path.StructSelector, StaticStructField Tree)]
  inter =
    fst $
      foldr
        ( \key (l, visited) ->
            let
              sf1 = fields1 Map.! key
              sf2 = fields2 Map.! key
              ua = mergeAttrs (ssfAttr sf1) (ssfAttr sf2)
              -- No original node exists yet
              f = mkBinaryOp AST.Unify unify (ssfField sf1) (ssfField sf2)
              field =
                StaticStructField
                  { ssfField = mkFuncTree f
                  , ssfAttr = ua
                  }
             in
              -- If the key is in the intersection set and not visited, we add the field to the list. This prevents same
              -- keys in second ordLabels from being added multiple times.
              if (key `Set.member` interKeysSet) && not (key `Set.member` visited)
                then ((key, field) : l, Set.insert key visited)
                else (l, visited)
        )
        -- first element is the pairs, the second element is the visited keys set.
        ([], Set.empty)
        (stcOrdLabels s1 ++ stcOrdLabels s2)

  -- select the fields in the struct that are in the keysSet.
  select :: Struct Tree -> Set.Set Path.StructSelector -> [(Path.StructSelector, StaticStructField Tree)]
  select s keysSet = [(key, stcSubs s Map.! key) | key <- stcOrdLabels s, key `Set.member` keysSet]

  allStatics :: [(Path.StructSelector, StaticStructField Tree)]
  allStatics = inter ++ select s1 disjKeysSet1 ++ select s2 disjKeysSet2

  nodesToStruct ::
    [(Path.StructSelector, StaticStructField Tree)] -> [PatternStructField Tree] -> [PendingStructElem Tree] -> Tree
  nodesToStruct nodes patterns pends =
    mkStructTree $
      Struct
        { stcOrdLabels = map fst nodes
        , stcSubs = Map.fromList nodes
        , stcPendSubs = pends
        , stcPatterns = patterns
        , stcClosed = stcClosed s1 || stcClosed s2
        }
unifyStructs isEitherEmbeded dt1@(Path.R, _) dt2 = unifyStructs isEitherEmbeded dt2 dt1

{- | Check if the new labels from the new struct are permitted based on the base struct.
The isNewEmbedded flag indicates whether the new struct is embedded in the base struct.
-}
checkPermittedLabels :: (TreeMonad s m) => Struct Tree -> Bool -> Struct Tree -> m (Maybe Tree)
checkPermittedLabels base isNewEmbedded new =
  -- According to the spec, An embedded value of type struct is unified with the struct in which it is embedded, but
  -- disregarding the restrictions imposed by closed structs.
  if not (stcClosed base) || isNewEmbedded
    then return Nothing
    else do
      let
        baseLabels = Set.fromList $ stcOrdLabels base
        basePatterns = map psfPattern (stcPatterns base)
        newLabels = Set.fromList $ stcOrdLabels new
        diff = Set.difference newLabels baseLabels

      -- If the new struct has new labels, we need to check if they are in the field patterns of the base struct.
      res <-
        mapM
          ( \sel -> case sel of
              StringSelector s -> do
                -- foldM only returns a non-bottom value when the new label is in the patterns.
                r <-
                  foldM
                    ( \iacc (i, pat) ->
                        if maybe False isTreeBottom iacc
                          then return iacc
                          else do
                            inDiscardSubTM
                              (StructSelector (PatternSelector i))
                              ( mkFuncTree $
                                  mkBinaryOp AST.Unify unify (mkAtomTree $ String s) (mkNewTree $ TNBounds pat)
                              )
                              (reduce >> Just <$> getTMTree)
                    )
                    Nothing
                    (zip [0 ..] basePatterns)

                return (sel, r)
              _ -> throwError $ printf "unexpected selector: %s" (show sel)
          )
          (Set.toList diff)

      logDebugStr $
        printf "checkPermittedLabels: isNewEmbedde: %s, diff: %s, r: %s" (show isNewEmbedded) (show diff) (show res)

      -- A field is only disallowed if its unified value is a bottom.
      let disallowed = map fst $ filter (maybe True isTreeBottom . snd) res

      -- When no new labels or all new labels are in the patterns, we return the new labels.
      if null disallowed
        then return Nothing
        else return . Just $ mkBottomTree $ printf "fields: %s are not allowed" (show disallowed)

mkNodeWithDir ::
  (TreeMonad s m) => UTree -> UTree -> (Tree -> Tree -> m ()) -> m ()
mkNodeWithDir (UTree{utVal = t1, utDir = d1}) (UTree{utVal = t2}) f = case d1 of
  Path.L -> f t1 t2
  Path.R -> f t2 t1

unifyLeftDisj :: (TreeMonad s m) => (Disj Tree, UTree) -> UTree -> m Bool
unifyLeftDisj
  (dj1, ut1@(UTree{utDir = d1, utEmbedded = isEmbedded1}))
  ut2@( UTree
          { utVal = t2
          , utDir = d2
          , utEmbedded = isEmbedded2
          }
        ) = do
    case treeNode t2 of
      TNFunc _ -> unifyLeftOther ut2 ut1
      TNConstraint _ -> unifyLeftOther ut2 ut1
      TNRefCycle _ -> unifyLeftOther ut2 ut1
      -- If the left disj is embedded in the right struct and there is no fields and no pending dynamic fields, we can
      -- immediately put the disj into the tree without worrying any future new fields. This is what CUE currently
      -- does.
      TNStruct s2
        | utEmbedded ut1 && hasEmptyFields s2 -> putTMTree (utVal ut1) >> return True
      TNDisj dj2 -> case (dj1, dj2) of
        -- this is U0 rule, <v1> & <v2> => <v1&v2>
        (Disj{dsjDefault = Nothing, dsjDisjuncts = ds1}, Disj{dsjDefault = Nothing, dsjDisjuncts = ds2}) -> do
          ds <- mapM (`oneToMany` (d2, isEmbedded2, ds2)) (map (\x -> (d1, isEmbedded1, x)) ds1)
          treeFromNodes Nothing ds >>= putTMTree
          return True
        -- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
        (Disj{dsjDefault = Just df1, dsjDisjuncts = ds1}, Disj{dsjDefault = Nothing, dsjDisjuncts = ds2}) -> do
          logDebugStr $ printf "unifyLeftDisj: U1, df1: %s, ds1: %s, df2: N, ds2: %s" (show df1) (show ds1) (show ds2)
          dfs <- oneToMany (d1, isEmbedded1, df1) (d2, isEmbedded2, ds2)
          df <- treeFromNodes Nothing [dfs]
          dss <- manyToMany (d1, isEmbedded1, ds1) (d2, isEmbedded2, ds2)
          treeFromNodes (Just df) dss >>= putTMTree
          return True
        -- this is also the U1 rule.
        (Disj{dsjDefault = Nothing}, Disj{}) -> unifyLeftDisj (dj2, ut2) ut1
        -- this is U2 rule, <v1,d1> & <v2,d2> => <v1&v2,d1&d2>
        (Disj{dsjDefault = Just df1, dsjDisjuncts = ds1}, Disj{dsjDefault = Just df2, dsjDisjuncts = ds2}) -> do
          withDebugInfo $ \path _ ->
            logDebugStr $
              printf
                "unifyLeftDisj: path: %s, U2, d1:%s, df1: %s, ds1: %s, df2: %s, ds2: %s"
                (show path)
                (show d1)
                (show df1)
                (show ds1)
                (show df2)
                (show ds2)
          df <- unifyUTrees (ut1{utVal = df1}) (ut2{utVal = df2}) >> getTMTree
          dss <- manyToMany (d1, isEmbedded1, ds1) (d2, isEmbedded2, ds2)
          withDebugInfo $ \path _ ->
            logDebugStr $ printf "unifyLeftDisj: path: %s, U2, df: %s, dss: %s" (show path) (show df) (show dss)
          treeFromNodes (Just df) dss >>= putTMTree
          return True
      -- this is the case for a disjunction unified with a value.
      _ -> case dj1 of
        Disj{dsjDefault = Nothing, dsjDisjuncts = ds1} -> do
          ds2 <- oneToMany (d2, isEmbedded2, t2) (d1, isEmbedded1, ds1)
          treeFromNodes Nothing [ds2] >>= putTMTree
          return True
        Disj{dsjDefault = Just df1, dsjDisjuncts = ds1} -> do
          logDebugStr $
            printf "unifyLeftDisj: U1, unify with atom %s, disj: (df: %s, ds: %s)" (show t2) (show df1) (show ds1)
          df2 <- unifyUTrees (ut1{utVal = df1}) ut2 >> getTMTree
          ds2 <- oneToMany (d2, isEmbedded2, t2) (d1, isEmbedded1, ds1)
          logDebugStr $ printf "unifyLeftDisj: U1, df2: %s, ds2: %s" (show df2) (show ds2)
          r <- treeFromNodes (Just df2) [ds2]
          logDebugStr $ printf "unifyLeftDisj: U1, result: %s" (show r)
          putTMTree r
          return True
   where
    -- Note: isEmbedded is still required. Think about the following values,
    -- {x: 42} & (close({}) | int) // error because close({}) is not embedded.
    -- {x: 42, (close({}) | int)} // ok because close({}) is embedded.
    oneToMany :: (TreeMonad s m) => (Path.BinOpDirect, Bool, Tree) -> (Path.BinOpDirect, Bool, [Tree]) -> m [Tree]
    oneToMany (ld1, em1, node) (ld2, em2, ts) =
      let f x y = unifyUTrees (UTree x ld1 em1) (UTree y ld2 em2) >> getTMTree
       in mapM (`f` node) ts

    manyToMany :: (TreeMonad s m) => (Path.BinOpDirect, Bool, [Tree]) -> (Path.BinOpDirect, Bool, [Tree]) -> m [[Tree]]
    manyToMany (ld1, em1, ts1) (ld2, em2, ts2) =
      if ld1 == Path.R
        then mapM (\y -> oneToMany (ld2, em2, y) (ld1, em1, ts1)) ts2
        else mapM (\x -> oneToMany (ld1, em1, x) (ld2, em2, ts2)) ts1

treeFromNodes :: (MonadError String m) => Maybe Tree -> [[Tree]] -> m Tree
treeFromNodes dfM ds = case (excludeBottomM dfM, concatDedupNonBottoms ds) of
  (_, []) -> throwError "empty disjuncts"
  (Nothing, [_d]) -> return $ mkNewTree (treeNode _d)
  (Nothing, _ds) ->
    let
      node = TNDisj $ Disj{dsjDefault = Nothing, dsjDisjuncts = _ds}
     in
      return $ mkNewTree node
  (_df, _ds) ->
    let
      node = TNDisj $ Disj{dsjDefault = _df, dsjDisjuncts = _ds}
     in
      return $ mkNewTree node
 where
  -- concat and dedup the non-bottom disjuncts
  concatDedupNonBottoms :: [[Tree]] -> [Tree]
  concatDedupNonBottoms xs =
    dedup $
      concatMap (filter (not . isTreeBottom)) xs

  excludeBottomM :: Maybe Tree -> Maybe Tree
  excludeBottomM = maybe Nothing (\x -> if isTreeBottom x then Nothing else Just x)

  dedup :: [Tree] -> [Tree]
  dedup = foldr (\y acc -> if y `elem` acc then acc else y : acc) []

-- funcApplier creates a new function tree for the original function with the arguments applied.
funcApplier :: (MonadError String m) => Tree -> [Tree] -> m Tree
funcApplier t args = case treeNode t of
  TNFunc fn ->
    return $
      mkFuncTree $
        ( mkStubFunc $ \_ -> do
            putTMTree . mkFuncTree $
              fn
                { fncArgs = args
                }
            return True
        )
          { fncName = "funcApplier"
          }
  _ -> throwError $ printf "%s is not a function" (show t)

-- built-in functions
builtinFuncTable :: [(String, Tree)]
builtinFuncTable =
  [
    ( "close"
    , mkFuncTree $
        (mkStubFunc closeStruct)
          { fncName = "close"
          , fncArgs = [mkNewTree TNTop]
          }
    )
  ]

closeStruct :: (TreeMonad s m) => [Tree] -> m Bool
closeStruct args
  | length args /= 1 = throwError $ printf "expected 1 argument, got %d" (length args)
  | otherwise = do
      let a = head args
      r <- reduceFuncArg unaryOpSelector a
      case treeNode r of
        TNBottom _ -> putTMTree r >> return True
        TNStruct s -> do
          let closed = s{stcClosed = True}
          putTMTree $ mkStructTree closed
          return True
        TNFunc _ -> return False
        _ -> return False
