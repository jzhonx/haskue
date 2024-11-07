{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Reduction where

import qualified AST
import Control.Monad (foldM, forM, void, when)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (ask)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust, isNothing)
import qualified Data.Set as Set
import Path
import Ref
import Text.Printf (printf)
import Util
import Value.Tree

setOrigNodes :: (TreeMonad s m) => m ()
setOrigNodes = traverseTM $ withTree $ \t ->
  when (isNothing (treeOrig t)) $ putTMTree t{treeOrig = Just t}

reduce :: (TreeMonad s m) => m ()
reduce = do
  dumpEntireTree "reduce start"

  origT <- getTMTree
  withTree $ \t -> case treeNode t of
    TNFunc fn -> reduceFunc fn
    TNStruct struct -> reduceStruct struct
    TNList _ -> traverseSub reduce
    TNDisj _ -> traverseSub reduce
    _ -> return ()

  withTree $ \t -> do
    let nt = setOrig t origT
    putTMTree $ nt{treeEvaled = True}

  path <- getTMAbsPath
  withTree $ \t -> tryPopulateRef t reduceFunc

  logDebugStr $ printf "reduce: path: %s, done" (show path)
  dumpEntireTree "reduce done"

-- Evaluate tree nodes

{- | Reduce the function.
 - Function reduction is a top-down process, unlike other languages where the arguments are evaluated first.
Function call convention:
1. The result of a function is stored in the fncRes.
2. If the result can be used to replace the function itself, then the function is replaced by the result.
3. Otherwise, the function is kept.
-}
reduceFunc :: (TreeMonad s m) => Func Tree -> m ()
reduceFunc fn = do
  void $ callFunc >>= handleFuncRes

  withDebugInfo $ \path t ->
    logDebugStr $
      printf
        "reduceFunc: path: %s, function %s reduced to:\n%s"
        (show path)
        (show $ fncName fn)
        (show t)

-- Evaluate the sub node of the tree. The node must be a function.
-- Notice that if the argument is a function and the result of the function, such as struct or disjunction, is not
-- reducible, the result is still returned because the parent function needs to be evaluated.
reduceFuncArg :: (TreeMonad s m) => Selector -> Tree -> Bool -> m Tree
reduceFuncArg sel sub mustAtom = withTree $ \t -> do
  withDebugInfo $ \path _ ->
    logDebugStr $ printf "reduceFuncArg: path: %s, start reduction %s" (show path) (show sub)
  if isTreeFunc t
    then do
      res <-
        inSubTM
          sel
          sub
          ( withTree $ \x -> case treeNode x of
              TNFunc _ -> do
                rM <- callFunc
                return $ getFuncRes x rM
              _ -> reduce >> getTMTree
          )
      withDebugInfo $ \path _ ->
        logDebugStr $ printf "reduceFuncArg: path: %s, %s is reduced to:\n%s" (show path) (show sub) (show res)
      -- return $ getFuncResOrTree mustAtom res getFunc
      return res
    else throwError "reduceFuncArg: node is not a function"
 where
  -- Get the result of the function. If the result is not found, return the original tree.
  -- If the require Atom is true, then the result must be an atom. Otherwise, the function itself is returned.
  getFuncRes :: Tree -> Maybe Tree -> Tree
  getFuncRes ft =
    maybe
      ft
      ( \res ->
          if
            -- If the result is ref cycle tail, then the function must handle the tail to find the cycle head.
            | mustAtom && (treeHasAtom res || isTreeBottom res || isTreeRefCycleTail res) -> res
            -- The result of the function is not an atom while an atom is required. The function itself is returned to
            -- represent incompleteness.
            | mustAtom -> ft
            | otherwise -> res
      )

reduceStruct :: forall s m. (TreeMonad s m) => Struct Tree -> m ()
reduceStruct origStruct = do
  delIdxes <- do
    mapM_ (reduceStaticSF . fst) (Map.toList . stcSubs $ origStruct)
    mapM_ reducePattern (zip (map PatternSelector [0 ..]) (stcPatterns origStruct))
    foldM reducePendSE [] (zip (map PendingSelector [0 ..]) (stcPendSubs origStruct))

  whenStruct () $ \struct -> do
    let newStruct = mk struct{stcPendSubs = [pse | (i, pse) <- zip [0 ..] (stcPendSubs struct), i `notElem` delIdxes]}
    withDebugInfo $ \path _ ->
      logDebugStr $ printf "reduceStruct: path: %s, new struct: %s" (show path) (show newStruct)
    putTMTree newStruct
 where
  mk = mkNewTree . TNStruct

whenStruct :: (TreeMonad s m) => a -> (Struct Tree -> m a) -> m a
whenStruct a f = do
  t <- getTMTree
  case treeNode t of
    TNBottom _ -> return a
    TNStruct struct -> f struct
    _ -> do
      putTMTree $ mkBottomTree "not a struct"
      return a

mustStruct :: (TreeMonad s m) => (Struct Tree -> m a) -> m a
mustStruct f = withTree $ \t -> case treeNode t of
  TNStruct struct -> f struct
  _ -> throwError $ printf "mustStruct: %s is not a struct" (show t)

reduceStaticSF :: (TreeMonad s m) => StructSelector -> m ()
reduceStaticSF sel = whenStruct () $ \struct ->
  inSubTM (StructSelector sel) (ssfField (stcSubs struct Map.! sel)) reduce

reducePattern :: (TreeMonad s m) => (StructSelector, PatternStructField Tree) -> m ()
reducePattern (sel, psf) = whenStruct () $ \_ -> inSubTM (StructSelector sel) (psfValue psf) reduce

reducePendSE :: (TreeMonad s m) => [Int] -> (StructSelector, PendingStructElem Tree) -> m [Int]
reducePendSE idxes (sel, pse) = do
  case (sel, pse) of
    (PendingSelector i, DynamicField dsf) -> do
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
          newSF <- mustStruct $ \struct ->
            return $ dynToStaticField dsf (stcSubs struct Map.!? StringSelector s)

          let sSel = StructSelector $ StringSelector s
          pushTMSub sSel (ssfField newSF)
          mergedT <- reduce >> getTMTree
          -- do not use propUpTCSel here because the field might not be in the original struct.
          discardTMAndPop
          -- TODO: use whenStruct because mergedT could be a bottom.
          nstruct <- mustStruct $ \struct ->
            return $ mkNewTree (TNStruct $ addStatic s (newSF{ssfField = mergedT}) struct)
          putTMTree nstruct
          return (i : idxes)

        -- TODO: pending label
        _ -> putTMTree (mkBottomTree "selector can only be a string") >> return idxes
    (PendingSelector i, PatternField pattern val) -> do
      -- evaluate the pattern.
      evaledPattern <- inSubTM (StructSelector sel) pattern (reduce >> getTMTree)
      withDebugInfo $ \path _ ->
        logDebugStr $
          printf
            "reducePendSE: path: %s, pattern is evaluated to %s"
            (show path)
            (show evaledPattern)
      case treeNode evaledPattern of
        TNBounds bds ->
          if null (bdsList bds)
            then putTMTree (mkBottomTree "patterns must be non-empty") >> return idxes
            else do
              pushTMSub (StructSelector sel) val
              defaultVal <- reduce >> getTMTree
              -- apply the pattern to all existing fields.
              -- TODO: apply the pattern to filtered fields.
              nodes <- mustStruct $ \struct ->
                return $
                  [ mkNewTree . TNFunc $
                    mkBinaryOp AST.Unify unify (ssfField n) defaultVal
                  | n <- Map.elems (stcSubs struct)
                  ]
              mapM_ (\x -> whenNotBottom () (putTMTree x >> reduce)) nodes
              -- r <- foldM (\acc n -> whenNotBottom acc (reduce n)) defaultVal nodes
              whenNotBottom idxes $ do
                newStruct <- mustStruct $ \struct ->
                  return $ mkNewTree . TNStruct $ addPattern (PatternStructField bds defaultVal) struct
                discardTMAndPut newStruct
                return (i : idxes)
        _ ->
          putTMTree (mkBottomTree (printf "pattern should be bounds, but is %s" (show evaledPattern)))
            >> return idxes
    _ -> throwError "evalStructField: invalid selector field combination"
 where
  dynToStaticField ::
    DynamicStructField Tree ->
    Maybe (StaticStructField Tree) ->
    StaticStructField Tree
  dynToStaticField dsf sfM = case sfM of
    Just sf ->
      StaticStructField
        { ssfField = mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify (ssfField sf) (dsfValue dsf))
        , ssfAttr = mergeAttrs (ssfAttr sf) (dsfAttr dsf)
        }
    Nothing ->
      StaticStructField
        { ssfField = dsfValue dsf
        , ssfAttr = dsfAttr dsf
        }

  addStatic :: String -> StaticStructField Tree -> Struct Tree -> Struct Tree
  addStatic s sf x =
    x
      { stcSubs = Map.insert (StringSelector s) sf (stcSubs x)
      , stcOrdLabels =
          if StringSelector s `elem` stcOrdLabels x
            then stcOrdLabels x
            else stcOrdLabels x ++ [StringSelector s]
      }

  addPattern :: PatternStructField Tree -> Struct Tree -> Struct Tree
  addPattern psf x = x{stcPatterns = stcPatterns x ++ [psf]}

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
          , fncExprGen = return $ AST.ExprUnaryExpr ue
          }
  _ ->
    (mkStubFunc (index ue))
      { fncName = "index"
      , fncType = IndexFunc
      , fncArgs = [treeArg, selArg]
      , fncExprGen = return $ AST.ExprUnaryExpr ue
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
          res <- reduceFuncArg (FuncSelector $ FuncArgSelector 0) t False
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
  return $
    ( mkStubFunc
        ( \_ -> do
            ok <- deref tp
            when ok $ withTree $ \t -> putTMTree $ t{treeEvaled = False}
            return ok
        )
    )
      { fncName = printf "&%s" (show tp)
      , fncType = RefFunc
      , fncArgs = args
      , fncExprGen = return $ AST.ExprUnaryExpr ue
      }

validateCnstrs :: (TreeMonad s m) => m ()
validateCnstrs = do
  logDebugStr $ printf "validateCnstrs: start"

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
validateCnstr c = withTree $ \t -> do
  withDebugInfo $ \path _ -> do
    tc <- getTMCursor
    logDebugStr $ printf "evalConstraint: path: %s, constraint unify tc:\n%s" (show path) (show tc)

  let
    origAtomT = mkAtomVTree $ cnsAtom c
    orig = fromJust $ treeOrig t

  -- run the function in a sub context.
  pushTMSub unaryOpSelector orig
  x <- reduce >> getTMTree
  discardTMAndPop

  when (isTreeAtom x) $ do
    when (x /= origAtomT) $
      throwError $
        printf
          "validateCnstr: constraint not satisfied, %s != %s"
          (show x)
          (show origAtomT)
    putTMTree origAtomT

dispUnaryFunc :: (TreeMonad s m) => AST.UnaryOp -> Tree -> m Bool
dispUnaryFunc op _t = do
  t <- reduceFuncArg unaryOpSelector _t True
  case treeNode t of
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
    -- The unary op is operating on a non-atom.
    TNFunc _ -> return False
    TNRefCycle (RefCycleTail _) -> putTMTree t >> return True
    _ -> putConflict
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

  t1 <- reduceFuncArg (toBinOpSelector d1) _t1 True
  t2 <- reduceFuncArg (toBinOpSelector d2) _t2 True

  withDebugInfo $ \path _ ->
    logDebugStr $
      printf "regBinDir: path: %s, reduced args, %s: %s with %s: %s" (show path) (show d1) (show t1) (show d2) (show t2)

  case (treeNode t1, treeNode t2) of
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
    (TNFunc fn, _)
      -- unresolved reference
      | isFuncRef fn -> return False
      | otherwise -> return False
    (TNRefCycle _, _) -> reduceOrDelay
    (TNConstraint c, _) -> do
      na <- regBinDir op (d1, mkNewTree (TNAtom $ cnsAtom c)) (d2, t2) >> getTMTree
      case treeNode na of
        TNAtom atom -> putTMTree (mkNewTree (TNConstraint $ updateCnstrAtom atom c)) >> return True
        _ -> undefined
    _ -> putTMTree (mkBottomTree mismatchErr) >> return True
 where
  -- reduceOrDelay tries to reduce the left side of the binary operation. If it is not possible to reduce it, it
  -- returns a delayed reduction.
  reduceOrDelay :: (TreeMonad s m) => m Bool
  reduceOrDelay = do
    logDebugStr $ printf "reduceOrDelay: %s: %s, %s: %s" (show d1) (show t1) (show d2) (show t2)
    et1 <- reduceFuncArg (toBinOpSelector d1) t1 True
    procLeftOtherRes et1

  procLeftOtherRes :: (TreeMonad s m) => Tree -> m Bool
  procLeftOtherRes x = case treeNode x of
    TNAtom a1 -> regBinLeftAtom op (d1, a1, x) (d2, t2)
    TNDisj dj1 -> regBinLeftDisj op (d1, dj1, x) (d2, t2)
    TNStruct s1 -> regBinLeftStruct op (d1, s1, x) (d2, t2)
    TNList _ -> undefined
    TNConstraint _ -> regBinLeftOther op (d1, x) (d2, t2)
    _ -> do
      withDebugInfo $ \path _ ->
        logDebugStr $ printf "regBinLeftOther: path: %s, %s is incomplete, delaying" (show path) (show x)
      return False

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

unify :: (TreeMonad s m) => Tree -> Tree -> m Bool
unify = unifyToTree

unifyToTree :: (TreeMonad s m) => Tree -> Tree -> m Bool
unifyToTree t1 t2 = unifyWithDir (Path.L, t1) (Path.R, t2)

-- If there exists a struct beneath the current node, we need to be careful about the references in the struct. We
-- should not further reduce the values of the references.
-- For example, {a: b + 100, b: a - 100} & {b: 50}. The "b" in the first struct will have to see the atom 50.
unifyWithDir :: (TreeMonad s m) => (Path.BinOpDirect, Tree) -> (Path.BinOpDirect, Tree) -> m Bool
unifyWithDir dt1@(d1, t1) dt2@(d2, t2) = do
  withDebugInfo $ \path _ ->
    logDebugStr $
      printf
        ("unifying start, path: %s:, %s:\n%s" ++ "\n" ++ "with %s:\n%s")
        (show path)
        (show d1)
        (show t1)
        (show d2)
        (show t2)

  r <- case (treeNode t1, treeNode t2) of
    (TNTop, _) -> putTree t2
    (_, TNTop) -> putTree t1
    (TNBottom _, _) -> putTree t1
    (_, TNBottom _) -> putTree t2
    (TNAtom l1, _) -> unifyLeftAtom (d1, l1, t1) dt2
    -- Below is the earliest time to create a constraint
    (_, TNAtom l2) -> unifyLeftAtom (d2, l2, t2) dt1
    (TNDisj dj1, _) -> unifyLeftDisj (d1, dj1, t1) (d2, t2)
    (TNStruct s1, _) -> unifyLeftStruct (d1, s1, t1) dt2
    (TNBounds b1, _) -> unifyLeftBound (d1, b1, t1) dt2
    _ -> unifyLeftOther dt1 dt2

  withDebugInfo $ \path res ->
    logDebugStr $
      printf
        "unifying done, path: %s, %s: %s, with %s: %s, res: %s"
        (show path)
        (show d1)
        (show t1)
        (show d2)
        (show t2)
        (show res)
  return r
 where
  putTree :: (TreeMonad s m) => Tree -> m Bool
  putTree x = putTMTree x >> return True

{- |
parTC points to the bin op node.
-}
unifyLeftAtom :: (TreeMonad s m) => (Path.BinOpDirect, AtomV, Tree) -> (Path.BinOpDirect, Tree) -> m Bool
unifyLeftAtom (d1, l1, t1) dt2@(d2, t2) = do
  case (amvAtom l1, treeNode t2) of
    (String x, TNAtom s) -> case amvAtom s of
      String y -> putTree $ if x == y then TNAtom l1 else amismatch x y
      _ -> notUnifiable dt1 dt2
    (Int x, TNAtom s) -> case amvAtom s of
      Int y -> putTree $ if x == y then TNAtom l1 else amismatch x y
      _ -> notUnifiable dt1 dt2
    (Bool x, TNAtom s) -> case amvAtom s of
      Bool y -> putTree $ if x == y then TNAtom l1 else amismatch x y
      _ -> notUnifiable dt1 dt2
    (Float x, TNAtom s) -> case amvAtom s of
      Float y -> putTree $ if x == y then TNAtom l1 else amismatch x y
      _ -> notUnifiable dt1 dt2
    (Null, TNAtom s) -> case amvAtom s of
      Null -> putTree $ TNAtom l1
      _ -> notUnifiable dt1 dt2
    (_, TNBounds b) -> do
      logDebugStr $ printf "unifyAtomBounds: %s, %s" (show t1) (show t2)
      putTMTree $ unifyAtomBounds (d1, amvAtom l1) (d2, bdsList b)
      return True
    (_, TNConstraint c) ->
      if l1 == cnsAtom c
        then putCnstr (d2, cnsAtom c) dt1 >> return True
        else do
          putTMTree $
            mkBottomTree $
              printf "values mismatch: %s != %s" (show l1) (show $ cnsAtom c)
          return True
    (_, TNDisj dj2) -> do
      logDebugStr $ printf "unifyLeftAtom: TNDisj %s, %s" (show t2) (show t1)
      unifyLeftDisj (d2, dj2, t2) (d1, t1)
    (_, TNFunc fn2) -> case fncType fn2 of
      -- Notice: Unifying an atom with a marked disjunction will not get the same atom. So we do not create a
      -- constraint. Another way is to add a field in Constraint to store whether the constraint is created from a
      -- marked disjunction.
      DisjFunc -> unifyLeftOther dt2 dt1
      _ -> procOther
    (_, TNRefCycle _) -> procOther
    _ -> notUnifiable dt1 dt2
 where
  dt1 = (d1, t1)

  putTree :: (TreeMonad s m) => TreeNode Tree -> m Bool
  putTree n = do
    withTree $ \t -> putTMTree $ setTN t n
    return True

  amismatch :: (Show a) => a -> a -> TreeNode Tree
  amismatch x y = TNBottom . Bottom $ printf "values mismatch: %s != %s" (show x) (show y)

  procOther :: (TreeMonad s m) => m Bool
  procOther = do
    Config{cfCreateCnstr = cc} <- ask
    if cc
      then putCnstr (d1, l1) dt2 >> return True
      else unifyLeftOther dt2 dt1

  putCnstr :: (TreeMonad s m) => (Path.BinOpDirect, AtomV) -> (Path.BinOpDirect, Tree) -> m ()
  putCnstr (_, a1) (_, _) = withTree $ \t -> putTMTree $ mkCnstrTree a1 t

unifyLeftBound :: (TreeMonad s m) => (Path.BinOpDirect, Bounds, Tree) -> (Path.BinOpDirect, Tree) -> m Bool
unifyLeftBound (d1, b1, t1) (d2, t2) = case treeNode t2 of
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
  TNFunc _ -> unifyLeftOther (d2, t2) (d1, t1)
  TNConstraint _ -> unifyLeftOther (d2, t2) (d1, t1)
  TNRefCycle _ -> unifyLeftOther (d2, t2) (d1, t1)
  TNDisj _ -> unifyLeftOther (d2, t2) (d1, t1)
  _ -> notUnifiable (d1, t1) (d2, t2)

unifyAtomBounds :: (Path.BinOpDirect, Atom) -> (Path.BinOpDirect, [Bound]) -> Tree
unifyAtomBounds (d1, a1) (_, bs) =
  let
    cs = map withBound bs
    ta1 = mkAtomTree a1
   in
    foldl (\_ x -> if x == ta1 then ta1 else x) (mkAtomTree a1) cs
 where
  withBound :: Bound -> Tree
  withBound b =
    let
      r = unifyBounds (d1, BdIsAtom a1) (Path.R, b)
     in
      case r of
        Left s -> mkBottomTree s
        Right v -> case v of
          [x] -> case x of
            BdIsAtom a -> mkNewTree $ TNAtom $ AtomV a
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
    let bsMap = Map.fromListWith (\x y -> x ++ y) (map (\b -> (bdRep b, [b])) (concat bss))
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
          Int _ -> BdInt `elem` [BdInt, BdNumber]
          Float _ -> BdFloat `elem` [BdFloat, BdNumber]
          String _ -> t1 == BdString
          _ -> False
     in if r then return [b2] else Left conflict

  conflict :: String
  conflict = printf "bounds %s and %s conflict" (show b1) (show b2)

  newOrdBounds :: [Bound]
  newOrdBounds = if d1 == Path.L then [b1, b2] else [b2, b1]

unifyLeftOther :: (TreeMonad s m) => (Path.BinOpDirect, Tree) -> (Path.BinOpDirect, Tree) -> m Bool
unifyLeftOther dt1@(d1, t1) dt2@(d2, t2) = case (treeNode t1, treeNode t2) of
  (TNFunc fn1, _) -> do
    withDebugInfo $ \path _ ->
      logDebugStr $
        printf
          "unifyLeftOther starts, path: %s, %s: %s, %s: %s"
          (show path)
          (show d1)
          (show t1)
          (show d2)
          (show t2)
    r1 <- reduceFuncArg (Path.toBinOpSelector d1) t1 False
    withDebugInfo $ \path _ ->
      logDebugStr $ printf "unifyLeftOther, path: %s, %s is reduced to %s" (show path) (show t1) (show r1)

    case treeNode r1 of
      TNFunc xfn
        -- If the function type changes from the reference to regular, we need to evaluate the regular function.
        -- Otherwise, leave the unification.
        | isFuncRef fn1 && isFuncRef xfn
        , not (isFuncRef fn1) && not (isFuncRef xfn) ->
            return False
      _ -> unifyWithDir (d1, r1) dt2

  -- For the constraint, unifying the constraint with a value will always lead to either the constraint, which
  -- containing an atom or a bottom.
  (TNConstraint c1, _) -> do
    r <- unifyWithDir (d1, mkNewTree (TNAtom $ cnsAtom c1)) dt2
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
  _ -> notUnifiable dt1 dt2

unifyLeftStruct :: (TreeMonad s m) => (Path.BinOpDirect, Struct Tree, Tree) -> (Path.BinOpDirect, Tree) -> m Bool
unifyLeftStruct (d1, s1, t1) (d2, t2) = case treeNode t2 of
  TNStruct s2 -> unifyStructs (d1, s1) (d2, s2)
  _ -> unifyLeftOther (d2, t2) (d1, t1)

unifyStructs :: (TreeMonad s m) => (Path.BinOpDirect, Struct Tree) -> (Path.BinOpDirect, Struct Tree) -> m Bool
unifyStructs (_, s1) (_, s2) = do
  let merged = nodesToStruct allStatics combinedPatterns combinedPendSubs
  withDebugInfo $ \path _ ->
    logDebugStr $ printf "unifyStructs: %s gets updated to tree:\n%s" (show path) (show merged)
  putTMTree merged
  reduce
  return True
 where
  fields1 = stcSubs s1
  fields2 = stcSubs s2
  l1Set = Map.keysSet fields1
  l2Set = Map.keysSet fields2
  interKeys = Set.intersection l1Set l2Set
  disjKeys1 = Set.difference l1Set interKeys
  disjKeys2 = Set.difference l2Set interKeys
  combinedPendSubs = stcPendSubs s1 ++ stcPendSubs s2
  combinedPatterns = stcPatterns s1 ++ stcPatterns s2

  inter :: [(Path.StructSelector, StaticStructField Tree)]
  inter =
    Set.foldr
      ( \key acc ->
          let sf1 = fields1 Map.! key
              sf2 = fields2 Map.! key
              ua = mergeAttrs (ssfAttr sf1) (ssfAttr sf2)
              -- No original node exists yet
              unifyOp = mkNewTree (TNFunc $ mkBinaryOp AST.Unify unify (ssfField sf1) (ssfField sf2))
           in ( key
              , StaticStructField
                  { ssfField = unifyOp
                  , ssfAttr = ua
                  }
              )
                : acc
      )
      []
      interKeys

  select :: Struct Tree -> Set.Set Path.StructSelector -> [(Path.StructSelector, StaticStructField Tree)]
  select s keys = map (\key -> (key, stcSubs s Map.! key)) (Set.toList keys)

  allStatics :: [(Path.StructSelector, StaticStructField Tree)]
  allStatics = inter ++ select s1 disjKeys1 ++ select s2 disjKeys2

  nodesToStruct ::
    [(Path.StructSelector, StaticStructField Tree)] -> [PatternStructField Tree] -> [PendingStructElem Tree] -> Tree
  nodesToStruct nodes patterns pends =
    mkNewTree
      ( TNStruct $
          Struct
            { stcOrdLabels = map fst nodes
            , stcSubs = Map.fromList nodes
            , stcPendSubs = pends
            , stcPatterns = patterns
            }
      )

mkNodeWithDir ::
  (TreeMonad s m) => (Path.BinOpDirect, Tree) -> (Path.BinOpDirect, Tree) -> (Tree -> Tree -> m ()) -> m ()
mkNodeWithDir (d1, t1) (_, t2) f = case d1 of
  Path.L -> f t1 t2
  Path.R -> f t2 t1

notUnifiable :: (TreeMonad s m) => (Path.BinOpDirect, Tree) -> (Path.BinOpDirect, Tree) -> m Bool
notUnifiable dt1 dt2 = mkNodeWithDir dt1 dt2 f >> return False
 where
  f :: (TreeMonad s m) => Tree -> Tree -> m ()
  f x y = putTMTree $ mkBottomTree $ printf "values not unifiable: L:\n%s, R:\n%s" (show x) (show y)

unifyLeftDisj :: (TreeMonad s m) => (Path.BinOpDirect, Disj Tree, Tree) -> (Path.BinOpDirect, Tree) -> m Bool
unifyLeftDisj (d1, dj1, t1) (d2, t2) = do
  case treeNode t2 of
    TNFunc _ -> unifyLeftOther (d2, t2) (d1, t1)
    TNConstraint _ -> unifyLeftOther (d2, t2) (d1, t1)
    TNRefCycle _ -> unifyLeftOther (d2, t2) (d1, t1)
    TNDisj dj2 -> case (dj1, dj2) of
      -- this is U0 rule, <v1> & <v2> => <v1&v2>
      (Disj{dsjDefault = Nothing, dsjDisjuncts = ds1}, Disj{dsjDefault = Nothing, dsjDisjuncts = ds2}) -> do
        ds <- mapM (`oneToMany` (d2, ds2)) (map (\x -> (d1, x)) ds1)
        treeFromNodes Nothing ds >>= putTMTree
        return True
      -- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
      (Disj{dsjDefault = Just df1, dsjDisjuncts = ds1}, Disj{dsjDefault = Nothing, dsjDisjuncts = ds2}) -> do
        logDebugStr $ printf "unifyLeftDisj: U1, df1: %s, ds1: %s, df2: N, ds2: %s" (show df1) (show ds1) (show ds2)
        dfs <- oneToMany (d1, df1) (d2, ds2)
        df <- treeFromNodes Nothing [dfs]
        dss <- manyToMany (d1, ds1) (d2, ds2)
        treeFromNodes (Just df) dss >>= putTMTree
        return True
      -- this is also the U1 rule.
      (Disj{dsjDefault = Nothing}, Disj{}) -> unifyLeftDisj (d2, dj2, t2) (d1, t1)
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
        df <- unifyWithDir (d1, df1) (d2, df2) >> getTMTree
        dss <- manyToMany (d1, ds1) (d2, ds2)
        withDebugInfo $ \path _ ->
          logDebugStr $ printf "unifyLeftDisj: path: %s, U2, df: %s, dss: %s" (show path) (show df) (show dss)
        treeFromNodes (Just df) dss >>= putTMTree
        return True
    -- this is the case for a disjunction unified with a value.
    _ -> case dj1 of
      Disj{dsjDefault = Nothing, dsjDisjuncts = ds1} -> do
        ds2 <- oneToMany (d2, t2) (d1, ds1)
        treeFromNodes Nothing [ds2] >>= putTMTree
        return True
      Disj{dsjDefault = Just df1, dsjDisjuncts = ds1} -> do
        logDebugStr $ printf "unifyLeftDisj: U1, unify with atom %s, disj: (df: %s, ds: %s)" (show t2) (show df1) (show ds1)
        df2 <- unifyWithDir (d1, df1) (d2, t2) >> getTMTree
        ds2 <- oneToMany (d2, t2) (d1, ds1)
        logDebugStr $ printf "unifyLeftDisj: U1, df2: %s, ds2: %s" (show df2) (show ds2)
        r <- treeFromNodes (Just df2) [ds2]
        logDebugStr $ printf "unifyLeftDisj: U1, result: %s" (show r)
        putTMTree r
        return True
 where
  oneToMany :: (TreeMonad s m) => (Path.BinOpDirect, Tree) -> (Path.BinOpDirect, [Tree]) -> m [Tree]
  oneToMany (ld1, node) (ld2, ts) =
    let f x y = unifyWithDir (ld1, x) (ld2, y) >> getTMTree
     in mapM (`f` node) ts

  manyToMany :: (TreeMonad s m) => (Path.BinOpDirect, [Tree]) -> (Path.BinOpDirect, [Tree]) -> m [[Tree]]
  manyToMany (ld1, ts1) (ld2, ts2) =
    if ld1 == Path.R
      then mapM (\y -> oneToMany (ld2, y) (ld1, ts1)) ts2
      else mapM (\x -> oneToMany (ld1, x) (ld2, ts2)) ts1

treeFromNodes :: (MonadError String m) => Maybe Tree -> [[Tree]] -> m Tree
treeFromNodes dfM ds = case (excludeDefault dfM, concatExclude ds) of
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
  -- concat the disjuncts and exclude the disjuncts with Bottom values.
  concatExclude :: [[Tree]] -> [Tree]
  concatExclude xs =
    filter
      ( \x ->
          case treeNode x of
            TNBottom _ -> False
            _ -> True
      )
      (concat xs)

  excludeDefault :: Maybe Tree -> Maybe Tree
  excludeDefault Nothing = Nothing
  excludeDefault (Just x) = case treeNode x of
    TNBottom _ -> Nothing
    _ -> Just x
