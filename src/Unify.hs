{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unify (unify) where

import qualified AST
import           Control.Monad.Except (MonadError, throwError)
import qualified Data.Map.Strict      as Map
import qualified Data.Set             as Set
import           Text.Printf          (printf)
import           Value

unify :: (Runtime m) => Value -> Value -> m Value
unify v1@(Pending p1) v2@(Pending p2) =
  let temp1 = pvTemp p1
      temp2 = pvTemp p2
   in if
          | isValueStub temp1 && isValueStub temp2 -> delayBinaryOp AST.Unify unify p1 p2
          | isValueStub temp1 ->
              delayUnaryOp (AST.binaryOpCons AST.Unify (pvExpr p1) (pvExpr p2)) (`unify` v2) p1
          | isValueStub temp2 ->
              delayUnaryOp (AST.binaryOpCons AST.Unify (pvExpr p1) (pvExpr p2)) (unify v1) p2
          | otherwise -> do
              v <- unifyNonPends temp1 temp2
              delayIfTemp2 p1 p2 v
unify (Pending p1) v2 =
  let temp1 = pvTemp p1
   in if
          | isValueAtom v2 ->
              let c =
                    Constraint $
                      DelayConstraint
                        { dcPath = pvPath p1,
                          dcAtom = v2,
                          dcPend = p1,
                          dcUnify = unify
                        }
               in do
                    dump $ printf "unify: path: %s, creates a constraint: %s" (show $ pvPath p1) (show c)
                    return c
          | isValueStub temp1 -> do
              e2 <- vToE v2
              delayUnaryOp (AST.binaryOpCons AST.Unify (pvExpr p1) e2) (`unify` v2) p1
          | otherwise -> do
              v <- unifyNonPends temp1 v2
              delayIfLeftTemp p1 v v
unify v1 (Pending p2) =
  let temp2 = pvTemp p2
   in if
          | isValueAtom v1 ->
              let c =
                    Constraint $
                      DelayConstraint
                        { dcPath = pvPath p2,
                          dcAtom = v1,
                          dcPend = p2,
                          dcUnify = unify
                        }
               in do
                    dump $ printf "unify: path: %s, creates a constraint: %s" (show $ pvPath p2) (show c)
                    return c
          | isValueStub temp2 -> do
              e1 <- vToE v1
              delayUnaryOp (AST.binaryOpCons AST.Unify e1 (pvExpr p2)) (unify v1) p2
          | otherwise -> do
              v <- unifyNonPends v1 temp2
              delayIfRightTemp v p2 v
unify v1 v2 = unifyNonPends v1 v2

-- | If the left value of the unification is a pending value and contains a valid temp value, then depending on the
-- unification result of the temporary unified value, an atom or a new pending value is returned.
delayIfLeftTemp :: (Runtime m) => PendingValue -> Value -> Value -> m Value
delayIfLeftTemp pv v tun =
  if isValueAtom tun
    then return tun
    else do
      e <- vToE v
      delayUnaryOp (AST.binaryOpCons AST.Unify (pvExpr pv) e) (`unify` v) pv

-- | Similar to 'delayIfLeftTemp', but for the right value of the unification.
delayIfRightTemp :: (Runtime m) => Value -> PendingValue -> Value -> m Value
delayIfRightTemp v pv tun =
  if isValueAtom tun
    then return tun
    else do
      e <- vToE v
      delayUnaryOp (AST.binaryOpCons AST.Unify e (pvExpr pv)) (unify v) pv

delayIfTemp2 :: (Runtime m) => PendingValue -> PendingValue -> Value -> m Value
delayIfTemp2 pv1 pv2 temp =
  if isValueAtom temp
    then return temp
    else delayBinaryOp AST.Unify unify pv1 pv2

unifyNonPends :: (Runtime m) => Value -> Value -> m Value
unifyNonPends v1 v2 = case (v1, v2) of
  (Bottom _, _) -> return v1
  (Top, _) -> return v2
  (Stub, _) -> return v2
  (String x, String y) ->
    return $ if x == y then v1 else Bottom $ printf "strings mismatch: %s != %s" x y
  (Int x, Int y) ->
    return $ if x == y then v1 else Bottom $ printf "ints mismatch: %d != %d" x y
  (Bool x, Bool y) ->
    return $ if x == y then v1 else Bottom $ printf "bools mismatch: %s != %s" (show x) (show y)
  (Null, Null) -> return v1
  (Struct {}, Struct {}) -> unifyStructs v1 v2
  (Disjunction _ _, _) -> unifyDisjunctions v1 v2
  (_, Top) -> unify v2 v1
  (_, Stub) -> unify v2 v1
  (_, Bottom _) -> unify v2 v1
  (_, Disjunction _ _) -> unify v2 v1
  _ -> return $ Bottom $ printf "values not unifiable: %s, %s" (show v1) (show v2)

unifyStructs :: (Runtime m) => Value -> Value -> m Value
unifyStructs (Struct v1) (Struct v2) = do
  valList <- unifyIntersectionLabels
  let vs = sequence valList
  case vs of
    -- If any of the values is Bottom, then the whole struct is Bottom.
    Left (Bottom msg) -> return $ Bottom msg
    Left _ -> throwError "unifyVertices: impossible"
    Right vs' ->
      do
        let newEdges = Map.unions [disjointVertices1, disjointVertices2, Map.fromList vs']
        return $ fieldsToValue newEdges
  where
    (fields1, fields2) = (svFields v1, svFields v2)
    labels1Set = Map.keysSet fields1
    labels2Set = Map.keysSet fields2
    interLabels = Set.intersection labels1Set labels2Set
    disjointVertices1 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) fields1
    disjointVertices2 = Map.filterWithKey (\k _ -> Set.notMember k interLabels) fields2
    processUnified :: String -> Value -> Either Value (String, Value)
    processUnified key val = case val of
      Bottom _ -> Left val
      _        -> Right (key, val)
    unifyIntersectionLabels =
      sequence
        ( Set.foldr
            ( \key acc ->
                let valx = fields1 Map.! key
                    valy = fields2 Map.! key
                    unified = unify valx valy
                 in fmap (processUnified key) unified : acc
            )
            []
            interLabels
        )

    fieldsToValue :: Map.Map String Value -> Value
    fieldsToValue fds = Struct (StructValue (Map.keys fds) fds Set.empty Set.empty)
unifyStructs _ _ = throwError "unifyStructs: impossible"

unifyDisjunctions :: (Runtime m) => Value -> Value -> m Value
-- this is U0 rule, <v1> & <v2> => <v1&v2>
unifyDisjunctions (Disjunction [] ds1) (Disjunction [] ds2) = do
  ds <- mapM (`unifyValues` ds2) ds1
  disjunctionFromValues [] ds

-- this is U1 rule, <v1,d1> & <v2> => <v1&v2,d1&v2>
unifyDisjunctions (Disjunction df1 ds1) (Disjunction [] ds2) = do
  df <- mapM (`unifyValues` ds2) df1
  ds <- mapM (`unifyValues` ds2) ds1
  disjunctionFromValues df ds

-- this is also the U1 rule.
unifyDisjunctions d1@(Disjunction [] _) d2@(Disjunction _ _) = unifyDisjunctions d2 d1
-- this is U2 rule, <v1,d1> & <v2,d2> => <v1&v2,d1&d2>
unifyDisjunctions (Disjunction df1 ds1) (Disjunction df2 ds2) = do
  df <- mapM (`unifyValues` df2) df1
  ds <- mapM (`unifyValues` ds2) ds1
  disjunctionFromValues df ds

-- this is the case for a disjunction unified with a value.
unifyDisjunctions (Disjunction [] ds) val = do
  ds' <- unifyValues val ds
  disjunctionFromValues [] [ds']
unifyDisjunctions (Disjunction df ds) val = do
  df' <- unifyValues val df
  ds' <- unifyValues val ds
  disjunctionFromValues [df'] [ds']
unifyDisjunctions d1 d2 =
  throwError $ "unifyDisjunctions: impossible unification, d1: " ++ show d1 ++ ", d2: " ++ show d2

unifyValues :: (Runtime m) => Value -> [Value] -> m [Value]
unifyValues val = mapM (`unify` val)

disjunctionFromValues :: (MonadError String m) => [[Value]] -> [[Value]] -> m Value
disjunctionFromValues df ds = f (concatFilter df) (concatFilter ds)
  where
    concatFilter :: [[Value]] -> [Value]
    concatFilter xs = case filter (\x -> case x of Bottom _ -> False; _ -> True) (concat xs) of
      []  -> [Bottom "empty disjuncts"]
      xs' -> xs'
    f :: (MonadError String m) => [Value] -> [Value] -> m Value
    f [] []                 = emptyDisjunctError [] []
    f [Bottom _] [Bottom _] = return $ Bottom "empty disjuncts"
    f df' [Bottom _]        = return $ Disjunction [] df'
    f [Bottom _] ds'        = return $ Disjunction [] ds'
    f df' ds'               = return $ Disjunction df' ds'
    emptyDisjunctError :: (MonadError String m) => [Value] -> [Value] -> m Value
    emptyDisjunctError df' ds' =
      throwError $
        "disjunctionFromUnifyResult failed because of empty disjuncts, df: "
          ++ show df'
          ++ ", ds: "
          ++ show ds'
