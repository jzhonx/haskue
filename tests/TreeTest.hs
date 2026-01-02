{-# LANGUAGE FlexibleContexts #-}

module TreeTest where

import Test.Tasty

treeTests :: IO TestTree
treeTests =
  return $
    testGroup
      "treetests"
      []

-- [testRep]

-- testRep :: TestTree
-- testRep = testCase "rep" $ do
--   let work = do
--         e <- parseExpr "{a: x: a}"
--         t <- runEvalEnv (evalExpr e)
--         evalReduceMonad
--           (VCur t [(RootTASeg, mkNewVal VNTop)])
--           (reduce >> getTMVal)
--   rE <- runExceptT work
--   case rE of
--     Left err -> assertFailure err
--     Right r -> do
--       putStrLn $ treeToRepString r
--       putStrLn $ treeToFullRepString r
--       putStrLn $ oneLinerStringOfVal r

--   return ()

-- evalResolveMonad :: (MonadIO m, MonadError String m) => StateT Context (ReaderT Config m) a -> m a
-- evalResolveMonad action = runReaderT (evalStateT action emptyContext) emptyConfig

-- evalReduceMonad ::
--   (MonadIO m, MonadError String m) => VCur -> StateT RTCState (ReaderT ReduceConfig (ExceptT Error m)) a -> m a
-- evalReduceMonad vc action = do
--   r <- runExceptT $ runReaderT (evalStateT action (RTCState vc emptyContext)) emptyReduceConfig
--   case r of
--     Left err -> throwError (show err)
--     Right v -> return v

-- runEvalEnv :: (MonadIO m, MonadError String m) => StateT CommonState (ReaderT Config m) a -> m a
-- runEvalEnv action = runReaderT (evalStateT action emptyCommonState) emptyConfig

-- --   rE <- runExceptT work
-- --   case rE of
-- --     Left err -> assertFailure err
-- --     Right r -> do
-- --       putStrLn $ treeToFullRepString r
-- --       putStrLn $ oneLinerStringOfVal r

-- --  testSnapshotTree
-- -- , testSnapshotTree2
-- -- testeliminateRCAndOtherRefs

-- -- testSnapshotTree :: TestTree
-- -- testSnapshotTree =
-- --   testCase "snapshot_tree" $ do
-- --     let
-- --       refAWithRC = mkNewValWithOp TNRefCycle (TGenOp $ withEmptyOpFrame $ Ref $ emptyIdentRef $ T.pack "x")

-- --       -- a1 = mkAtomVal (Int 1)
-- --       -- a2 = mkAtomVal (Int 2)
-- --       -- a3 = mkAtomVal (Int 3)
-- --       -- a4 = mkAtomVal (Int 4)
-- --       -- unify1 = mkUnifyOp [refAWithRC, a2]
-- --       -- disj1 = mkDisjoinOpFromList [DisjTerm False a1, DisjTerm False (mkMutableVal unify1)]
-- --       -- refB = withEmptyOpFrame $ Ref $ emptyIdentRef $ T.pack "b"
-- --       -- refBV = setMutVal (Just (mkMutableVal disj1)) refB
-- --       -- disj2 = mkDisjoinOpFromList [DisjTerm False (mkMutableVal refBV), DisjTerm False a4]
-- --       -- t = mkNewVal (TNMutable disj2)
-- --       t = refAWithRC

-- --     t <- case runExcept (snapshotTree t) of
-- --       Left err -> assertFailure err
-- --       Right t -> return t

-- --     putStrLn "-----"
-- --     let rep = buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = True})
-- --     putStrLn (repToString 0 rep)

-- --     putStrLn "-----"
-- --     let rep = buildRepTree t (defaultTreeRepBuildOption{trboRepSubFields = False})
-- --     putStrLn (repToString 0 rep)

-- --     putStrLn "-----"
-- --     BL.putStr (encode rep)

-- --     putStrLn "-----"
-- --     let astE = buildASTExprDebug t
-- --     case runExcept astE of
-- --       Left err -> assertFailure err
-- --       Right expr -> putStrLn $ exprToOneLinerStr expr

-- -- testSnapshotTree2 :: TestTree
-- -- testSnapshotTree2 =
-- --   testCase "snapshot_tree2" $ do
-- --     let
-- --       refAWithRC = setMutVal (Just (mkNewVal TNRefCycle)) (withEmptyOpFrame $ Ref $ emptyIdentRef $ T.pack "a")

-- --       b1 = mkBlockTree $ mkBlockFromAdder 1 (StaticSAdder (T.pack "x") (mkdefaultField (mkAtomVal (Int 2))))
-- --       b2 = mkBlockTree $ mkBlockFromAdder 1 (StaticSAdder (T.pack "y") (mkdefaultField (mkAtomVal (Int 2))))
-- --       unify1 = mkUnifyOp [mkNewVal (TNMutable refAWithRC), b2]
-- --       disj1 = mkDisjoinOpFromList [DisjTerm False b1, DisjTerm False (mkNewVal (TNMutable unify1))]
-- --       tester = mkNewVal (TNMutable disj1)

-- --     putStrLn "-----"
-- --     putStrLn (oneLinerStringOfVal tester)

-- --     putStrLn "-----"
-- --     let rep = buildRepTree tester (defaultTreeRepBuildOption{trboRepSubFields = True})
-- --     putStrLn (repToString 0 rep)

-- --     x <- case runExcept (snapshotTree tester) of
-- --       Left err -> assertFailure err
-- --       Right x -> return x

-- --     putStrLn "-----"
-- --     let rep = buildRepTree x (defaultTreeRepBuildOption{trboRepSubFields = False})
-- --     putStrLn (repToString 0 rep)

-- --     putStrLn "-----"
-- --     BL.putStr (encode rep)

-- --     putStrLn "-----"
-- --     let astE = buildASTExprDebug x
-- --     case runExcept astE of
-- --       Left err -> assertFailure err
-- --       Right expr -> putStrLn $ exprToOneLinerStr expr

-- buildAbsTA :: String -> ValAddr
-- buildAbsTA path = appendValAddr rootValAddr (addrFromString path)

-- absA, absAX, absB, absC :: ValAddr
-- absA = buildAbsTA "a"
-- absAX = buildAbsTA "a.x"
-- absB = buildAbsTA "b"
-- absC = buildAbsTA "c"

-- -- testeliminateRCAndOtherRefs :: TestTree
-- -- testeliminateRCAndOtherRefs = testCase "eliminateRCAndOtherRefs" $ do
-- --   let work = do
-- --         e <- parseExpr "{a: 2 & (b + 1), b: a - 1}"
-- --         t <- runEvalEnv (evalExpr e)
-- --         r <-
-- --           evalResolveMonad
-- --             ( do
-- --                 let rootVC = VCur t [(RootTASeg, mkNewVal VNTop)]
-- --                 aTC <- goDownVCSegMust (strToStringFeature "a") rootVC
-- --                 eliminateRCAndOtherRefs [absA, absB] [absA] aTC
-- --             )
-- --         return $ focus r
-- --   rE <- runExceptT work
-- --   case rE of
-- --     Left err -> assertFailure err
-- --     Right r -> do
-- --       putStrLn $ treeToFullRepString r
-- --       putStrLn $ oneLinerStringOfVal r
-- --  where
-- --   b1 = mkBlockTree $ mkBlockFromAdder 1 (StaticSAdder (T.pack "x") (mkdefaultField (mkAtomVal (Int 2))))
