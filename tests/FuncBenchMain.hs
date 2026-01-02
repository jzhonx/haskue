{-# LANGUAGE FlexibleContexts #-}

module Main (main) where

import Control.Monad (forM_)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (StateT, evalStateT, execStateT, runStateT)
import Criterion.Main
import Cursor
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Vector as V
import Env
import Eval (
  emptyEvalConfig,
  strToCUEVal,
 )
import qualified Eval
import Feature
import Reduce.RMonad
import Reduce.RefSys
import StringIndex (TextIndexer (..))
import qualified Value as VT
import Value.Val

-- tData :: Map.Map ValAddr [ValAddr]
-- tData =
--   Map.fromList
--     [ (g "a.b.c.d", [g "a.b.c.e", g "a.b.c.f"])
--     , (g "a.b.c.e", [g "a.b.c.d"])
--     , (g "a.b.d.f", [g "a.b.c.d"])
--     , (g "a.b.f.g", [g "a.b.c.h"])
--     , (g "a.b.c.h", [])
--     , (g "a.b.d.i", [g "a.b.c.j"])
--     , (g "a.b.c.j", [])
--     , (g "a.b.e.k", [])
--     ]
--  where
--   g = addrFromString

-- pathABC :: ValAddr
-- pathABC = addrFromString "a.b.c"

-- pathBC :: ValAddr
-- pathBC = addrFromString "b.c"

-- work :: Map.Map ValAddr [ValAddr] -> Map.Map ValAddr [ValAddr]
-- work x = delRecvsInMap pathABC x

-- delRecvsInMap2 :: ValAddr -> Map.Map ValAddr [ValAddr] -> Map.Map ValAddr [ValAddr]
-- delRecvsInMap2 mutAddr m = delEmptyElem $ delRecvs m
--  where
--   delEmptyElem :: Map.Map ValAddr [ValAddr] -> Map.Map ValAddr [ValAddr]
--   delEmptyElem = Map.filter (not . null)

--   -- Delete the receivers that have the mutable address as the prefix.
--   delRecvs :: Map.Map ValAddr [ValAddr] -> Map.Map ValAddr [ValAddr]
--   delRecvs =
--     Map.map
--       ( filter
--           ( \recv ->
--               let
--                 mutValAddr = mutAddr
--                in
--                 not $ isPrefix mutValAddr recv
--           )
--       )

-- work2 :: Map.Map ValAddr [ValAddr] -> Map.Map ValAddr [ValAddr]
-- work2 x = delRecvsInMap2 pathABC x

-- testPrefix :: ValAddr -> Bool
-- testPrefix addr = isPrefix pathLong2 addr

-- pathLong :: ValAddr
-- pathLong = addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z"

-- pathLong2 :: ValAddr
-- pathLong2 = addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y"

-- testPrefix2 :: ValAddr -> ValAddr -> Bool
-- testPrefix2 (ValAddr x) (ValAddr y) = V.length x <= V.length y && V.and (V.zipWith (==) x y)

runRM :: ReduceConfig -> RTCState -> StateT RTCState (ReaderT ReduceConfig (ExceptT Error IO)) a -> IO a
runRM conf initState f = do
  -- let runner =
  --       Eval.emptyRunner
  --         { Eval.rcConfig =
  --             ( Env.Config
  --                 { Env.cfSettings =
  --                     Env.Settings
  --                       { Env.stTraceExtraInfo = False
  --                       , Env.stTraceEnable = False
  --                       , Env.stTracePrintTree = False
  --                       , Env.stTraceFilter = Set.empty
  --                       , Env.stShowMutArgs = False
  --                       , Env.stMaxTreeDepth = 15
  --                       }
  --                 , Env.cfReduceParams = Env.ReduceParams{Env.createCnstr = True}
  --                 }
  --             )
  --         }
  x <- runExceptT (runReaderT (evalStateT f initState) conf)
  case x of
    Left err -> error $ show err
    Right r -> return r

testCustom :: Benchmark
testCustom =
  env
    ( do
        let
          root = mkAtomVal $ VT.String $ T.pack "yyyyyyyyyyyyyyyy"
          rootVC =
            VCur
              root
              [ (rootFeature, mkNewVal VNTop)
              , (rootFeature, mkNewVal VNTop)
              , (rootFeature, mkNewVal VNTop)
              , (rootFeature, mkNewVal VNTop)
              , (rootFeature, mkNewVal VNTop)
              , (rootFeature, mkNewVal VNTop)
              ]
          state =
            RTCState
              { rtsTC = rootVC
              , rtsCtx =
                  emptyContext
                    { Reduce.RMonad.tIndexer =
                        TextIndexer
                          { labels = V.fromList $ [T.pack (show i) | i <- [0 .. 100000]]
                          , labelToIndex = Map.fromList [(T.pack $ show i, i) | i <- [0 .. 100000]]
                          }
                    }
              }
        return state
    )
    ( \state -> bench "base" $ nfIO $ do
        runRM emptyReduceConfig state $ do
          forM_ [1 .. 1000] $ \_ -> do
            vc <- getTMCursor
            let rtc = setVCFocusVN VNTop vc
            putTMCursor rtc
    )

-- testGetDstTC :: Benchmark
-- testGetDstTC =
--   env
--     ( do
--         let s = "{a: {b: c: d: e: f: 1}, b: c: d: e: f: g: h: i: j: k: l: m: n: o: p: q: r: s: t: u: v: w: x: y: z: 2}}"
--         rE <- runExceptT $ Eval.strToCUEVal s Eval.emptyEvalConfig
--         let !vp = fieldPathFromString "a.b.c.d"
--         runRM $ do
--           root <- case rE of
--             Left err -> throwError err
--             Right v -> return v
--           let rootVC = VCur root [(RootTASeg, mkNewVal VNTop)]
--           let addr = addrFromString "b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z"
--           !startTC <- Cursor.goDownVCAddrMust addr rootVC
--           return (vp, startTC)
--     )
--     ( \ ~(vp, startTC) -> bench "base" $ nfIO $ do
--         runRM $ do
--           res <- getDstTC vp Nothing startTC
--           case res of
--             Nothing -> throwError "getDstTC returned Nothing"
--             _ -> return ()
--     )

main :: IO ()
main =
  defaultMain
    [ bgroup
        "cue"
        [ bgroup
            "RM"
            [ testCustom
            ]
            -- bgroup
            --   "del"
            --   [ bench "improve" $ whnf (delRecvsInMap pathABC) tData
            --   , bench "control" $ whnf (delRecvsInMap2 pathABC) tData
            --   ]
            -- , bgroup
            --     "isPrefix"
            --     [ bench "improve" $ nf (isPrefix pathLong2) pathLong
            --     , bench "control" $ nf (testPrefix2 pathLong2) pathLong
            --     ]
            -- , bgroup
            --     "getDstTC"
            --     [ testGetDstTC
            --     ]
            -- , bgroup
            --     "snapshotTree"
            --     [ testGetDstTC
            --     ]
        ]
    ]
