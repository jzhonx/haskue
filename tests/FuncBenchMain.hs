{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Main (main) where

import Common
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (StateT, evalStateT, execStateT, runStateT)
import Criterion.Main
import Cursor
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Vector as V
import Eval (
  Runner (rcConfig),
  emptyEvalConfig,
  emptyRunner,
  strToCUEVal,
 )
import qualified Eval
import Feature
import Reduce.RMonad
import Reduce.RefSys
import qualified Value as VT
import Value.Tree

tData :: Map.Map TreeAddr [TreeAddr]
tData =
  Map.fromList
    [ (g "a.b.c.d", [g "a.b.c.e", g "a.b.c.f"])
    , (g "a.b.c.e", [g "a.b.c.d"])
    , (g "a.b.d.f", [g "a.b.c.d"])
    , (g "a.b.f.g", [g "a.b.c.h"])
    , (g "a.b.c.h", [])
    , (g "a.b.d.i", [g "a.b.c.j"])
    , (g "a.b.c.j", [])
    , (g "a.b.e.k", [])
    ]
 where
  g = addrFromString

pathABC :: TreeAddr
pathABC = addrFromString "a.b.c"

pathBC :: TreeAddr
pathBC = addrFromString "b.c"

work :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
work x = delRecvsInMap pathABC x

delRecvsInMap2 :: TreeAddr -> Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
delRecvsInMap2 mutAddr m = delEmptyElem $ delRecvs m
 where
  delEmptyElem :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  delEmptyElem = Map.filter (not . null)

  -- Delete the receivers that have the mutable address as the prefix.
  delRecvs :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
  delRecvs =
    Map.map
      ( filter
          ( \recv ->
              let
                mutValAddr = mutAddr
               in
                not $ isPrefix mutValAddr recv
          )
      )

work2 :: Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
work2 x = delRecvsInMap2 pathABC x

testPrefix :: TreeAddr -> Bool
testPrefix addr = isPrefix pathLong2 addr

pathLong :: TreeAddr
pathLong = addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z"

pathLong2 :: TreeAddr
pathLong2 = addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y"

testPrefix2 :: TreeAddr -> TreeAddr -> Bool
testPrefix2 (TreeAddr x) (TreeAddr y) = V.length x <= V.length y && V.and (V.zipWith (==) x y)

runRM :: StateT Common.Context (ReaderT Eval.Runner (ExceptT String IO)) a -> IO a
runRM f = do
  let runner =
        Eval.emptyRunner
          { Eval.rcConfig =
              ( Common.Config
                  { Common.cfSettings =
                      Common.Settings
                        { Common.stTraceExtraInfo = False
                        , Common.stTraceEnable = False
                        , Common.stTracePrintTree = False
                        , Common.stTraceFilter = Set.empty
                        , Common.stShowMutArgs = False
                        , Common.stMaxTreeDepth = 15
                        }
                  , Common.cfReduceParams = Common.ReduceParams{Common.createCnstr = True}
                  }
              )
          }
  x <- runExceptT (runReaderT (evalStateT f Common.emptyContext) runner)
  case x of
    Left err -> error err
    Right r -> return r

testGetDstTC :: Benchmark
testGetDstTC =
  env
    ( do
        let s = "{a: {b: c: d: e: f: 1}, b: c: d: e: f: g: h: i: j: k: l: m: n: o: p: q: r: s: t: u: v: w: x: y: z: 2}}"
        rE <- runExceptT $ Eval.strToCUEVal s Eval.emptyEvalConfig
        let !vp = fieldPathFromString "a.b.c.d"
        runRM $ do
          root <- case rE of
            Left err -> throwError err
            Right v -> return v
          let rootTC = TrCur root [(RootTASeg, mkNewTree TNTop)]
          let addr = addrFromString "b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z"
          !startTC <- Cursor.goDownTCAddrMust addr rootTC
          return (vp, startTC)
    )
    ( \ ~(vp, startTC) -> bench "base" $ nfIO $ do
        runRM $ do
          res <- getDstTC vp Nothing startTC
          case res of
            Nothing -> throwError "getDstTC returned Nothing"
            _ -> return ()
    )

main :: IO ()
main =
  defaultMain
    [ bgroup
        "cue"
        [ bgroup
            "del"
            [ bench "improve" $ whnf (delRecvsInMap pathABC) tData
            , bench "control" $ whnf (delRecvsInMap2 pathABC) tData
            ]
        , bgroup
            "isPrefix"
            [ bench "improve" $ nf (isPrefix pathLong2) pathLong
            , bench "control" $ nf (testPrefix2 pathLong2) pathLong
            ]
        , bgroup
            "getDstTC"
            [ testGetDstTC
            ]
        , bgroup
            "snapshotTree"
            [ testGetDstTC
            ]
        ]
    ]
