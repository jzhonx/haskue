{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Main (main) where

import Common
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError)
import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State.Strict (StateT, evalStateT, execStateT, runStateT)
import Criterion.Main
import qualified Cursor
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
import qualified Path
import qualified Reduce.Mutate as Mutate
import qualified Reduce.RMonad as RM
import qualified Reduce.RefSys as RefSys
import qualified TCOps
import qualified Value.Tree as VT

tData :: Map.Map Path.TreeAddr [Path.TreeAddr]
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
  g = Path.addrFromString

pathABC :: Path.TreeAddr
pathABC = Path.addrFromString "a.b.c"

pathBC :: Path.TreeAddr
pathBC = Path.addrFromString "b.c"

work :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
work x = Mutate.delRecvsInMap pathABC x

delRecvsInMap2 :: Path.TreeAddr -> Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
delRecvsInMap2 mutAddr m = delEmptyElem $ delRecvs m
 where
  delEmptyElem :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  delEmptyElem = Map.filter (not . null)

  -- Delete the receivers that have the mutable address as the prefix.
  delRecvs :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
  delRecvs =
    Map.map
      ( filter
          ( \recv ->
              let
                mutValAddr = Path.appendSeg mutAddr Path.SubValTASeg
               in
                not $ Path.isPrefix mutValAddr recv
          )
      )

work2 :: Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
work2 x = delRecvsInMap2 pathABC x

testPrefix :: Path.TreeAddr -> Bool
testPrefix addr = Path.isPrefix pathLong2 addr

pathLong :: Path.TreeAddr
pathLong = Path.addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z"

pathLong2 :: Path.TreeAddr
pathLong2 = Path.addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y"

testPrefix2 :: Path.TreeAddr -> Path.TreeAddr -> Bool
testPrefix2 (Path.TreeAddr x) (Path.TreeAddr y) = V.length x <= V.length y && V.and (V.zipWith (==) x y)

runRM :: StateT Common.Context (ReaderT Eval.Runner (ExceptT String IO)) a -> IO a
runRM f = do
  let runner =
        Eval.emptyRunner
          { Eval.rcConfig =
              ( Common.Config
                  { Common.cfSettings =
                      Common.Settings
                        { Common.stDebugLogging = False
                        , Common.stTraceExec = False
                        , Common.stTracePrintTree = False
                        , Common.stTraceFilter = Set.empty
                        , Common.stShowMutArgs = False
                        , Common.stMaxTreeDepth = 15
                        }
                  , Common.cfRuntimeParams = Common.RuntimeParams{Common.rpCreateCnstr = True}
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
        let !vp = Path.valPathFromString "a.b.c.d"
        runRM $ do
          root <- case rE of
            Left err -> throwError err
            Right v -> return v
          let rootTC = Cursor.TreeCursor root [(Path.RootTASeg, VT.mkNewTree VT.TNTop)]
          let addr = Path.addrFromString "b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z"
          !startTC <- TCOps.goDownTCAddrMust addr rootTC
          return (vp, startTC)
    )
    ( \ ~(vp, startTC) -> bench "base" $ nfIO $ do
        runRM $ do
          res <- RefSys.getDstTC vp Nothing startTC
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
            [ bench "improve" $ whnf (Mutate.delRecvsInMap pathABC) tData
            , bench "control" $ whnf (delRecvsInMap2 pathABC) tData
            ]
        , bgroup
            "isPrefix"
            [ bench "improve" $ nf (Path.isPrefix pathLong2) pathLong
            , bench "control" $ nf (testPrefix2 pathLong2) pathLong
            ]
        , bgroup
            "getDstTC"
            [ testGetDstTC
            ]
        ]
    ]
