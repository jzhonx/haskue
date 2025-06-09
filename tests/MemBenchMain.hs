module Main where

import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import qualified Path
import qualified Reduce.Mutate as Mutate
import Weigh

testPrefix :: Path.TreeAddr -> Bool
testPrefix addr = Path.isPrefix pathLong2 addr

pathLong :: Path.TreeAddr
pathLong = Path.addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z"

pathLong2 :: Path.TreeAddr
pathLong2 = Path.addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y"

testPrefix2 :: Path.TreeAddr -> Bool
testPrefix2 _ = False

tData :: Map.Map Path.TreeAddr [Path.TreeAddr]
tData =
  Map.fromList
    [ (g "a.b.c.d", [g "a.b.c.e", g "a.b.c.f", g "a.e.c.f", g "a.d.c.f", g "a.b.c.h"])
    , (g "a.b.c.e", [g "a.b.c.d", g "a.b.c.f", g "a.e.c.f", g "a.d.c.f", g "a.b.c.h"])
    , (g "a.b.d.f", [g "a.b.c.d", g "a.b.c.f", g "a.e.c.f", g "a.d.c.f", g "a.b.c.h"])
    , (g "a.b.f.g", [g "a.b.c.h", g "a.b.c.f", g "a.e.c.f", g "a.d.c.f", g "a.b.c.h"])
    , (g "a.b.c.h", [g "a.b.c.f", g "a.e.c.f", g "a.d.c.f"])
    , (g "a.b.d.i", [g "a.b.c.j", g "a.b.c.f", g "a.e.c.f", g "a.d.c.f", g "a.b.c.h"])
    , (g "a.b.c.j", [g "a.b.c.f", g "a.e.c.f", g "a.d.c.f"])
    , (g "a.b.e.k", [g "a.b.c.f", g "a.e.c.f", g "a.d.c.f"])
    ]
 where
  g = Path.addrFromString

pathABC :: Path.TreeAddr
pathABC = Path.addrFromString "a.b.c"

pathBC :: Path.TreeAddr
pathBC = Path.addrFromString "b.c"

-- | Delete the receivers that have the mutable address as the prefix.
delRecvsInMap :: Path.TreeAddr -> Map.Map Path.TreeAddr [Path.TreeAddr] -> Map.Map Path.TreeAddr [Path.TreeAddr]
delRecvsInMap mutAddr =
  Map.mapMaybe
    ( \l ->
        let r =
              filter
                ( \recv ->
                    let
                      mutValAddr = Path.appendSeg mutAddr Path.SubValTASeg
                     in
                      not $ {-# SCC "isPrefix" #-} Path.isPrefix mutValAddr recv
                )
                l
         in if null r
              then Nothing
              else Just r
    )

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

main :: IO ()
main = mainWith $ do
  -- Configure columns to show allocation
  setColumns [Case, Allocated, GCs, Live, Max, WallTime]

  -- Measure a pure function
  func "improve" (Path.isPrefix pathLong) pathLong2
  func "control" testPrefix2 pathLong

  func "improve-del" (delRecvsInMap pathABC) tData
  func "improve-control" (delRecvsInMap2 pathABC) tData
