module Main where

import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import Path
import Reduce.Mutate
import Weigh

testPrefix :: TreeAddr -> Bool
testPrefix addr = isPrefix pathLong2 addr

pathLong :: TreeAddr
pathLong = addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y.z"

pathLong2 :: TreeAddr
pathLong2 = addrFromString "a.b.c.d.e.f.g.h.i.j.k.l.m.n.o.p.q.r.s.t.u.v.w.x.y"

testPrefix2 :: TreeAddr -> Bool
testPrefix2 _ = False

tData :: Map.Map TreeAddr [TreeAddr]
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
  g = addrFromString

pathABC :: TreeAddr
pathABC = addrFromString "a.b.c"

pathBC :: TreeAddr
pathBC = addrFromString "b.c"

-- | Delete the receivers that have the mutable address as the prefix.
delRecvsInMap :: TreeAddr -> Map.Map TreeAddr [TreeAddr] -> Map.Map TreeAddr [TreeAddr]
delRecvsInMap mutAddr =
  Map.mapMaybe
    ( \l ->
        let r =
              filter
                ( \recv ->
                    let
                      mutValAddr = mutAddr
                     in
                      not $ {-# SCC "isPrefix" #-} isPrefix mutValAddr recv
                )
                l
         in if null r
              then Nothing
              else Just r
    )

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

main :: IO ()
main = mainWith $ do
  -- Configure columns to show allocation
  setColumns [Case, Allocated, GCs, Live, Max, WallTime]

  -- Measure a pure function
  func "improve" (isPrefix pathLong) pathLong2
  func "control" testPrefix2 pathLong

  func "improve-del" (delRecvsInMap pathABC) tData
  func "improve-control" (delRecvsInMap2 pathABC) tData
