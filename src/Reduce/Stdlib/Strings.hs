{-# LANGUAGE ViewPatterns #-}

module Reduce.Stdlib.Strings where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, listToMaybe)
import qualified Data.Vector as V
import Feature
import Reduce.Monad (RM)
import Reduce.TraceSpan (traceSpanNoPreRM)
import StringIndex (strToTextIndex)
import Text.Printf (printf)
import Value

funcMap :: RM (Map.Map ValAddr ([Val] -> ValAddr -> RM Val))
funcMap = do
  pkgTI <- strToTextIndex "strings"
  Map.fromList
    <$> mapM
      ( \(name, f) -> do
          nameTI <- strToTextIndex name
          let
            pkgAddr = appendSeg packageValAddr (mkStringFeature pkgTI)
            addr = appendSeg pkgAddr (mkStringFeature nameTI)
          return (addr, f)
      )
      [ ("Join", join)
      , ("Replace", replace)
      ]

withConcreteArgs :: [Val] -> ValAddr -> ([Val] -> ValAddr -> RM Val) -> RM Val
withConcreteArgs args addr f = case fetchConcreteArgs args of
  Left v -> return v
  Right concreteArgs -> f concreteArgs addr

fetchConcreteArgs :: [Val] -> Either Val [Val]
fetchConcreteArgs = mapM isConcrete
 where
  isConcrete v = case v of
    VUnknown -> Left v
    VBottom{} -> Left v
    _ -> Right v

fetchStringArgs :: [Val] -> Either Val [BC.ByteString]
fetchStringArgs = mapM isString
 where
  isString v = case v of
    (rtrString -> Just s) -> Right s
    VUnknown -> Left v
    VBottom{} -> Left v
    _ ->
      let
        msg :: String
        msg = printf "expected a string argument, got %s" (showValType v)
       in
        Left $ mkBottomVal msg

join :: [Val] -> ValAddr -> RM Val
join [VList l, VAtom (String sep)] _
  | not l.isFinalReady = return VUnknown
  | otherwise = do
      case fetchStringArgs (V.toList l.final) of
        Left v -> return v
        Right stringArgs -> return $ VAtom $ String $ joinBSs stringArgs sep
join _ _ = return $ mkBottomVal "wrong type of arguments to Join"

joinBSs :: [BC.ByteString] -> BC.ByteString -> BC.ByteString
joinBSs bs sep = BC.intercalate sep bs

replace :: [Val] -> ValAddr -> RM Val
replace [VAtom (String s), VAtom (String old), VAtom (String new), VAtom (Int n)] addr =
  traceSpanNoPreRM "strings.Replace" addr $
    return $
      VAtom $
        String $
          replaceBS s old new (fromIntegral n)
replace xs addr = traceSpanNoPreRM "strings.Replace" addr $ do
  let incompletes = map rtrIncomplete xs
  case listToMaybe $ catMaybes incompletes of
    Just _ -> return VUnknown
    Nothing -> return $ mkBottomVal "wrong type of arguments to Replace"

{- | Replace the first n occurrences of old with new in s.

From the https://pkg.go.dev/cuelang.org/go/pkg/strings#Replace

Replace returns a copy of the string s with the first n non-overlapping instances of old replaced by new. If old is
empty, it matches at the beginning of the string and after each UTF-8 sequence, yielding up to k+1 replacements for a
k-rune string. If n < 0, there is no limit on the number of replacements.
-}
replaceBS :: BC.ByteString -> BC.ByteString -> BC.ByteString -> Int -> BC.ByteString
replaceBS s old new n
  | n == 0 = s
  | BC.null old = replaceEmpty s new n
  | otherwise = replaceNonEmpty limit s
 where
  oldLen = BC.length old
  limit
    | n < 0 = Nothing
    | otherwise = Just n

  -- Replaces non-empty matches from left to right until the limit is reached.
  replaceNonEmpty (Just 0) rest = rest
  replaceNonEmpty remaining rest =
    case BC.breakSubstring old rest of
      (prefix, suffix)
        | BC.null suffix -> prefix
        | otherwise -> prefix <> new <> replaceNonEmpty (step remaining) (BC.drop oldLen suffix)

  -- Decrements the remaining replacement count when a bounded limit is used.
  step Nothing = Nothing
  step (Just k) = Just (k - 1)

  -- Handles the special case where an empty pattern matches between UTF-8 code points.
  replaceEmpty bs repl count = BS.concat (go inserts (utf8Chunks bs))
   where
    chunks = utf8Chunks bs
    maxInserts = length chunks + 1
    inserts
      | count < 0 = maxInserts
      | otherwise = min count maxInserts

    -- Interleaves replacements before each chunk while inserts remain.
    go remaining []
      | remaining > 0 = [repl]
      | otherwise = []
    go remaining (chunk : chunks)
      | remaining > 0 = repl : chunk : go (remaining - 1) chunks
      | otherwise = chunk : go remaining chunks

  -- Splits a ByteString into UTF-8-sized chunks without validating encoding.
  utf8Chunks = unfoldUtf8

  -- Consumes the input one UTF-8-sized chunk at a time.
  unfoldUtf8 bs
    | BS.null bs = []
    | otherwise = chunk : unfoldUtf8 rest
   where
    len = min (utf8CharLen (BS.head bs)) (BS.length bs)
    chunk = BS.take len bs
    rest = BS.drop len bs

  -- Estimates the width of a UTF-8 code point from its leading byte.
  utf8CharLen w
    | w < 0x80 = 1
    | w < 0xC0 = 1
    | w < 0xE0 = 2
    | w < 0xF0 = 3
    | w < 0xF8 = 4
    | otherwise = 1
