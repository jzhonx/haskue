{-# LANGUAGE ViewPatterns #-}

module Reduce.Stdlib.Strings where

import qualified Data.ByteString.Char8 as BC
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import Feature
import Reduce.Monad (RM)
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
join [VList l, VAtom (String sep)] _ = do
  case fetchStringArgs (map value $ V.toList l.final) of
    Left v -> return v
    Right stringArgs -> return $ VAtom $ String $ joinBSs stringArgs sep
join _ _ =
  return $
    mkBottomVal "wrong type of arguments to Join"

joinBSs :: [BC.ByteString] -> BC.ByteString -> BC.ByteString
joinBSs bs sep = BC.intercalate sep bs