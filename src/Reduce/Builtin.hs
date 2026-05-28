module Reduce.Builtin where

import Data.Foldable (Foldable (toList))
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import Feature
import Reduce.Monad (RM, throwFatal)
import StringIndex (strToTextIndex)
import Text.Printf (printf)
import Value

builtinFuncMap :: RM (Map.Map ValAddr ([Val] -> ValAddr -> RM Val))
builtinFuncMap =
  Map.fromList
    <$> mapM
      ( \(name, f) -> do
          nameTI <- strToTextIndex name
          let addr = appendSeg universalValAddr (mkStringFeature nameTI)
          return (addr, f)
      )
      [ ("close", close)
      , ("slice", sliceWith "slice")
      , ("sliceLeft", sliceWith "sliceLeft")
      , ("sliceRight", sliceWith "sliceRight")
      ]

-- | Closes a struct when the tree has struct.
close :: [Val] -> ValAddr -> RM Val
close [arg] _ = return $ closeConcrete arg
close args _ = return $ mkBottomVal $ printf "close function expects exactly 1 argument, got %d" (length args)

-- | Close a concrete value.
closeConcrete :: Val -> Val
closeConcrete a =
  case a of
    VUnknown -> VUnknown
    VStruct s -> VStruct $ s{stcClosed = True}
    -- This is the current behavior of close for non-struct values.
    -- If the value is a disjunction, we do not close the disjunction itself.
    VDisj dj -> case defDisjunctsFromDisj dj of
      [x] -> x
      _ -> VUnknown
    _ -> mkBottomVal $ printf "cannot use %s as struct in argument 1 to close" (show a)

sliceWith :: String -> [Val] -> ValAddr -> RM Val
sliceWith _ [_] _ = return $ mkBottomVal "slice expects at least 1 argument"
sliceWith name (opd : rest) addr = case name of
  "slice" -> slice opd (Just $ head args) (Just $ args !! 1) addr
  "sliceLeft" -> slice opd (Just $ head args) Nothing addr
  "sliceRight" -> slice opd Nothing (Just $ head args) addr
  _ -> throwFatal $ printf "unexpected error in sliceWith: unknown function name %s" name
 where
  args = toList rest
sliceWith _ _ _ = throwFatal "unexpected error in sliceWith: should have been handled by semantics"

slice :: Val -> Maybe Val -> Maybe Val -> ValAddr -> RM Val
slice opd (Just ls) (Just rs) _ =
  case ( do
          l <- fetchSliceOprand opd
          ls' <- fetchSliceIdx ls
          rs' <- fetchSliceIdx rs
          return (l, ls', rs')
       ) of
    Right (l, ls', rs') -> return $ VList $ sliceList ls' rs' l
    Left v -> return v
slice opd (Just ls) Nothing _ =
  case ( do
          l <- fetchSliceOprand opd
          ls' <- fetchSliceIdx ls
          return (l, ls')
       ) of
    Right (l, ls') -> return $ VList $ sliceList ls' maxBound l
    Left v -> return v
slice opd Nothing (Just rs) _ =
  case ( do
          l <- fetchSliceOprand opd
          rs' <- fetchSliceIdx rs
          return (l, rs')
       ) of
    Right (l, rs') -> return $ VList $ sliceList 0 rs' l
    Left v -> return v
slice _ Nothing Nothing _ = throwFatal "should have been handled by semantics"

fetchSliceOprand :: Val -> Either Val List
fetchSliceOprand opd = case opd of
  VList l -> Right l
  VBottom _ -> Left opd
  VUnknown -> Left opd
  _ -> Left $ mkBottomVal $ printf "cannot slice %s" (showValType opd)

fetchSliceIdx :: Val -> Either Val Int
fetchSliceIdx idx = case idx of
  VAtom (Int i) -> Right (fromIntegral i)
  VBottom _ -> Left idx
  VUnknown -> Left idx
  _ -> Left $ mkBottomVal $ printf "cannot use %s as slice index"

sliceList :: Int -> Int -> List -> List
sliceList ls rs l =
  let len = V.length (store l)
      -- Handle negative indices and out-of-bounds indices.
      start = if ls < 0 then max 0 (len + ls) else min ls len
      end = if rs < 0 then max 0 (len + rs) else min rs len
   in l{store = V.slice start (max 0 (end - start)) (store l)}