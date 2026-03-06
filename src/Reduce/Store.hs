module Reduce.Store where

import Cursor (setSubVal)
import Data.Aeson (KeyValue (..), object)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Feature
import Reduce.Monad
import Reduce.TraceSpan (traceSpanTM, valDebugRepJSON)
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)
import Util.Trace (debugInstant)
import Value
import Value.Instances (posttravsVal, pretravsValQ)

fetchValMust :: String -> ValAddr -> RM Val
fetchValMust hdr addr = do
  mv <- fetchValFromStore hdr addr
  case mv of
    Just v -> return v
    Nothing -> do
      addrT <- tshow addr
      let msg = printf "%s value not found for addr: %s" hdr addrT
      debugInstant "fetchValMust" (object ["addr" .= addrT, "msg" .= hdr])
      throwFatal msg

fetchValFromStore :: String -> ValAddr -> RM (Maybe Val)
fetchValFromStore hdr addr = do
  store <- vStore <$> getRMContext
  case addrIsSufIrred addr of
    Just saddr -> return $ Map.lookup saddr store
    Nothing -> do
      addrT <- tshow addr
      throwFatal $ printf "%s cannot fetch value for non-suffix-irreducible addr: %s" hdr addrT

-- | TODO: only store values with valid addresses
storeVal :: ValAddr -> Val -> RM ()
storeVal addr v = do
  store <- vStore <$> getRMContext
  case addrIsSufIrred addr of
    Just saddr -> do
      let newStore = Map.insert saddr v store
      modifyRMContext $ \ctx -> ctx{vStore = newStore}
    Nothing -> return ()

-- | Store the value with the address and all its ancestors up to the root.
storeValUpToRoot :: ValAddr -> Val -> RM ()
storeValUpToRoot addr v = do
  storeVal addr v
  parent <- propValUp addr v
  case parent of
    Just (pAddr, pVal) -> storeValUpToRoot pAddr pVal
    Nothing -> return ()

propValUp :: ValAddr -> Val -> RM (Maybe (ValAddr, Val))
propValUp addr v
  | rootValAddr == addr = return Nothing
  | otherwise = do
      let
        subF = fromJust $ lastSeg addr
        parentAddr = fromJust $ initValAddr addr
      parentV <- fetchValMust "propValUp" parentAddr
      let newParentVM = setSubVal subF v parentV
      case newParentVM of
        Just newParentV -> return $ Just (parentAddr, newParentV)
        Nothing -> do
          subFT <- tshow subF
          parentAddrT <- tshow parentAddr
          let
            parentVT = showValType parentV
            msg =
              printf
                "failed to set sub val for parent val %s with feature %s and parent addr %s"
                parentVT
                subFT
                parentAddrT
          debugInstant "propValUp" (object ["parentAddr" .= parentAddrT, "subF" .= subFT, "parentV" .= parentVT, "msg" .= msg])
          throwFatal msg

{- | Add the value and all its sub-values into the store with their addresses.

It recursively stores the value at the referable address.

It is typically used after we change the value without using reduce.
-}
storeAllSubVals :: ValAddr -> Val -> RM ()
storeAllSubVals topAddr topV =
  traceSpanTM "storeAllSubVals" topAddr (valDebugRepJSON topAddr topV) $ preOrderAdd topAddr topV
 where
  isSegUnwanted seg = case fetchLabelType seg of
    StubFieldLabelType -> True
    _ -> isFeatureReducible seg

  preOrderAdd :: ValAddr -> Val -> RM ()
  preOrderAdd p x = case lastSeg p of
    Just seg
      | not (isSegUnwanted seg) -> do
          storeVal p x
          sequence_ (vtmapQ preOrderAdd p x)
    _ -> return ()

queryLastDerefedVal :: SuffixIrredAddr -> ReferableAddr -> RM (Maybe Val)
queryLastDerefedVal addr depAddr = do
  m <- lastDerefs <$> getRMContext
  case Map.lookup addr m of
    Just depMap -> return $ Map.lookup depAddr depMap
    Nothing -> return Nothing

{- | Copy the value from the target address to the reference address.

It makes references that point to the value inside the target value point to the copied value.

All the values in the copied value will be put into the store with their addresses.
-}
copyVal :: ValAddr -> ValAddr -> Val -> RM Val
copyVal srcAddr dstAddr tarV =
  do
    let v' =
          posttravsVal
            ( \_ x ->
                case x of
                  IsRef sop ref
                    -- If the resolved ident address is inside the target value, then it should be redirected to the
                    -- copied value.
                    -- For example, {a: {x: 1, y: x}, b: a}. When we copy a to b, the reference in a should be
                    -- redirected to the copied value of a, not the original a.
                    | let resIdentAddr = ref.resolvedIdentAddr
                    , srcAddr `isPrefix` resIdentAddr && resIdentAddr /= srcAddr -> do
                        let rest = trimPrefixAddr srcAddr resIdentAddr
                            rfbDstAddr = trimAddrToRfb dstAddr
                            newIdentAddr = appendValAddr (rfbAddrToAddr rfbDstAddr) rest
                            newRef = ref{resolvedIdentAddr = newIdentAddr}
                        setTOp (setOpInSOp (Ref newRef) sop) x
                  _ -> x
            )
            dstAddr
            tarV
    pretravsValQ (>>) storeVal dstAddr v'
    return v'