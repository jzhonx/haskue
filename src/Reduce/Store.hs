module Reduce.Store where

import Cursor (setSubVN)
import Data.Aeson (KeyValue (..), object)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Feature
import Reduce.Monad
import StringIndex (ShowWTIndexer (..))
import Text.Printf (printf)
import Util.Trace (debugInstant)
import Value
import Value.Instances (posttravsVT)

fetchValMust :: String -> ValAddr -> RM VNode
fetchValMust hdr addr = do
  mv <- fetchValFromStore hdr addr
  case mv of
    Just v -> return v
    Nothing -> do
      addrT <- tshow addr
      let msg = printf "%s value not found for addr: %s" hdr addrT
      debugInstant "fetchValMust" (object ["addr" .= addrT, "msg" .= hdr])
      throwFatal msg

fetchValFromStore :: String -> ValAddr -> RM (Maybe VNode)
fetchValFromStore hdr addr = do
  store <- vStore <$> getRMContext
  case addrIsCanonical addr of
    Just saddr -> return $ Map.lookup saddr store
    Nothing -> do
      addrT <- tshow addr
      throwFatal $ printf "%s cannot fetch value for non-suffix-irreducible addr: %s" hdr addrT

storeVal :: ValAddr -> VNode -> RM ()
storeVal addr v = do
  store <- vStore <$> getRMContext
  case addrIsCanonical addr of
    Just saddr -> do
      let newStore = Map.insert saddr v store
      modifyRMContext $ \ctx -> ctx{vStore = newStore}
    Nothing -> return ()

-- | Store the value with the address and all its ancestors up to the root.
storeValUpToRoot :: ValAddr -> VNode -> RM ()
storeValUpToRoot addr v = do
  storeVal addr v
  parent <- propValUp addr v
  case parent of
    Just (pAddr, pVal) -> storeValUpToRoot pAddr pVal
    Nothing -> return ()

propValUp :: ValAddr -> VNode -> RM (Maybe (ValAddr, VNode))
propValUp addr vn
  | rootValAddr == addr = return Nothing
  | otherwise = do
      let
        subF = fromJust $ lastSeg addr
        parentAddr = fromJust $ initValAddr addr
      parentVN <- fetchValMust "propValUp" parentAddr
      let newParentVNM = setSubVN subF vn parentVN
      case newParentVNM of
        Just newParentVN -> return $ Just (parentAddr, newParentVN)
        Nothing -> do
          subFT <- tshow subF
          parentAddrT <- tshow parentAddr
          let
            parentVT = showValType (value parentVN)
            msg =
              printf
                "failed to set sub val for parent val %s with feature %s and parent addr %s"
                parentVT
                subFT
                parentAddrT
          debugInstant "propValUp" (object ["parentAddr" .= parentAddrT, "subF" .= subFT, "parentV" .= parentVT, "msg" .= msg])
          throwFatal msg

queryLastDerefedVal :: VertexAddr -> ReferableAddr -> RM (Maybe VNode)
queryLastDerefedVal addr depAddr = do
  m <- lastDerefs <$> getRMContext
  case Map.lookup addr m of
    Just depMap -> return $ Map.lookup depAddr depMap
    Nothing -> return Nothing

{- | Copy the value from the target address to the reference address.

It makes references that point to the value inside the target value point to the copied value.

All the values in the copied value will be put into the store with their addresses.
-}
copyVTermNode :: ValAddr -> ValAddr -> VTermNode -> VTermNode
copyVTermNode srcAddr dstAddr =
  posttravsVT
    ( \_ x ->
        case x of
          IsRef _ ref
            -- If the resolved ident address is inside the target value, then it should be redirected to the
            -- copied value.
            -- For example, {a: {x: 1, y: x}, b: a}. When we copy a to b, the reference in a should be
            -- redirected to the copied value of a, not the original a.
            | let resIdentAddr = ref.resolvedIdentAddr
            , srcAddr `isPrefix` resIdentAddr && resIdentAddr /= srcAddr ->
                let rest = trimPrefixAddr srcAddr resIdentAddr
                    rfbDstAddr = trimCanonicalToRfb $ collapseToCanonical dstAddr
                    newIdentAddr = appendValAddr (rfbAddrToAddr rfbDstAddr) rest
                    newRef = ref{resolvedIdentAddr = newIdentAddr}
                 in VTOp (Ref newRef)
          _ -> x
    )
    srcAddr
