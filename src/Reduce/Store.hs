module Reduce.Store where

import Data.Aeson (KeyValue (..), object)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence as Seq
import Feature
import Reduce.Monad
import StringIndex (ShowWTIndexer (..), TextIndex, strToTextIndex)
import Text.Printf (printf)
import Util.Trace (debugInstant)
import Value
import Value.Instances (posttravsVT, setSubVN)

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
  case addrIsVertex addr of
    Just saddr -> return $ Map.lookup saddr store
    Nothing -> do
      addrT <- tshow addr
      throwFatal $ printf "%s cannot fetch value for non-suffix-irreducible addr: %s" hdr addrT

lookupIdentFromStore :: Feature -> CanonicalAddr -> CanonicalAddr -> RM (Maybe (VNode, ValAddr))
lookupIdentFromStore identf diff addr = do
  let targetScopeAddr = trimSuffixAddr (getCanonicalAddr diff) (getCanonicalAddr addr)
      targetAddr = appendSeg targetScopeAddr identf
  vM <- fetchValFromStore "lookupIdentFromStore" targetAddr
  case vM of
    Just v -> return $ Just (v, targetAddr)
    Nothing -> return Nothing

storeVal :: ValAddr -> VNode -> RM ()
storeVal addr v = do
  store <- vStore <$> getRMContext
  case addrIsVertex addr of
    Just saddr -> do
      let newStore = Map.insert saddr v store
      modifyRMContext $ \ctx -> ctx{vStore = newStore}
    Nothing -> return ()

-- | Set the value to Unknown for the value with the address.
setUnknownInStore :: ValAddr -> RM ()
setUnknownInStore addr = do
  store <- vStore <$> getRMContext
  case addrIsVertex addr of
    Just saddr -> do
      let newStore =
            Map.adjust
              (\v -> v{value = VUnknown, version = v.version + 1})
              saddr
              store
      modifyRMContext $ \ctx -> ctx{vStore = newStore}
    Nothing -> return ()

propValUp :: ValAddr -> VNode -> RM (Maybe (ValAddr, VNode))
propValUp addr vn
  | fileTopValAddr == addr = return Nothing
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

queryLastDerefedVal :: VertexAddr -> ReferableAddr -> RM (Maybe Int)
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
            | ResolvedIdentFromTop resIdentAddr <- ref.resolvedIdentAddr
            , srcAddr `isPrefix` resIdentAddr && resIdentAddr /= srcAddr ->
                let rest = trimPrefixAddr srcAddr resIdentAddr
                    rfbDstAddr = trimCanonicalToRfb $ collapseToCanonical dstAddr
                    newIdentAddr = appendValAddr (rfbAddrToAddr rfbDstAddr) rest
                    newRef = ref{resolvedIdentAddr = ResolvedIdentFromTop newIdentAddr}
                 in VTOp (Ref newRef)
          _ -> x
    )
    srcAddr

storeComprehBindingVal :: Int -> TextIndex -> VNode -> RM ()
storeComprehBindingVal depth name vn = do
  bindings <- comprehBindings <$> getRMContext
  let
    oldPairs = fromJust $ bindings Seq.!? depth
    newPairs =
      if any (\(n, _) -> n == name) oldPairs
        then map (\(n, v) -> if n == name then (n, vn) else (n, v)) oldPairs
        else (name, vn) : oldPairs
    newBindings = Seq.update depth newPairs bindings
  modifyRMContext $ \ctx -> ctx{comprehBindings = newBindings}

withComprehBindings :: [(TextIndex, VNode)] -> RM a -> RM a
withComprehBindings newPairs action = do
  pushComprehBinding newPairs
  result <- action
  popComprehBindingVal
  return result

popComprehBindingVal :: RM ()
popComprehBindingVal = do
  bindings <- comprehBindings <$> getRMContext
  case Seq.viewr bindings of
    Seq.EmptyR -> throwFatal "popComprehBindingVal: no comprehension binding to pop"
    bs Seq.:> _ -> modifyRMContext $ \ctx -> ctx{comprehBindings = bs}

pushComprehBinding :: [(TextIndex, VNode)] -> RM ()
pushComprehBinding newPairs = do
  bindings <- comprehBindings <$> getRMContext
  let newBindings = bindings Seq.|> newPairs
  modifyRMContext $ \ctx -> ctx{comprehBindings = newBindings}

fetchComprehBindingVal :: Int -> TextIndex -> RM VNode
fetchComprehBindingVal depth name = do
  bindings <- comprehBindings <$> getRMContext
  case lookupComprehBindingVal depth name bindings of
    Just vn -> return vn
    _ -> throwFatal $ printf "fetchComprehBindingVal: no comprehension binding found"

lookupComprehBindingVal :: Int -> TextIndex -> Seq.Seq [(TextIndex, VNode)] -> Maybe VNode
lookupComprehBindingVal depth name bindings = do
  pairs <- bindings Seq.!? depth
  lookup name pairs