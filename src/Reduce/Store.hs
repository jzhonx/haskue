module Reduce.Store where

import Data.Aeson (KeyValue (..), object)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import qualified Data.Sequence as Seq
import DepGraph (VertexAddr, vertexToAddr)
import EvalAddr
import Reduce.Monad
import Reduce.TraceSpan (debugInst, debugInstStr)
import StringIndex (ShowWTIndexer (..), TextIndex)
import Text.Printf (printf)
import Value
import Value.Instances (posttravsVT, setSubVN)

fetchValMust :: String -> EvalAddr -> RM VNode
fetchValMust hdr addr = do
  mv <- fetchValFromStore hdr addr
  case mv of
    Just v -> return v
    Nothing -> do
      addrT <- tshow addr
      let msg = printf "%s: no value found at address %s" hdr addrT
      debugInst "fetchValMust" addr (return $ object ["addr" .= addrT, "msg" .= hdr])
      throwFatal msg

fetchValFromStore :: String -> EvalAddr -> RM (Maybe VNode)
fetchValFromStore hdr addr = do
  store <- vStore <$> getRMContext
  case addrIsReduced addr of
    Just reducedAddr -> return $ Map.lookup reducedAddr store
    Nothing -> do
      addrT <- tshow addr
      throwFatal $ printf "%s: cannot fetch a value at non-reduced address %s" hdr addrT

storeVal :: EvalAddr -> VNode -> RM ()
storeVal addr v = do
  store <- vStore <$> getRMContext
  case addrIsReduced addr of
    Just reducedAddr -> do
      let newStore = Map.insert reducedAddr v store
      modifyRMContext $ \ctx -> ctx{vStore = newStore}
    Nothing -> return ()

-- | Set the value to Unknown for the value with the address.
setUnknownInStore :: EvalAddr -> RM ()
setUnknownInStore addr = do
  store <- vStore <$> getRMContext
  case addrIsReduced addr of
    Just reducedAddr -> do
      let newStore =
            Map.adjust
              (\v -> v{value = VUnknown, version = v.version + 1})
              reducedAddr
              store
      modifyRMContext $ \ctx -> ctx{vStore = newStore}
    Nothing -> return ()

propValUp :: EvalAddr -> VNode -> RM (Maybe (EvalAddr, VNode))
propValUp addr vn
  | fileTopEvalAddr == addr = return Nothing
  | otherwise = do
      let
        subF = fromJust $ lastSeg addr
        parentAddr = fromJust $ initEvalAddr addr
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
          debugInst
            "propValUp"
            parentAddr
            (return $ object ["parentAddr" .= parentAddrT, "subF" .= subFT, "parentV" .= parentVT, "msg" .= msg])
          throwFatal msg

queryLastDerefedVersion :: VertexAddr -> DependencyAddr -> RM (Maybe Int)
queryLastDerefedVersion useAddr depAddr = do
  m <- lastDerefs <$> getRMContext
  case Map.lookup useAddr m.ldUseToDep of
    Just depMap -> return $ Map.lookup depAddr depMap
    Nothing -> return Nothing

storeLastDerefedVersion :: VertexAddr -> DependencyAddr -> VNode -> RM ()
storeLastDerefedVersion userAddr depAddr v = do
  m <- lastDerefs <$> getRMContext
  let depPairs = Map.findWithDefault Map.empty userAddr m.ldUseToDep
      newDepPairs = Map.insert depAddr v.version depPairs
      newLDUseToDep = Map.insert userAddr newDepPairs m.ldUseToDep

      usePairs = Map.findWithDefault Map.empty depAddr m.ldDepToUse
      newUsePairs = Map.insert userAddr v.version usePairs
      newLDDepToUse = Map.insert depAddr newUsePairs m.ldDepToUse

  debugInstStr
    "storeLastDerefedVersion"
    (vertexToAddr userAddr)
    ( do
        addrT <- tshow userAddr
        depAddrT <- tshow depAddr
        vT <- tshow v
        return $
          printf
            "store last derefed version for addr: %s, depAddr: %s, val: %s, version: %d"
            addrT
            depAddrT
            vT
            v.version
    )
  modifyRMContext $ \ctx -> ctx{lastDerefs = m{ldUseToDep = newLDUseToDep, ldDepToUse = newLDDepToUse}}

{- | Copy the value from the target address to the reference address.

It makes references that point to the value inside the target value point to the copied value.

All the values in the copied value will be put into the store with their addresses.
-}
copyVTermNode :: EvalAddr -> EvalAddr -> VTermNode -> VTermNode
copyVTermNode srcAddr dstAddr =
  posttravsVT
    ( \_ x ->
        case x of
          IsRef _ ref
            -- If the resolved ident address is inside the target value, then it should be redirected to the
            -- copied value.
            -- For example, {a: {x: 1, y: x}, b: a}. When we copy a to b, the reference in a should be
            -- redirected to the copied value of a, not the original a.
            | AbsoluteIdentAddr resIdentAddr <- ref.identLocator
            , srcAddr `isPrefix` resIdentAddr && resIdentAddr /= srcAddr ->
                let rest = trimPrefixAddr srcAddr resIdentAddr
                    -- Remove any reduction-local constraint arguments from the destination address.
                    normDstAddr = toReducedForm dstAddr
                    newIdentAddr = appendEvalAddr normDstAddr rest
                    newRef = ref{identLocator = AbsoluteIdentAddr newIdentAddr}
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
    _ -> throwFatal "fetchComprehBindingVal: comprehension binding not found"

lookupComprehBindingVal :: Int -> TextIndex -> Seq.Seq [(TextIndex, VNode)] -> Maybe VNode
lookupComprehBindingVal depth name bindings = do
  pairs <- bindings Seq.!? depth
  lookup name pairs
