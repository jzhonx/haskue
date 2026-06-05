module Value.Export.JSON where

import Control.Monad (foldM)
import Control.Monad.Except (Except)
import Control.Monad.RWS.Strict (RWST, runRWST)
import Data.Aeson (ToJSON (..), Value)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import Exception (throwErrSt)
import StringIndex (ShowWTIndexer (..), TextIndexer)
import Text.Printf (printf)
import Value.List
import Value.Struct
import Value.Val

newtype BuildConfig = BuildConfig {isDebug :: Bool}

type JM = RWST BuildConfig () TextIndexer (Except String)

buildJSON :: VNode -> TextIndexer -> Except String (Value, TextIndexer)
buildJSON t tier = do
  (a, s, _) <- runRWST (buildJSONExt t) (BuildConfig False) tier
  return (a, s)

buildJSONExt :: VNode -> JM Value
buildJSONExt v = case value v of
  VAtom atom -> return $ toJSON atom
  VBottom _ -> throwErrSt "bottom should be eliminated before JSON export"
  VBounds _ -> incompleteErr v
  VTop -> incompleteErr v
  VStruct stc -> buildJSONStruct stc
  VList l -> do
    let elems = V.toList l.final
    jsonElems <- mapM (buildJSONExt . mkValVN) elems
    return $ toJSON jsonElems
  VDisj dj | Just df <- rtrDisjDefVal dj -> buildJSONExt (mkValVN df)
  _ -> do
    vType <- Value.Val.showValueType (value v)
    throwErrSt $ printf "unsupported value for JSON export %s" vType

buildJSONStruct :: Struct -> JM Value
-- Handle embedded values first.
buildJSONStruct (Struct{stcEmbedVal = Just ev}) = buildJSONExt (mkValVN ev)
buildJSONStruct stc = do
  let fields = stcFields stc
  objFields <- foldM buildField Map.empty (Map.toList fields)
  return $ toJSON objFields
 where
  buildField acc (i, field) = do
    key <- tshow i
    valJSON <- buildJSONExt field.ssfValue
    return $ Map.insert key valJSON acc

incompleteErr :: VNode -> JM a
incompleteErr v = do
  t <- oneLinerStringOfVNode v
  throwErrSt $ printf "incomplete value %s" t