module Value.Export.JSON where

import Control.Monad (foldM)
import Control.Monad.Except (Except)
import Control.Monad.RWS.Strict (RWST, runRWST)
import Data.Aeson (ToJSON (..), Value, object)
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

buildJSON :: Val -> TextIndexer -> Except String (Value, TextIndexer)
buildJSON t tier = do
  (a, s, _) <- runRWST (buildJSONExt t) (BuildConfig False) tier
  return (a, s)

buildJSONExt :: Val -> JM Value
buildJSONExt v = case valNode v of
  VNAtom atom -> return $ toJSON atom
  VNBottom _ -> throwErrSt "bottom should be eliminated before JSON export"
  VNBounds _ -> incompleteErr v
  VNTop -> incompleteErr v
  VNStruct stc -> buildJSONStruct stc
  VNList l -> do
    let elems = V.toList l.final
    jsonElems <- mapM buildJSONExt elems
    return $ toJSON jsonElems
  _ -> throwErrSt "unsupported value for JSON export"

buildJSONStruct :: Struct -> JM Value
-- Handle embedded values first.
buildJSONStruct (Struct{stcEmbedVal = Just ev}) = buildJSONExt ev
buildJSONStruct stc = do
  let fields = stcFields stc
  objFields <- foldM buildField Map.empty (Map.toList fields)
  return $ toJSON objFields
 where
  buildField acc (i, field) = do
    key <- tshow i
    valJSON <- buildJSONExt field.ssfValue
    return $ Map.insert key valJSON acc

incompleteErr :: Val -> JM a
incompleteErr v = do
  t <- oneLinerStringOfVal v
  throwErrSt $ printf "incomplete value %s" t