module Semant.Resolver where

import Control.Monad (foldM)
import Control.Monad.Except (ExceptT (..), MonadError (..))
import Control.Monad.RWS (lift)
import Control.Monad.RWS.Strict (RWST)
import Control.Monad.State (gets, modify')
import Cursor
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Vector as V
import Debug.Trace (trace)
import Feature
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import StringIndex (
  HasTextIndexer (..),
  ShowWTIndexer (..),
  TextIndex,
  TextIndexer,
  getTextIndex,
 )
import Syntax.AST (getNodeLoc)
import Syntax.Token (Location)
import Text.Printf (printf)
import Value

resolve :: VCur -> RM VCur
resolve = return

resolve2 :: VCur -> RM VCur
resolve2 vc = do
  case vc.focus of
    IsStruct struct -> recordStructScope (vcAddr vc) struct
    IsCompreh _ comp -> recordComprehScope (vcAddr vc) comp
    _ -> return ()

  -- Visit sub-nodes to resolve any unresolved identifiers.
  let subFs = subNodes True vc
  uvc <-
    foldM
      ( \acc subSeg -> do
          liftEitherRM (goDownVCSegMust subSeg acc)
            >>= resolve
            >>= liftEitherRM . propUpVC
      )
      vc
      subFs

  -- Post process the focus node.
  case uvc.focus of
    -- Save the resolved struct fields to stub fields.
    IsStruct struct -> return $ mapVCFocus (setVN (VNStruct struct{stcStaticFieldBases = stcFields struct})) uvc
    -- IsRef sop (Reference (RefPath (RefIdentUnresolved sid ti inTopScope identType) sels)) -> do
    --   scopeAddr <- lookupIdentScopeAddr sid
    --   f <- case identType of
    --     ITField -> return $ mkStringFeature ti
    --     ITIterBinding -> return $ mkIterBindFeature ti
    --     _ -> mkLetFeature ti (Just sid)
    --   let
    --     identAddr = if inTopScope then addrFromList [f] else createRefFormAddr scopeAddr f
    --     newRef = Reference (RefPath (RefIdentResolved identAddr identType) sels)
    --     newMut = setOpInSOp (Ref newRef) sop
    --   return $ mapVCFocus (\t -> t{op = Just newMut}) uvc
    _ -> return uvc

type RM = RWST () () ResolveState (ExceptT String IO)

data ResolveState = ResolveState
  { scopes :: Map.Map Int ValAddr
  -- ^ scopes maps scope ids to their corresponding addresses.
  , tIndexer :: TextIndexer
  }

instance HasTextIndexer ResolveState where
  getTextIndexer = tIndexer
  setTextIndexer ti ts = ts{tIndexer = ti}

mapScopes :: (Map.Map Int ValAddr -> Map.Map Int ValAddr) -> ResolveState -> ResolveState
mapScopes f rs = rs{scopes = f rs.scopes}

initResolveState :: TextIndexer -> ResolveState
initResolveState ti = ResolveState{scopes = Map.empty, tIndexer = ti}

recordStructScope :: ValAddr -> Struct -> RM ()
recordStructScope addr struct = do
  scopes <- gets scopes
  case Map.lookup struct.stcID scopes of
    Just _ -> throwFatal $ printf "recordStructScope: struct scope with id %d already exists" struct.stcID
    Nothing -> modify' $ mapScopes (Map.insert struct.stcID addr)

-- | Record the comprehension scope ids and their addresses.
recordComprehScope :: ValAddr -> Comprehension -> RM ()
recordComprehScope addr Comprehension{args} = do
  scopes <- gets scopes
  foldM
    ( \_ (_, arg) -> do
        let
          cidM = case arg of
            -- ComprehArgFor sid _ _ _ -> Just sid
            -- ComprehArgLet sid _ _ -> Just sid
            _ -> Nothing
        case cidM of
          Nothing -> return ()
          Just cid -> case Map.lookup cid scopes of
            Just _ -> throwFatal $ printf "recordComprehScope: comprehension scope with id %d already exists" cid
            -- All comprehension scopes share the same address of their comprehension address.
            -- Comprehension will have a dynamically built up bindings.
            Nothing -> modify' $ mapScopes (Map.insert cid addr)
    )
    ()
    (zip [0 ..] (toList args))

lookupIdentScopeAddr :: Int -> RM ValAddr
lookupIdentScopeAddr sid = do
  scopes <- gets scopes
  case Map.lookup sid scopes of
    Just addr -> return addr
    Nothing -> throwFatal $ printf "lookupIdentScopeAddr: scope with id %d not found" sid

liftEitherRM :: Either String a -> RM a
liftEitherRM e = lift $ ExceptT $ return e

throwFatal :: (HasCallStack) => String -> RM a
throwFatal msg = throwError $ msg ++ "\n" ++ prettyCallStack callStack

{- | Create a reference address from a base address and a feature.

It normalizes the base address by converting stub field labels to normal string features.
-}
createRefFormAddr :: ValAddr -> Feature -> ValAddr
createRefFormAddr addr ft = normAddr $ appendSeg addr ft
 where
  normAddr = id

-- normAddr (ValAddr xs) =
--   ValAddr $
--     V.foldl
--       ( \acc f -> case fetchLabelType f of
--           StubFieldLabelType -> acc V.++ V.singleton (mkStringFeature (getTextIndexFromFeature f))
--           _ -> acc V.++ V.singleton f
--       )
--       V.empty
--       xs

-- recordStructScope :: ValAddr -> Struct -> RM (Either Val ())
-- recordStructScope addr struct = do
--   -- First push a new block for the struct scope.
--   modify' $ mapEnvs (pushBlock struct.stcID addr)
--   -- Add static fields to the current environment.
--   res1 <-
--     foldM
--       ( \acc ti -> case acc of
--           Left errVal -> return $ Left errVal
--           Right () -> do
--             -- The address of the field should not be stub.
--             let f = mkStringFeature ti
--             addNameToCurrentEnv ti ITField (createRefFormAddr addr f)
--       )
--       (Right ())
--       (Map.keys struct.stcStaticFieldBases)
--   -- Add bindings to the current environment.
--   res2 <-
--     foldM
--       ( \acc ti -> case acc of
--           Left errVal -> return $ Left errVal
--           Right () -> do
--             let f = mkFeature (getTextIndex ti) LetLabelType
--             -- ti might have suffixes, we need to get the prefix for the let binding.
--             namePrefix <- getLetIdentPrefix f
--             addNameToCurrentEnv namePrefix ITLetBinding (createRefFormAddr addr f)
--       )
--       res1
--       (Map.keys struct.stcBindings)

--   -- addrT <- tshow addr
--   -- envsT <- tshow =<< gets envs
--   -- trace (printf "In struct scope: addr=%s, envs=%s" (T.unpack addrT) (T.unpack envsT)) (return ())

--   return res2

-- leaveStructScope :: RM (Either Val ())
-- leaveStructScope = do
--   -- debugShowEnvs "leaving struct scope"

--   envs <- gets envs
--   let (poppedEnv, restEnvs) = popBlock envs
--   modify' $ mapEnvs (const restEnvs)
--   let unreferencedNames =
--         Map.keys $
--           Map.filter
--             ( \(_, identType, isReferenced) -> case identType of
--                 ITLetBinding -> not isReferenced
--                 _ -> False
--             )
--             poppedEnv.names
--   if null unreferencedNames
--     then return $ Right ()
--     else do
--       let firstName = head unreferencedNames
--       firstNameT <- tshow firstName
--       return $ Left $ mkBottomVal $ printf "unreferenced let clause let %s" (show firstNameT)

-- -- | Lookup the identifier in the current environments.
-- lookupIdentInScopes :: TextIndex -> Val -> RM (Either Val (ValAddr, RefIdentType))
-- lookupIdentInScopes identTI val = do
--   res <- lookupIdentInEnvs identTI
--   case res of
--     Just (_, addr, identType) -> return $ Right (addr, identType)
--     Nothing -> do
--       errMsg <- notFoundMsg identTI (getNodeLoc <$> origExpr val)
--       return $ Left $ mkBottomVal errMsg

-- notFoundMsg :: TextIndex -> Maybe Location -> RM String
-- notFoundMsg ident locM = do
--   idStr <- tshow ident
--   case locM of
--     Nothing -> return $ printf "reference %s is not found" (show idStr)
--     Just loc -> do return $ printf "reference %s is not found:\n\t%s" (show idStr) (show loc)

-- {- | Lookup the identifier in the environments.

-- Returns (isInTopEnv, address, identType) if found.
-- -}
-- lookupIdentInEnvs :: TextIndex -> RM (Maybe (Bool, ValAddr, RefIdentType))
-- lookupIdentInEnvs name = do
--   (Environments envs) <- gets envs
--   let (res, updatedEnvs) = lookupInStack (topEnvID envs) [] envs
--   modify' $ mapEnvs (const $ Environments updatedEnvs)
--   return res
--  where
--   topEnvID envs = case envs of
--     [] -> -1
--     (env : _) -> env.envid

--   lookupInStack _ acc [] = (Nothing, reverse acc)
--   lookupInStack tenvid acc (env : rest) =
--     case Map.lookup name env.names of
--       Just (v, t, _) ->
--         ( Just (env.envid == tenvid, v, t)
--         , reverse acc ++ markNameAsReferenced name env : rest
--         )
--       Nothing -> lookupInStack tenvid (env : acc) rest

-- checkIdentInEnvs :: TextIndex -> RefIdentType -> RM (Either Val ())
-- checkIdentInEnvs key identType = do
--   res <- lookupIdentInEnvs key
--   case res of
--     Just (isInTopEnv, _, targetIdentType)
--       -- If the identifier exists and the types conflict, return an error.
--       | isInTopEnv
--       , targetIdentType `elem` [ITLetBinding, ITIterBinding]
--       , identType `elem` [ITLetBinding, ITIterBinding] ->
--           Left <$> lbRedeclErr key
--       | targetIdentType == ITField && identType == ITLetBinding
--           || targetIdentType == ITLetBinding && identType == ITField ->
--           Left <$> aliasErr key
--     _ -> return $ Right ()

-- aliasErr :: TextIndex -> RM Val
-- aliasErr name = do
--   nameStr <- tshow name
--   return $ mkBottomVal $ printf "can not have both alias and field with name %s in the same scope" (show nameStr)

-- lbRedeclErr :: TextIndex -> RM Val
-- lbRedeclErr name = do
--   nameStr <- tshow name
--   return $ mkBottomVal $ printf "%s redeclared in same scope" (show nameStr)

-- addNameToCurrentEnv :: TextIndex -> RefIdentType -> ValAddr -> RM (Either Val ())
-- addNameToCurrentEnv ti identType addr = do
--   checked <- checkIdentInEnvs ti identType
--   case checked of
--     Left errVal -> return $ Left errVal
--     Right _ -> do
--       modify' $ mapEnvs $ addName ti
--       return $ Right ()
--  where
--   addName name (Environments envs) = case envs of
--     [] -> Environments []
--     (env : rest) -> Environments $ env{names = Map.insert name (addr, identType, False) env.names} : rest

-- liftEitherRM :: Either String a -> RM a
-- liftEitherRM e = lift $ ExceptT $ return e

-- debugShowEnvs :: String -> RM ()
-- debugShowEnvs msg = do
--   envsT <- tshow =<< gets envs
--   trace (printf "In struct scope: %s envs=%s" msg (T.unpack envsT)) (return ())

-- data ResolveState = ResolveState
--   { envs :: Environments
--   , tIndexer :: TextIndexer
--   }

-- instance HasTextIndexer ResolveState where
--   getTextIndexer = tIndexer
--   setTextIndexer ti ts = ts{tIndexer = ti}

-- mapEnvs :: (Environments -> Environments) -> ResolveState -> ResolveState
-- mapEnvs f rs = rs{envs = f rs.envs}

-- -- | Environments is a stack of environments that is used to resolve identifiers.
-- newtype Environments = Environments
--   { getEnvs :: [Environment]
--   -- ^ It is a stack of pairs of address of a scope and the set of identifiers defined in that scope.
--   }
--   deriving (Eq)

-- instance Show Environments where
--   show (Environments envs) = "Envs[" ++ concatMap (\e -> show e ++ "; ") envs ++ "]"

-- instance ShowWTIndexer Environments where
--   tshow (Environments envs) = do
--     envStrs <- mapM tshow envs
--     return $ T.pack $ "Envs[" ++ concatMap (\e -> T.unpack e ++ "; ") envStrs ++ "]"

-- data Environment = Environment
--   { envAddr :: ValAddr
--   , envid :: !Int
--   , names :: Map.Map TextIndex (ValAddr, RefIdentType, Bool)
--   -- ^ names maps identifiers to
--   --  (1) their addresses,
--   --  (2) their types (field, let binding, or iter binding),
--   --  (3) a boolean indicating whether it is referenced.
--   -- Notice the identifiers should not have suffix for let bindings.
--   }
--   deriving (Eq)

-- instance Show Environment where
--   show (Environment addr envid names) = printf "Env(id=%d, addr=%s, names=[%s])" envid (show addr) nameStr
--    where
--     nameStr :: String
--     nameStr =
--       concatMap
--         ( \(k, (v, t, r)) ->
--             printf "%s->(%s,%s,%s); " (show k) (show v) (show t) (show r)
--         )
--         (Map.toList names)

-- instance ShowWTIndexer Environment where
--   tshow (Environment addr envid names) = do
--     envAddrT <- tshow addr
--     nameStrs <-
--       mapM
--         ( \(k, (v, t, r)) -> do
--             kT <- tshow k
--             vT <- tshow v
--             return $ T.pack $ printf "%s->(%s,%s,%s); " (T.unpack kT) (T.unpack vT) (show t) (show r)
--         )
--         (Map.toList names)
--     return $ T.pack $ printf "Env(id=%d, addr=%s, names=[%s])" envid (T.unpack envAddrT) (T.unpack $ T.concat nameStrs)

-- emptyEnvironments :: Environments
-- emptyEnvironments = Environments []

-- markNameAsReferenced :: TextIndex -> Environment -> Environment
-- markNameAsReferenced key env = env{names = Map.adjust markRef key env.names}
--  where
--   markRef (addr, identType, _) = (addr, identType, True)

-- pushBlock :: Int -> ValAddr -> Environments -> Environments
-- pushBlock envid addr (Environments envs) =
--   Environments $ Environment{envAddr = addr, names = Map.empty, envid = envid} : envs

-- popBlock :: Environments -> (Environment, Environments)
-- popBlock (Environments envs) = case envs of
--   [] -> error "popBlock: empty environment stack"
--   (env : rest) -> (env, Environments rest)
