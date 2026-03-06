module Value.Val where

data ValNode
data Val

-- class VTerm a where
--   vtmapT :: (Val -> Val) -> a -> a
--   vtmapQ :: (Val -> r) -> a -> [r]
--   vtmapM :: (Monad m) => (Val -> m Val) -> a -> m a