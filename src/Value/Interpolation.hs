module Value.Interpolation where

data IplSeg = IplSegExpr Int | IplSegStr String
  deriving (Eq, Show)

data Interpolation t = Interpolation
  { itpSegs :: [IplSeg]
  , itpExprs :: [t]
  , itpValue :: Maybe t
  }
  deriving (Eq, Show)

emptyInterpolation :: Interpolation t
emptyInterpolation = Interpolation [] [] Nothing