{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

module Util.Format where

import qualified Data.Text as T
import StringIndex (ShowWTIndexer (..), TextIndexerMonad)
import Text.Printf (printf)

data MSPrintfArg = forall a. (ShowWTIndexer a) => MSPrintfArg a

instance Show MSPrintfArg where
  show (MSPrintfArg x) = show x

instance ShowWTIndexer MSPrintfArg where
  tshow (MSPrintfArg x) = tshow x

packFmtA :: (ShowWTIndexer a) => a -> MSPrintfArg
packFmtA = MSPrintfArg

msprintf :: (TextIndexerMonad s m) => String -> [MSPrintfArg] -> m T.Text
msprintf fmt as = do
  ts <- mapM tshow as
  let fmtT = T.pack fmt
  case length ts of
    0 -> return fmtT
    1 -> return $ T.pack $ printf (T.unpack fmtT) (T.unpack $ head ts)
    2 -> return $ T.pack $ printf (T.unpack fmtT) (T.unpack $ ts !! 0) (T.unpack $ ts !! 1)
    3 -> return $ T.pack $ printf (T.unpack fmtT) (T.unpack $ ts !! 0) (T.unpack $ ts !! 1) (T.unpack $ ts !! 2)
    4 ->
      return $
        T.pack $
          printf (T.unpack fmtT) (T.unpack $ ts !! 0) (T.unpack $ ts !! 1) (T.unpack $ ts !! 2) (T.unpack $ ts !! 3)
    _ -> return $ T.pack $ printf "%s %s" (fmt ++ "(more args...)") (show ts)
