-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE ScopedTypeVariables #-}

-- This module is slightly generalized from
-- http://hackage.haskell.org/package/microtimer
module System.Timer
  ( time
  , time_
  , time'
  , formatSeconds
  ) where

import Control.Monad (liftM)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Time.Clock.POSIX (getPOSIXTime)
import Prelude
import Text.Printf (printf)

time :: MonadIO m => m a -> m (Double, a)
time act = do
  start <- liftIO getTime
  result <- act
  end <- liftIO getTime
  let !delta = end - start
  return (delta, result)

time_ :: MonadIO m => m a -> m Double
time_ act = fst `liftM` (time act)

formatSeconds :: Double -> String
formatSeconds k
  | k < 0 = '-' : formatSeconds (-k)
  | k >= 1 = k `with` "s"
  | k >= 1e-3 = (k * 1e3) `with` "ms"
  | k >= 1e-6 = (k * 1e6) `with` "us"
  | k >= 1e-9 = (k * 1e9) `with` "ns"
  | k >= 1e-12 = (k * 1e12) `with` "ps"
  | otherwise = printf "%g s" k
  where
    with (t :: Double) (u :: String)
      | t >= 1e9 = printf "%.4g %s" t u
      | t >= 1e6 = printf "%.0f %s" t u
      | t >= 1e5 = printf "%.1f %s" t u
      | t >= 1e4 = printf "%.2f %s" t u
      | t >= 1e3 = printf "%.3f %s" t u
      | t >= 1e2 = printf "%.4f %s" t u
      | t >= 1e1 = printf "%.5f %s" t u
      | otherwise = printf "%.6f %s" t u

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

time' :: MonadIO m => m a -> m a
time' action = do
  (t, res) <- time action
  liftIO $ putStrLn (formatSeconds t)
  return res
