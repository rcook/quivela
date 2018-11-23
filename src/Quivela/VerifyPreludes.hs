{-# LANGUAGE TemplateHaskell #-}

module Quivela.VerifyPreludes
  ( z3Prelude
  ) where

import qualified Quivela.Util as U

-- This file defines the preludes for the z3 backend so we don't
-- need to worry about paths to these files (if they were placed as actual
-- files somewhere)
-- | Z3 encoding for quivela values and operations on them
z3Prelude :: String
z3Prelude = $(U.readFileCompileTime "quivela.smt2")
