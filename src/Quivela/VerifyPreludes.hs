-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell #-}

module Quivela.VerifyPreludes
  ( z3Prelude,
    z3PreludeCompiled
  ) where

import qualified Quivela.Util as Q
import Quivela.Prelude
import qualified System.IO as IO

-- This file defines the preludes for the z3 backend so we don't
-- need to worry about paths to these files (if they were placed as actual
-- files somewhere)
-- | Z3 encoding for quivela values and operations on them
z3Prelude :: IO String
z3Prelude = IO.readFile "src/Quivela/quivela.smt2"

z3PreludeCompiled :: (Monad m) => m String
z3PreludeCompiled = return $(Q.readFileCompileTime "quivela.smt2")
