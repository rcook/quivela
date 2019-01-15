-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell #-}

module Quivela.VerifyPreludes
  ( z3Prelude
  , z3PreludeCompiled
  ) where

import Quivela.Prelude
import Quivela.Resources (quivelaSmt2Content, quivelaSmt2Path)
import qualified System.IO as IO

-- This file defines the preludes for the z3 backend so we don't
-- need to worry about paths to these files (if they were placed as actual
-- files somewhere)
-- | Z3 encoding for quivela values and operations on them
z3Prelude :: IO String
z3Prelude = IO.readFile $quivelaSmt2Path

z3PreludeCompiled :: String
z3PreludeCompiled = quivelaSmt2Content
