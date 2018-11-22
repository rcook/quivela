{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module Quivela.VerifyPreludes where

import Language.Haskell.TH as TH hiding (Type)
import Language.Haskell.TH.Quote
import Quivela.Util

-- This file defines the preludes for the z3 and dafny backends so we don't
-- need to worry about paths to these files (if they were placed as actual
-- files somewhere)
-- | Z3 encoding for quivela values and operations on them
z3Prelude :: String
z3Prelude = $(readFileCompileTime "quivela.smt2")

-- | Dafny encoding for quivela values and operations on them
dafnyPrelude :: String
dafnyPrelude = $(readFileCompileTime "quivela.dfy")
