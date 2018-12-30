-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
module Quivela
   -- * Quotations
  ( prog
  , prog'
  , prove
  , prove'
  -- * Parsers.  Generally these will only be used by the quotations, but need to be in scope.
  , parseExpr
  , parseProofPart
  -- * Environment
  , emptyVerifyEnv
  -- * Proof steps
  , (≈)
  -- * Proof hints
  , ProofHint(Admit, NoAddressBijection, NoInfer, Note)
  , ProofPart(Hint)
  , fieldEqual
  , fieldsEqual
  , rewrite
  ) where

import Quivela.Language
import Quivela.Parse
import Quivela.Prelude
import Quivela.QuasiQuote
import Quivela.SymEval
import Quivela.Verify

-- | Like '~~' but using a nicer-looking unicode operator instead.
(≈) :: a -> [a] -> [a]
x ≈ y = x : y

infixr 5 ≈

-- | A shorthand for rewriting using quivela terms written in concrete syntax.
rewrite :: String -> String -> ProofHint
rewrite e1 e2 = Rewrite (parseExpr e1) (parseExpr e2)
