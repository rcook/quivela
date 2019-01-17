-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
module Quivela
   -- * Quotations
  ( prog
  , prog'
  , prove
  , prove'
  , proveFailFast
  , proveFailFast'
  -- * Parsers.  Generally these will only be used by the quotations, but need to be in scope.
  , parseExpr
  , parseProofPart
  -- * Environment
  , emptyVerifyEnv
  , jobName
  , tempDir
  , writeAllVCsToFile
  -- * Proof steps
  , (≈)
  -- * Proof hints
  , ProofHint(Admit, NoAddressBijection, NoInfer, Note)
  , fieldEqual
  , fieldsEqual
  , fieldOppEqual
  , fieldsOppEqual
  , rewrite
  -- * Proof parts
  , ProofPart(Hint)
  ) where

import Quivela.Language
import Quivela.Parse
import Quivela.Prelude
import Quivela.QuasiQuote
import Quivela.SymEval

-- | Like '~~' but using a nicer-looking unicode operator instead.
(≈) :: a -> [a] -> [a]
x ≈ y = x : y

infixr 5 ≈

-- | A shorthand for rewriting using quivela terms written in concrete syntax.
-- Note: We can only use rewriting as a single proof hint.  The rewritten result
-- must be syntactically identical. No VCs are generated.  For example, you can't
-- rewrite then apply other hints in the same step.
rewrite :: String -> String -> ProofHint
rewrite e1 e2 = Rewrite (parseExpr e1) (parseExpr e2)
