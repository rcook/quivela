-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell #-}

module Quivela.QuasiQuote
  ( prog
  , prog'
  , prove
  , prove'
  , rewrite
  ) where

import qualified Control.Arrow
import qualified Control.Monad as M
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as Q
import qualified System.Timer as Timer

import qualified Quivela.Language as L
import qualified Quivela.Parse as P
import qualified Quivela.SymEval as E
import qualified Quivela.Verify as V

-- | Construct a term that parses the given string as a quivela expression
-- and return it as a 'ProofPart'.
quivelaParse :: String -> TH.ExpQ
quivelaParse s = [|parseProofPart $ $(TH.litE $ TH.StringL s)|]

-- | Same as 'quivelaParse' but without the 'ProofPart' wrapper.
quivelaParse' :: String -> TH.ExpQ
quivelaParse' s = [|parseExpr $(TH.litE $ TH.StringL s)|]

-- | A quasiquoter for expressions as proof steps.
prog :: Q.QuasiQuoter
prog = Q.QuasiQuoter quivelaParse undefined undefined undefined

-- | Another quasiquoter for programs outside of proof steps.
prog' :: Q.QuasiQuoter
prog' = Q.QuasiQuoter quivelaParse' undefined undefined undefined

-- | Run the given quivela proof at compile time. We allow running this
-- at compile time to avoid having to manually invoke the verification
-- after loading the file into ghci.
prove :: E.VerifyEnv -> L.Expr -> [L.ProofPart] -> TH.Q [TH.Dec]
prove env prefix steps = do
  unverified <- TH.runIO $ prove' env prefix steps
  M.when (unverified > 0) $
    TH.reportError (show unverified ++ " unverified VCs")
  return []

-- | A non-compile-time version of 'prove'.
prove' :: E.VerifyEnv -> L.Expr -> [L.ProofPart] -> IO Int
prove' env prefix steps = do
  (t, results) <- Timer.time $ mapM doCheck (V.toSteps steps)
  return $ sum results
  where
    doCheck = V.runVerify env . V.proveStep prefix

-- | A shorthand for rewriting using quivela terms written in concrete syntax.
rewrite :: String -> String -> L.ProofHint
rewrite e1 e2 = L.Rewrite (P.parseExpr e1) (P.parseExpr e2)

heredocExpr :: String -> TH.ExpQ
heredocExpr s = [|$(TH.litE $ TH.StringL s)|]

-- | QuasiQuoter for multi-line string literals
heredoc :: Q.QuasiQuoter
heredoc = Q.QuasiQuoter heredocExpr undefined undefined undefined
