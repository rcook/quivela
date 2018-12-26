-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE TemplateHaskell #-}

module Quivela.QuasiQuote
  ( prog
  , prog'
  , prove
  , prove'
  , proveFailFast
  , rewrite
  ) where

import qualified Control.Monad as Monad
import qualified Data.List as L
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as TH
import qualified Quivela.Language as Q
import qualified Quivela.Parse as Q
import Quivela.Prelude
import qualified Quivela.SymEval as Q
import qualified Quivela.Verify as Q
import qualified System.Timer as Timer

-- | Construct a term that parses the given string as a quivela expression
-- and return it as a 'ProofPart'.
quivelaParse :: String -> TH.ExpQ
quivelaParse s = [|parseProofPart $ $(TH.litE $ TH.StringL s)|]

-- | Same as 'quivelaParse' but without the 'ProofPart' wrapper.
quivelaParse' :: String -> TH.ExpQ
quivelaParse' s = [|parseExpr $(TH.litE $ TH.StringL s)|]

-- | A quasiquoter for expressions as proof steps.
prog :: TH.QuasiQuoter
prog = TH.QuasiQuoter quivelaParse undefined undefined undefined

-- | Another quasiquoter for programs outside of proof steps.
prog' :: TH.QuasiQuoter
prog' = TH.QuasiQuoter quivelaParse' undefined undefined undefined

-- | Run the given quivela proof at compile time. We allow running this
-- at compile time to avoid having to manually invoke the verification
-- after loading the file into ghci.
prove :: Q.VerifyEnv -> Q.Expr -> [Q.ProofPart] -> TH.Q [TH.Dec]
prove env prefix steps = do
  unverified <- TH.runIO $ prove' env prefix steps
  Monad.when (unverified > 0) $
    TH.reportError (show unverified ++ " unverified VCs")
  return []

-- | A non-compile-time version of 'prove'.
prove' :: Q.VerifyEnv -> Q.Expr -> [Q.ProofPart] -> IO Int
prove' env prefix steps = do
  (_, results) <- Timer.time $ Monad.mapM doCheck (Q.toSteps steps)
  return $ L.sum results
  where
    doCheck = Q.runVerify env . Q.proveStep prefix

-- | Fail at first failure.  Return 0 if all succeed, 1 if there's a failure
proveFailFast :: Q.VerifyEnv -> Q.Expr -> [Q.ProofPart] -> IO Int
proveFailFast env prefix steps =
  Monad.foldM
    (\c s ->
       if c > 0
         then return c
         else doCheck s)
    0
    (Q.toSteps steps)
  where
    doCheck = Q.runVerify env . Q.proveStep prefix

-- | A shorthand for rewriting using quivela terms written in concrete syntax.
rewrite :: String -> String -> Q.ProofHint
rewrite e1 e2 = Q.Rewrite (Q.parseExpr e1) (Q.parseExpr e2)
