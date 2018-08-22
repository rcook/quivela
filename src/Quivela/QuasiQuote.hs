{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module Quivela.QuasiQuote where

import Control.Arrow
import Control.Monad
import Language.Haskell.TH as TH hiding (Type)
import Language.Haskell.TH.Quote
import System.Microtimer

import Quivela.Parse
import Quivela.SymEval
import Quivela.Verify

-- | Construct a term that parses the given string as a quivela expression
-- and return it as a 'ProofPart'.
quivelaParse :: String -> TH.ExpQ
quivelaParse s = [| Prog $ $(quivelaParse' s) |]

-- | Same as 'quivelaParse' but without the 'ProofPart' wrapper.
quivelaParse' :: String -> TH.ExpQ
quivelaParse' s = [| parseExpr $(litE $ TH.StringL s) |]

-- | A quasiquoter for expressions as proof steps.
prog :: QuasiQuoter
prog = QuasiQuoter quivelaParse undefined undefined undefined

-- | Another quasiquoter for programs outside of proof steps.
prog' :: QuasiQuoter
prog' = QuasiQuoter quivelaParse' undefined undefined undefined

-- | Run the given quivela proof at compile time. We allow running this
-- at compile time to avoid having to manually invoke the verification
-- after loading the file into ghci.
prove :: SymEvalEnv -> Expr -> [ProofPart] -> Q [Dec]
prove env prefix steps = do
  unverified <- runIO $ prove' env prefix steps
  when (unverified > 0) $ reportError (show unverified ++ " unverified VCs")
  return []

-- | A non-compile-time version of 'prove'.
prove' :: SymEvalEnv -> Expr -> [ProofPart] -> IO Int
prove' env prefix steps = do
  (t, results) <- time $ mapStepsM doCheck (toSteps steps)
  debug $ "Total verification time: " ++ formatSeconds t
  return $ sum results
  where doCheck invs lhs rhs = do
          remaining <- runVerify (checkEqv True prefix invs lhs rhs) env
          return . sum . map (length . snd) $ remaining


-- | A shorthand for rewriting using quivela terms written in concrete syntax.
rewrite :: String -> String -> Invariant
rewrite e1 e2 = Rewrite (parseExpr e1) (parseExpr e2)

-- | Convenience function for constructing a universal invariant from a quivela
-- term in concrete syntax.
univInvariant :: [(Var, Type)] -> String -> Invariant
univInvariant formals e = UnivInvariant formals (parseExpr e)
