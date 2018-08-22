{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
import Control.Applicative
import Control.DeepSeq
import Control.Exception
import Test.HUnit

import Quivela
import Quivela.Examples

assertVerified :: String -> Expr -> [ProofPart] -> Assertion
assertVerified msg prefix proof = do
  clearCache
  res <- prove' prefix proof
  assertEqual msg 0 res

assertError :: String -> IO a -> Assertion
assertError msg x = do
  errored <- catch (x >> pure False) handler
  if errored then
      assertFailure $ "Should have failed: " ++ msg
  else
      assertBool "true" True
  where
     handler :: SomeException -> IO Bool
     handler _ = pure True

assertEvalError :: String -> Expr -> Assertion
assertEvalError msg e = assertError msg $ symEval' (e, emptyCtx, [])

tests :: Test
tests = TestList
  [ TestCase $ assertVerified "& well-behaved" nop andExample
  , TestCase $ assertVerified "simple equality invariant" nop eqInvExample
  , TestCase $ assertVerified "simple const annotation" nop constExample
  , TestCase $ assertEvalError "assigning to constant variable" assignConst
  , TestCase $ assertEvalError "assigning to constant variable" assignConst'
  , TestCase $ assertEvalError "ill-typed assignment to object field" illTypedAssign
  , TestCase $ assertEvalError "ill-typed assignment to object field" illTypedAssign'
  ]

main :: IO ()
main = runTestTT tests >> return ()
