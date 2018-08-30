{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
import Control.Applicative
import Control.DeepSeq
import Control.Exception
import qualified Data.Map as M
import Test.HUnit

import Quivela
import Quivela.Examples

assertVerified :: String -> Expr -> [ProofPart] -> Assertion
assertVerified msg prefix proof = do
  clearCache
  res <- prove' emptyVerifyEnv prefix proof
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
assertEvalError msg e = assertError msg . runVerify emptyVerifyEnv $ symEval (e, emptyCtx, [])

assertEvalResult :: String -> Expr -> Value -> Assertion
assertEvalResult msg e v = do
  (res, _, _) <- singleResult <$> (runVerify emptyVerifyEnv $ (symEval (e, emptyCtx, [])))
  assertEqual msg res v

assertVerifyError :: String -> Expr -> [ProofPart] -> Assertion
assertVerifyError msg prefix proof = assertError msg $ prove' emptyVerifyEnv prefix proof

assertParses :: String -> String -> Expr -> Assertion
assertParses msg progText e = assertEqual msg (parseExpr progText) e

parserTests = map (TestCase . uncurry3 assertParses) $
  [ ("integer constants", "23", EConst (VInt 23))
  , ("empty map literal", "map", EConst (VMap M.empty))
  , ("unqualified function call", "f(1)"
    ,ECall {_callObj = EConst VNil, _callName = "f", _callArgs = [EConst (VInt 1)]})
  , ("tuple with comparisons", "<a, (b > c)>"
    ,ETuple [EVar "a",ECall {_callObj = EConst VNil, _callName = ">", _callArgs = [EVar "b",EVar "c"]}])
  , ("& is right-assoc", "a & b & c"
    ,ECall {_callObj = EConst VNil, _callName = "&", _callArgs = [EVar "a",ECall {_callObj = EConst VNil, _callName = "&", _callArgs = [EVar "b",EVar "c"]}]})
  , ("& and ,", "a & b , c & d"
    ,ECall {_callObj = EConst VNil, _callName = "&", _callArgs = [EVar "a",ESeq (EVar "b") (ECall {_callObj = EConst VNil, _callName = "&", _callArgs = [EVar "c",EVar "d"]})]})
  , (", is right-assoc", "a , b , c", ESeq (EVar "a") (ESeq (EVar "b") (EVar "c")))
  , ("& and , and | mix correctly",  "a | b , c & d",
      ECall {_callObj = EConst VNil, _callName = "|", _callArgs = [EVar "a",ESeq (EVar "b") (ECall {_callObj = EConst VNil, _callName = "&", _callArgs = [EVar "c",EVar "d"]})]})
  , ("associativity of ! and |", "!a | b",
     ECall {_callObj = EConst VNil, _callName = "|", _callArgs = [ECall {_callObj = EConst VNil, _callName = "!", _callArgs = [EVar "a"]},EVar "b"]})
  , ("projections, indexing, and method calls in one expression"
    ,"x[1].field.mtd(1, 2)"
    ,ECall {_callObj = EProj (EIdx (EVar "x") (EConst (VInt 1))) "field", _callName = "mtd", _callArgs = [EConst (VInt 1),EConst (VInt 2)]})
  , ("call on new in parentheses"
    ,"(new () { method f(x: int) { x = <1, 2> } }).f(7)"
    ,ECall {_callObj = ENew {_newFields = [], _newBody = ESeq (EMethod {_emethodName = "f", _emethodArgs = [("x",TInt)], _emethodBody = EAssign {_lhs = EVar "x", _rhs = ETuple [EConst (VInt 1),EConst (VInt 2)]}, _eisInvariant = False}) ENop}, _callName = "f", _callArgs = [EConst (VInt 7)]})

  ]

tests :: Test
tests = TestList $ parserTests ++
  [ TestCase $ assertEvalError "assigning to constant variable" assignConst
  , TestCase $ assertEvalError "assigning to constant variable" assignConst'
  , TestCase $ assertEvalError "ill-typed assignment to object field" illTypedAssign
  , TestCase $ assertEvalError "ill-typed assignment to object field" illTypedAssign'
  , TestCase $ assertEvalError "ill-typed assignment to method parameter" illTypedParamAssign
  , TestCase $ assertEvalResult "multiple indexing expressions in sequence" doubleIdx (VInt 5)
  , TestCase $ assertEvalResult "nested object field lookups" doubleFieldDeref (VInt 5)
  , TestCase $ assertEvalResult "post-increment on object field" incrementFieldDeref  (VInt 1)
  , TestCase $ assertEvalResult "type declarations with parameters" typedeclTest (VInt 5)
  , TestCase $ assertVerified "& well-behaved" nop andExample
  , TestCase $ assertVerified "simple equality invariant" nop eqInvExample
  , TestCase $ assertVerified "simple const annotation" nop constExample
  , TestCase $ assertVerified "addition is commutative and 0 is identity" nop addExample
  , TestCase $ assertVerified "multiplication example" nop mulExample
  , TestCase $ assertVerified "arithmetic example" nop arithExample
  , TestCase $ assertVerified "post-increment example 1" nop postIncrExample3
  , TestCase $ assertVerified "post-increment example 2" nop postIncrExample2
  , TestCase $ assertVerified "post-increment example 3" nop postIncrExample1
  , TestCase $ assertVerified "post-increment in a map index" nop postIncrementInMap
  , TestCase $ assertVerified "less-than operator example" nop leExample
  , TestCase $ assertVerified "call on symbolic object" nop symcallTest
  , TestCase $ assertVerified "call on symbolic map value" nop symcallMap
  , TestCase $ assertVerified "object maps with an invariant" nop symcallMapParam
  , TestCase $ assertVerifyError "verification should detect extraneous methods on one side" nop extraMethodsTest
  ]

main :: IO ()
main = runTestTT tests >> return ()
