{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
import Control.Applicative
import qualified Control.DeepSeq as DS
import Control.Exception
import qualified Data.Map as M
import Test.HUnit

import Quivela
import Quivela.Examples

assertVerified :: String -> Expr -> Proof -> Assertion
assertVerified msg prefix proof = do
  clearCache
  res <- prove' emptyVerifyEnv prefix proof
  assertEqual msg 0 res

assertError :: String -> IO a -> Assertion
assertError msg x = do
  errored <- fmap DS.force $ catch (x >> pure False) handler
  if not errored then
      assertFailure $ "Should have failed: " ++ msg
  else
      assertBool "true" True
  where
     handler :: SomeException -> IO Bool
     handler _ = do
       pure True

assertEvalError :: String -> Expr -> Assertion
assertEvalError msg e = assertError msg . runVerify emptyVerifyEnv $ symEval (e, emptyCtx, [])

assertEvalResult' :: String -> Context -> Expr -> Value -> Assertion
assertEvalResult' msg ctx e v = do
  (res, _, _) <- singleResult <$> (runVerify emptyVerifyEnv $ (symEval (e, ctx, [])))
  assertEqual msg res v

assertEvalResult :: String -> Expr -> Value -> Assertion
assertEvalResult msg e v = assertEvalResult' msg emptyCtx e v

assertVerifyError :: String -> Expr -> Proof -> Assertion
assertVerifyError msg prefix proof = assertError msg $ prove' emptyVerifyEnv prefix proof

assertParses :: String -> String -> Expr -> Assertion
assertParses msg progText e = assertEqual msg (parseExpr progText) e

doesntVerify :: String -> Expr -> Proof -> Assertion
doesntVerify msg prefix proof = do
  remaining <- prove' emptyVerifyEnv prefix proof
  assertBool msg (remaining > 0)

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
    ,ECall {_callObj = ENew {_newFields = [], _newBody = ESeq (EMethod {_emethodName = "f", _emethodArgs = [("x",TInt)], _emethodBody = EAssign {_lhs = EVar "x", _rhs = ETuple [EConst (VInt 1),EConst (VInt 2)]}, _emethodKind = NormalMethod}) ENop}, _callName = "f", _callArgs = [EConst (VInt 7)]})
  , ("if expression with braces", "if (1) { 3 } else { a + b }",
     EIf (EConst (VInt 1)) (EConst (VInt 3)) (ECall {_callObj = EConst VNil, _callName = "+", _callArgs = [EVar "a",EVar "b"]}))
  , ("if without braces", "if (x < y) a + b else 1+2",
     EIf (ECall {_callObj = EConst VNil, _callName = "<", _callArgs = [EVar "x",EVar "y"]}) (ECall {_callObj = EConst VNil, _callName = "+", _callArgs = [EVar "a",EVar "b"]}) (ECall {_callObj = EConst VNil, _callName = "+", _callArgs = [EConst (VInt 1),EConst (VInt 2)]}))
  ]

tests :: Test
tests = TestList $ parserTests ++ invalidCases ++
  [ TestCase $ assertEvalError "assigning to constant variable" assignConst
  , TestCase $ assertEvalError "assigning to constant variable" assignConst'
  , TestCase $ assertEvalError "ill-typed assignment to object field" illTypedAssign
  , TestCase $ assertEvalError "ill-typed assignment to object field" illTypedAssign'
  , TestCase $ assertEvalError "ill-typed assignment to method parameter" illTypedParamAssign
  , TestCase $ assertEvalError "ill-typed assignment using object type" illTypedConstrAssign
  , TestCase $ assertEvalError "ill-typed object creation" illTypedObjectCreation
  , TestCase $ assertEvalError "ill-typed object creation using constructor" illTypedObjectCreationNamed
  , TestCase $ assertEvalResult "multiple indexing expressions in sequence" doubleIdx (VInt 5)
  , TestCase $ assertEvalResult "nested object field lookups" doubleFieldDeref (VInt 5)
  , TestCase $ assertEvalResult "post-increment on object field" incrementFieldDeref  (VTuple [VInt 1, VInt 2])
  , TestCase $ assertEvalResult "type declarations with parameters" typedeclTest (VInt 5)
  , TestCase $ assertEvalResult "Addresses can be used as symbolic values" addressesSymbolic (Sym (Add (Sym (Ref 1)) (Sym (Ref 2))))
  , TestCase $ assertEvalResult' "Decreasing allocation strategy should yield negative addresses"
                 (emptyCtx { _ctxAllocStrategy = Decrease }) (parseExpr "<new() {}, new() {}>") (VTuple [Sym {_symVal = Ref (-1)},Sym {_symVal = Ref (-2)}])
  , TestCase $ assertEvalResult' "Decreasing allocation allows allocating objects in methods" emptyCtxRHS decreaseAlloc
               (VInt 1)
  , TestCase $ assertVerifyError "verification should detect extraneous methods on one side" nop extraMethodsTest
  , TestCase $ doesntVerify "if expression equivalence differing on one branch" nop ifEqvFalse
  , TestCase $ assertVerified "<= works" nop leTaut
  , TestCase $ assertVerified "& well-behaved" nop andExample
  , TestCase $ assertVerified "simple equality invariant" nop eqInvExample
  , TestCase $ assertVerified "simple const annotation" nop constExample
  , TestCase $ assertVerified "addition is commutative and 0 is identity" nop addExample
  , TestCase $ assertVerified "multiplication example" nop mulExample
  , TestCase $ assertVerified "arithmetic example" nop arithExample
  , TestCase $ assertVerified "assignment to local variable" nop assignAnd
  , TestCase $ assertVerified "tupling never returns 0" nop tuplingAnd
  , TestCase $ assertVerified "if-else with symbolic condition" nop ifSymbolic
  , TestCase $ assertVerified "if-else with same value in both branches" nop ifSimp
  , TestCase $ assertVerified "if-else with true guard" nop ifConcreteTrue
  , TestCase $ assertVerified "if-else with false guard" nop ifConcreteFalse
  , TestCase $ assertVerified "post-increment example 1" nop postIncrExample3
  , TestCase $ assertVerified "post-increment example 2" nop postIncrExample2
  , TestCase $ assertVerified "post-increment example 3" nop postIncrExample1
  , TestCase $ assertVerified "post-increment in a map index" nop postIncrementInMap
  , TestCase $ assertVerified "less-than operator example" nop leExample
  , TestCase $ assertVerified "Z(..) is idempotent" nop zIdempotent
  , TestCase $ assertVerified "call on symbolic object" nop symcallTest
  , TestCase $ assertVerified "call on symbolic map value" nop symcallMap
  , TestCase $ assertVerified "object maps with an invariant" nop symcallMapParam
  , TestCase $ assertVerified "object maps with invariant using field access" nop mapInvariantField
  , TestCase $ assertVerified "commute two new(){} expressions used in result" nop commuteNews
  , TestCase $ assertVerified "commute two new(){} expressions with an extra new on one side" nop commuteNewPathCondition
  , TestCase $ assertVerified "reason about new()s used only in path condition" nop commuteNewContradictoryPath
  , TestCase $ assertVerified "syntactic sugar rnd() also commutes" nop commuteRands
  , TestCase $ assertVerified "basic set literals and membership" nop setInTest
  , TestCase $ assertVerified "set membership in singleton set" nop setInTest2
  , TestCase $ assertVerified "trivial set comprehension" nop setComprTest1
  , TestCase $ assertVerified "constant map comprehension" nop mapComprTest1
  , TestCase $ assertVerified "map comprehension with another map in predicate" nop mapComprTest2
  , TestCase $ assertVerified "map comprehension using another map in predicate and mapping function" nop mapComprTest3
  , TestCase $ assertVerified "map comprehension to modify existing map" nop mapComprTest4
  , TestCase $ assertVerified "⊆ operation on concrete values" nop constSubmap
  , TestCase $ assertVerified "⊆ operation on symbolic maps and indices" nop paramSubmap
  , TestCase $ assertVerified "local method" nop localMethodExample
  , TestCase $ assertVerified "Pattern-matching behaves like tuple projection" nop patMatch1
  , TestCase $ assertVerified "Pattern-matching remembers tuple size" nop patMatch2
  ]
  where invalidCases = map (TestCase . uncurry (`doesntVerify` nop))
          [ ("trivial contradiction", incorrectVerify1)
          , ("incorrect arithmetic", incorrectVerify2)
          , ("variable capture in method inlining", incorrectMethodInlineCapture)
          ]

main :: IO ()
main = runTestTT tests >> return ()
