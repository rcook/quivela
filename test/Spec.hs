-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE NamedFieldPuns, ScopedTypeVariables, TemplateHaskell #-}

import qualified Control.DeepSeq as DS
import Control.Exception (SomeException, catch)
import qualified Data.Map as M
import qualified Test.HUnit as T
import Test.HUnit (Assertion, Counts(..), Test(TestCase, TestList), (~:))

import qualified Quivela.Examples as E
import qualified Quivela.Language as L
import Quivela.Language
  ( Context(..)
  , Expr(..)
  , Proof(..)
  , SymValue(..)
  , Type(..)
  , Value(..)
  , nop
  )
import qualified Quivela.Parse as P
import qualified Quivela.QuasiQuote as Q
import qualified Quivela.SymEval as S
import qualified Quivela.Util as U
import qualified Quivela.Verify as V

-- Don't print garbage during tests.  If a test fails, debug it separately.
noDebugEnv = S.emptyVerifyEnv {S._debugFlag = False}

assertVerified :: String -> Expr -> Proof -> Test
assertVerified msg prefix proof =
  let t = do
        res <- Q.prove' noDebugEnv prefix proof
        T.assertEqual msg 0 res
   in msg ~: TestCase t

assertError :: String -> IO a -> Test
assertError msg x =
  let t = do
        errored <- fmap DS.force $ catch (x >> pure False) (\(_ :: SomeException) -> return True)
        if not errored
          then T.assertFailure $ "Should have failed: " ++ msg
          else T.assertBool "true" True
   in msg ~: TestCase t

assertEvalError :: String -> Expr -> Test
assertEvalError msg e =
  assertError msg . V.runVerify noDebugEnv $ S.symEval (e, L.emptyCtx, [])

assertEvalResult' :: String -> Context -> Expr -> Value -> Test
assertEvalResult' msg ctx e v =
  let a = do
           (res, _, _) <- S.singleResult <$> (V.runVerify noDebugEnv $ (S.symEval (e, ctx, [])))
           T.assertEqual msg res v
   in msg ~: TestCase a

assertEvalResult :: String -> Expr -> Value -> Test
assertEvalResult msg e v = assertEvalResult' msg L.emptyCtx e v

assertVerifyError :: String -> Expr -> Proof -> Test
assertVerifyError msg prefix proof =
  assertError msg $ Q.prove' noDebugEnv prefix proof

assertParses :: String -> String -> Expr -> Test
assertParses msg progText e =
  msg ~: TestCase (T.assertEqual msg (P.parseExpr progText) e)

doesntVerify :: String -> Expr -> Proof -> Test
doesntVerify msg prefix proof =
  let a = do
        remaining <- Q.prove' noDebugEnv prefix proof
        T.assertBool msg (remaining > 0)
   in msg ~: TestCase a

parserTests =
  map (U.uncurry3 assertParses) $
  [ ("integer constants", "23", EConst (VInt 23))
  , ("empty map literal", "map", EConst (VMap M.empty))
  , ( "unqualified function call"
    , "f(1)"
    , ECall
        {_callObj = EConst VNil, _callName = "f", _callArgs = [EConst (VInt 1)]})
  , ( "tuple with comparisons"
    , "<a, (b > c)>"
    , ETuple
        [ EVar "a"
        , ECall
            { _callObj = EConst VNil
            , _callName = ">"
            , _callArgs = [EVar "b", EVar "c"]
            }
        ])
  , ( "& is right-assoc"
    , "a & b & c"
    , ECall
        { _callObj = EConst VNil
        , _callName = "&"
        , _callArgs =
            [ EVar "a"
            , ECall
                { _callObj = EConst VNil
                , _callName = "&"
                , _callArgs = [EVar "b", EVar "c"]
                }
            ]
        })
  , ( "& and ,"
    , "a & b , c & d"
    , ECall
        { _callObj = EConst VNil
        , _callName = "&"
        , _callArgs =
            [ EVar "a"
            , ESeq
                (EVar "b")
                (ECall
                   { _callObj = EConst VNil
                   , _callName = "&"
                   , _callArgs = [EVar "c", EVar "d"]
                   })
            ]
        })
  , ( ", is right-assoc"
    , "a , b , c"
    , ESeq (EVar "a") (ESeq (EVar "b") (EVar "c")))
  , ( "& and , and | mix correctly"
    , "a | b , c & d"
    , ECall
        { _callObj = EConst VNil
        , _callName = "|"
        , _callArgs =
            [ EVar "a"
            , ESeq
                (EVar "b")
                (ECall
                   { _callObj = EConst VNil
                   , _callName = "&"
                   , _callArgs = [EVar "c", EVar "d"]
                   })
            ]
        })
  , ( "associativity of ! and |"
    , "!a | b"
    , ECall
        { _callObj = EConst VNil
        , _callName = "|"
        , _callArgs =
            [ ECall
                { _callObj = EConst VNil
                , _callName = "!"
                , _callArgs = [EVar "a"]
                }
            , EVar "b"
            ]
        })
  , ( "projections, indexing, and method calls in one expression"
    , "x[1].field.mtd(1, 2)"
    , ECall
        { _callObj = EProj (EIdx (EVar "x") (EConst (VInt 1))) "field"
        , _callName = "mtd"
        , _callArgs = [EConst (VInt 1), EConst (VInt 2)]
        })
  , ( "call on new in parentheses"
    , "(new () { method f(x: int) { x = <1, 2> } }).f(7)"
    , ECall
        { _callObj =
            ENew
              { _newFields = []
              , _newBody =
                  ESeq
                    (EMethod
                       { _emethodName = "f"
                       , _emethodArgs = [("x", TInt)]
                       , _emethodBody =
                           EAssign
                             { _lhs = EVar "x"
                             , _rhs = ETuple [EConst (VInt 1), EConst (VInt 2)]
                             }
                       , _emethodKind = L.NormalMethod
                       })
                    ENop
              }
        , _callName = "f"
        , _callArgs = [EConst (VInt 7)]
        })
  , ( "if expression with braces"
    , "if (1) { 3 } else { a + b }"
    , EIf
        (EConst (VInt 1))
        (EConst (VInt 3))
        (ECall
           { _callObj = EConst VNil
           , _callName = "+"
           , _callArgs = [EVar "a", EVar "b"]
           }))
  , ( "if without braces"
    , "if (x < y) a + b else 1+2"
    , EIf
        (ECall
           { _callObj = EConst VNil
           , _callName = "<"
           , _callArgs = [EVar "x", EVar "y"]
           })
        (ECall
           { _callObj = EConst VNil
           , _callName = "+"
           , _callArgs = [EVar "a", EVar "b"]
           })
        (ECall
           { _callObj = EConst VNil
           , _callName = "+"
           , _callArgs = [EConst (VInt 1), EConst (VInt 2)]
           }))
  ]

invalidCases =
  map
    (uncurry (`doesntVerify` nop))
    [ ("trivial contradiction", E.incorrectVerify1)
    , ("incorrect arithmetic", E.incorrectVerify2)
    , ("variable capture in method inlining", E.incorrectMethodInlineCapture)
    ]

tests :: Test
tests =
  TestList $
  parserTests ++
  invalidCases ++
  [ assertEvalError "assigning to constant variable" E.assignConst
  , assertEvalError "assigning to constant variable" E.assignConst'
  , assertEvalError
      "assigning to constant field in typedecl'd object"
      E.assignConstTypeDecl
  , assertEvalError "ill-typed assignment to object field" E.illTypedAssign
  , assertEvalError "ill-typed assignment to object field" E.illTypedAssign'
  , assertEvalError
      "ill-typed assignment to method parameter"
      E.illTypedParamAssign
  , assertEvalError
      "ill-typed assignment using object type"
      E.illTypedConstrAssign
  , assertEvalError "ill-typed object creation" E.illTypedObjectCreation
  , assertEvalError
      "ill-typed object creation using constructor"
      E.illTypedObjectCreationNamed
  , assertEvalResult
      "multiple indexing expressions in sequence"
      E.doubleIdx
      (VInt 5)
  , assertEvalResult "nested object field lookups" E.doubleFieldDeref (VInt 5)
  , assertEvalResult
      "post-increment on object field"
      E.incrementFieldDeref
      (VTuple [VInt 1, VInt 2])
  , assertEvalResult "type declarations with parameters" E.typedeclTest (VInt 5)
  , assertEvalResult
      "Addresses can be used as symbolic values"
      E.addressesSymbolic
      (Sym (Add (Sym (Ref 1)) (Sym (Ref 2))))
  , assertEvalResult'
      "Decreasing allocation strategy should yield negative addresses"
      (L.emptyCtx {_ctxAllocStrategy = L.Decrease})
      (P.parseExpr "<new() {}, new() {}>")
      (VTuple [Sym {_symVal = Ref (-1)}, Sym {_symVal = Ref (-2)}])
  , assertEvalResult'
      "Decreasing allocation allows allocating objects in methods"
      L.emptyCtxRHS
      E.decreaseAlloc
      (VInt 1)
  , assertVerifyError
      "verification should detect extraneous methods on one side"
      nop
      E.extraMethodsTest
  , doesntVerify
      "if expression equivalence differing on one branch"
      nop
      E.ifEqvFalse
  , assertVerified "<= works" nop E.leTaut
  , assertVerified "& well-behaved" nop E.andExample
  , assertVerified "simple equality invariant" nop E.eqInvExample
  , assertVerified "simple const annotation" nop E.constExample
  , assertVerified "addition is commutative and 0 is identity" nop E.addExample
  , assertVerified "multiplication example" nop E.mulExample
  , assertVerified "arithmetic example" nop E.arithExample
  , assertVerified "assignment to local variable" nop E.assignAnd
  , assertVerified "tupling never returns 0" nop E.tuplingAnd
  , assertVerified "if-else with symbolic condition" nop E.ifSymbolic
  , assertVerified "if-else with same value in both branches" nop E.ifSimp
  , assertVerified "if-else with true guard" nop E.ifConcreteTrue
  , assertVerified "if-else with false guard" nop E.ifConcreteFalse
  , assertVerified "post-increment example 1" nop E.postIncrExample3
  , assertVerified "post-increment example 2" nop E.postIncrExample2
  , assertVerified "post-increment example 3" nop E.postIncrExample1
  , assertVerified "post-increment in a map index" nop E.postIncrementInMap
  , assertVerified "less-than operator example" nop E.leExample
  , assertVerified "Z(..) is idempotent" nop E.zIdempotent
  , assertVerified "call on symbolic object" nop E.symcallTest
  , assertVerified "call on symbolic map value" nop E.symcallMap
  , assertVerified "object maps with an invariant" nop E.symcallMapParam
  , assertVerified
      "object maps with invariant using field access"
      nop
      E.mapInvariantField
  , assertVerified
      "commute two new(){} expressions used in result"
      nop
      E.commuteNews
  , assertVerified
      "commute two new(){} expressions with an extra new on one side"
      nop
      E.commuteNewPathCondition
  , assertVerified
      "reason about new()s used only in path condition"
      nop
      E.commuteNewContradictoryPath
  , assertVerified "syntactic sugar rnd() also commutes" nop E.commuteRands
  , assertVerified "basic set literals and membership" nop E.setInTest
  , assertVerified "set membership in singleton set" nop E.setInTest2
  , assertVerified "trivial set comprehension" nop E.setComprTest1
  , assertVerified "constant map comprehension" nop E.mapComprTest1
  , assertVerified
      "map comprehension with another map in predicate"
      nop
      E.mapComprTest2
  , assertVerified
      "map comprehension using another map in predicate and mapping function"
      nop
      E.mapComprTest3
  , assertVerified
      "map comprehension to modify existing map"
      nop
      E.mapComprTest4
  , assertVerified "⊆ operation on concrete values" nop E.constSubmap
  , assertVerified "⊆ operation on symbolic maps and indices" nop E.paramSubmap
  , assertVerified "local method" nop E.localMethodExample
  , assertVerified
      "Pattern-matching behaves like tuple projection"
      nop
      E.patMatch1
  , assertVerified "Pattern-matching remembers tuple size" nop E.patMatch2
  , assertVerified "Nested symbolic objects" nop E.nestedObjs
  , assertVerified "Nested symbolic objects in maps" nop E.nestedObjMap
  , uncurry
      (assertVerified "calling uninterpreted function with same arguments")
      E.fundeclTest1
  , uncurry
      (doesntVerify "uninterpreted function called with different arguments")
      E.fundeclTest2
  , assertVerified
      "Type declaration with constant initializer"
      nop
      E.typedeclConstField
  , uncurry
      (assertVerified "Placing object and its parameter in different maps")
      E.objectInTwoMaps
  , uncurry
      (assertVerified "Placing object and its parameter in different maps (2)")
      E.objectInTwoMaps'
  , assertVerified "Dropping a call to rnd()" nop E.dropRandom
  ]

main :: IO ()
main = do
  counts@Counts {cases, tried, errors, failures} <- T.runTestTT tests
  if failures > 0 || errors > 0
    then error $ "Failed tests: " ++ show counts
    else if tried /= cases
           then error $ "Not all tests ran: " ++ show counts
           else return ()
